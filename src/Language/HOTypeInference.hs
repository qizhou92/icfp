{-# LANGUAGE QuasiQuotes #-}
module Language.HOTypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Attributes

import           Language.Types
import           Language.HORT

import           Grammar
import qualified Formula as F

data InferenceError
  = UnificationError Type Type
  | UnboundError Var
  | InvalidSplit HORT
  deriving (Show, Read, Eq)

type Infer a = StateT Int (ExceptT InferenceError (Writer [Rule])) a

-- | Given an expression that is annotated with basic types and a context for
-- variable basic types, generate the constraints which relate the higher
-- order refinement types of the subexpressions.
--
-- Type judgements for expressions occur in two parts.
-- First, we generate the appropriate context for each subexpression.
-- This is done with a top down traversal of the expression. Fix expressions
-- and lambda expressions (over non-primitive arguments) add new variables to
-- the context.
--
-- Second, we perform type inference over the subexpressions, recording new
-- constrained Horn clause rules to the Writer Monad context as we go.
typeConstraints :: Attr CoreExpr' (Map Var Type, Type) -> Either InferenceError Grammar
typeConstraints e =
  let e' = infer =<< contextualize <$> giveType (addFreeVars e)
      ac = runExceptT (evalStateT e' 0)
  in case runWriter ac of
    (Left err, _) -> Left err
    (Right _, rs) -> Right (Grammar 0 rs)
  where
    -- | Mark each subexpression with the free variables which appear there.
    addFreeVars = annZipWith (\(m, t) vs -> (m, S.toList vs, t)) . freeVars
    -- | Generate a new higher order relational type for every subexpression.
    giveType = fmap unAttrib . traverse (\(m, vs, t) -> freshType m vs t) . Attrib

type Ctxt = Map Var (HORT, Maybe (Set Var))

-- | Annotate each subexpression with the context which maps variables
-- to their corresponding context.
contextualize :: Attr CoreExpr' HORT -> Attr CoreExpr' (HORT, Ctxt)
contextualize = annZip . inherit (\(Fix (Ann t e)) ctxt -> case e of
  -- We insert x into the context, regardless of its type for fix expressions.
  EFix x e' -> M.insert x (t, Just (boundVars e')) ctxt
  -- For lambda expressions, we only add x to the context if it is not primitive.
  -- Otherwise, we can constrain x directly.
  ELam x _ ->
    let (s, _) = split t
    in if isPrim s
    then ctxt
    else M.insert x (s, Nothing) ctxt
  _ -> ctxt) M.empty

-- | Given an expression where every subexpression has a higher order relational
-- type and has access to the correct context, generate constraints which
-- encode the typing relationships in the expression and propogate the
-- type to the parent expression.
infer :: Attr CoreExpr' (HORT, Ctxt) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (t, ctxt) e) -> case e of
    EVar x ->
      case M.lookup x ctxt of
        -- When x is not in the context (and hence is a primitive lambda bound variable),
        -- we just match x to the output of the expression.
        Nothing ->
          let tv = valueOf t
              vx = F.Var (getVar x) (F.exprType tv)
          in constrain [F.expr|$tv = @vx|] [] t >> pure t
        -- When x is in the context, we say that its type in the context is a subtype
        -- of the type of the current expression.
        Just (t', Nothing) -> t' <: t >> pure t
        Just (t', Just vs) ->
          pure (convertToFix vs t' t)

    EApp st s ->
      if isPrim s
      then
        -- When the argument to the application is primitive, we can constrain
        -- the output of the argument to the argument of the applicand directly.
        let sv = valueOf s
            sta = argumentOf st
        in subtype [F.expr|$sta = $sv|] [s] st t >> pure t
      else do
        -- When the argument is not primitive, all we can do is indicate that
        -- the output type of the applicand should be a subtype of the full
        -- application and that the input of the applicand is a supertype of
        -- the argument.
        let (s', t') = split st
        t' <: t
        s <: s'
        pure t

    ELam x t' ->
      if x `M.notMember` ctxt -- x is HO
      then do
        -- When the lambda argument, x, is primitive, we can directly substitute
        -- the bound argument for the free variable, x, in the body.
        let ta = argumentOf t
        let vx = F.Var (getVar x) (F.exprType ta)
        subtype [F.expr|$ta = @vx|] [] t' t
        pure t
      else do
        -- When the lambda argument is not primitive, all we can do is claim that
        -- the type of the body is a subtype of the output type of the lambda
        -- expression.
        let (_ , t'') = split t
        t' <: t''
        pure t

    EBin op r s ->
      -- For a primitive operation, we can constrain the output of the operation
      -- expression to be equal to performing the actual operation on the outputs
      -- of the subexpressions.
      let rv = valueOf r
          sv = valueOf s
          tv = valueOf t
          f = case op of
            Plus  -> [F.expr|$tv = $rv + $sv|]
            Minus -> [F.expr|$tv = $rv - $sv|]
            Mul   -> [F.expr|$tv = $rv * $sv|]
            Div   -> [F.expr|$tv = $rv / $sv|]
            Eq    -> [F.expr|$tv = ($rv = $sv)|]
            Ne    -> [F.expr|$tv = (not ($rv = $sv))|]
            Lt    -> [F.expr|$tv = ($rv < $sv)|]
            Le    -> [F.expr|$tv = ($rv <= $sv)|]
            And   -> [F.expr|$tv = ($rv && $sv)|]
            Or    -> [F.expr|$tv = ($rv || $sv)|]
            Cons  -> undefined
      in constrain f [r, s] t >> pure t

    EInt i ->
      -- Int literals constrain their output to be equal to the literal.
      let tv = valueOf t
          i' = F.LInt $ toInteger i
      in constrain [F.expr|$tv = $i'|] [] t >> pure t

    EBool b ->
      -- Bool literals constrain their output to be equal to the literal.
      let tv = valueOf t
          b' = F.LBool b
      in constrain [F.expr|$tv = $b'|] [] t >> pure t

    EIf s t' t'' -> do
      -- If expressions generate two sets of constraints.
      let sv = valueOf s
      -- One says that the consequence is a subtype of the full expression,
      -- as witnessed by the output of the condition being true.
      subtype [F.expr|$sv|] [s] t' t
      -- The other says taht the alternative is a subtype of the full
      -- expression, as witnessed by the output of the condition being false.
      subtype [F.expr|not $sv|] [s] t'' t
      pure t

    -- Fix expressions are deceptively simple: We merely state that body of
    -- the fix expression is a subtype of the full expression. Keep in mind
    -- that the variable has already been bound to type `t`, causing a
    -- recursive system of constraints.
    EFix _ t' -> t' <: t >> pure t

    ENil -> undefined
    EMatch{} -> undefined
    ECon{} -> undefined
    ELet{} -> undefined)

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) = subtype (F.LBool True) []


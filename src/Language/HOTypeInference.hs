{-# LANGUAGE QuasiQuotes #-}
module Language.HOTypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
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

type Ctxt = Map Var HORT

type Infer a = StateT Int (ExceptT InferenceError (Writer [Rule])) a

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
    giveType = fmap unAttrib . traverse (\(m, vs, t) -> fresh m vs t) . Attrib


-- | Type judgements for expressions occur in two parts.
-- First, we generate the appropriate context for each subexpression.
-- This is done with a top down traversal of the expression. Fix expressions
-- and lambda expressions (over non-primitive arguments) add new variables to
-- the context.
--
-- Second, we perform type inference over the subexpressions, recording new
-- constrained Horn clause rules to the Writer Monad context as we go.

-- | Annotate each subexpression with the context which maps variables
-- to their corresponding context.
contextualize :: Attr CoreExpr' HORT -> Attr CoreExpr' (HORT, Ctxt)
contextualize = annZip . inherit (\(Fix (Ann t e)) ctxt -> case e of
  EFix x _ -> M.insert x t ctxt
  ELam x _ ->
    case split t of
      Just (s, _) -> if isPrim s then ctxt else M.insert x s ctxt
      Nothing -> error "lambda has non-arrow type"
  _ -> ctxt) M.empty

-- | Given an expression where every subexpression has a higher order relational
-- type and has access to the correct context, generate constraints which
-- encode the typing relationships in the expression and propogate the
-- type to the parent expression.
infer :: Attr CoreExpr' (HORT, Ctxt) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (t, ctxt) e) -> do
    case e of
      EVar x ->
        if isPrim t
        then
          -- When x is primitive, we just match x to the output of the expression.
          let tv = valueOf t
              vx = F.Var (getVar x) (F.exprType tv)
          in constrain [F.expr|$tv = @vx|] [] t
        else do
          -- When x is not primitive, we're forced to look up the type of x from
          -- the context instead.
          t' <- isearch x ctxt
          t' <: t

      EApp st s ->
        if isPrim s
        then
          -- When the argument to the application is primitive, we can constrain
          -- the output of the argument to the argument of the applicand directly.
          let sv = valueOf s
              sta = argumentOf st
          in subtype [F.expr|$sta = $sv|] [s] st t
        else do
          -- When the argument is not primitive, all we can do is indicate that
          -- the output type of the applicand should be a subtype of the full
          -- application and that the input of the applicand is a supertype of
          -- the argument.
          (s', t') <- safeSplit st
          t' <: t
          s <: s'

      ELam x t' ->
        if x `M.member` ctxt -- x is HO
        then do
          (_ , t'') <- safeSplit t
          t' <: t''
        else do
          let ta = argumentOf t
          let vx = F.Var (getVar x) (F.exprType ta)
          subtype [F.expr|$ta = @vx|] [] t' t

      EBin op r s ->
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
        in constrain f [r, s] t

      EInt i ->
        let tv = valueOf t
            i' = F.LInt $ toInteger i
        in constrain [F.expr|$tv = $i'|] [] t

      EBool b ->
        let tv = valueOf t
            b' = F.LBool b
        in constrain [F.expr|$tv = $b'|] [] t

      EIf s t' t'' -> do
        let sv = valueOf s
        subtype [F.expr|$sv|] [s] t' t
        subtype [F.expr|not $sv|] [s] t'' t

      EFix _ t' -> t' <: t

      ENil -> undefined
      EMatch{} -> undefined
      ECon{} -> undefined
      ELet{} -> undefined
    pure t)

-- | Split the function type into the argument and result types or
-- generate an error if the type cannot be split.
safeSplit :: MonadError InferenceError m => HORT -> m (HORT, HORT)
safeSplit t = case split t of
  Nothing -> throwError (InvalidSplit t)
  Just x -> pure x

-- | Find the type of the variable in the context or generate an error
-- if it is not in the context.
isearch :: Var -> Ctxt -> Infer HORT
isearch x ctxt =
  case M.lookup x ctxt of
    Nothing -> throwError (UnboundError x)
    Just t' -> pure t'

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) = subtype (F.LBool True) []


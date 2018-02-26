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
typeConstraints :: Attr CoreExpr' (ExprID, Map Var Type, Type)
                -> Either InferenceError (Clones, Grammar)
typeConstraints e =
  let ac = runExceptT (evalStateT (do
      hasHO <- giveType (addFreeVars e)
      let cs = computeClones hasHO
      let hasHO' = annMap snd hasHO
      wCtxt <- contextualize hasHO'
      -- let wCtxt' = restrictContext (annZip $ freeVars wCtxt)
      _ <- ctxtSubtyping wCtxt
      _ <- infer wCtxt
      pure cs) 0)
  in case runWriter ac of
    (Left err, _) -> Left err
    (Right cs, rs) -> Right (cs, Grammar 0 rs)
  where
    -- | Mark each subexpression with the free variables which appear there.
    addFreeVars = annZipWith (\(iden, m, t) vs -> (iden, m, S.toList vs, t)) . freeVars
    -- | Generate a new higher order relational type for every subexpression.
    giveType = fmap unAttrib . traverse (\(iden, m, vs, t) -> (,) iden <$> freshType m vs t) . Attrib

    restrictContext :: Attr CoreExpr' ((HORT, Ctxt), Set Var) -> Attr CoreExpr' (HORT, Ctxt)
    restrictContext = annMap (\((t, c), vs) -> (t, M.filterWithKey (\k _ -> k `elem` vs) c))

computeClones :: Attr CoreExpr' (ExprID, HORT) -> Clones
computeClones ex = M.elems $ execState (mapM_ (modify . addToMap) (Attrib ex)) M.empty
  where
    addToMap (eid, hort) =
      M.insertWith S.union eid (S.singleton $ nonterminalPrimary $ topPredicate hort)

type Ctxt = Map Var HORT

-- | Annotate each subexpression with the context which maps variables
-- to their corresponding context.
contextualize :: MonadState Int m => Attr CoreExpr' HORT -> m (Attr CoreExpr' (HORT, Ctxt))
contextualize = copyCtxts . annZip . inherit
  (\(Fix (Ann t e)) ctxt -> case e of
    -- We insert x into the context, regardless of its type for fix expressions.
    EFix x _ -> M.insert x t ctxt
    -- For lambda expressions, we only add x to the context if it is not primitive.
    -- Otherwise, we can constrain x directly.
    ELam x _ ->
      let (s, _) = split t
      in M.insert x s ctxt
    _ -> ctxt) M.empty
  where
    copyCtxts (Fix (Ann (t, c) e)) = Fix <$> case e of
      ELam x e' -> pure $ Ann (t, c) (ELam x e')
      e' -> do c' <- copyContext c
               pure $ Ann (t, c') e'


-- | Declare that the types of the variables in the first context are subtypes
-- of their corresponding types in the second context.
constrainCtxt :: Ctxt -> Ctxt -> Infer ()
constrainCtxt c1 c2 =
  if c1 == c2
  then pure ()
  else let c' = M.intersectionWith (,) c1 c2 in
       mapM_ (uncurry (<:)) (M.elems c')

ctxtSubtyping :: Attr CoreExpr' (a, Ctxt) -> Infer (Attr CoreExpr' Ctxt)
ctxtSubtyping = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (_, t) e) -> do
    case e of
      EApp st s -> do
        constrainCtxt t st
        constrainCtxt t s
      ELam _ t' -> pure ()
      EBin _ r s -> do
        constrainCtxt t r
        constrainCtxt t s
      EIf q r s -> do
        constrainCtxt t q
        constrainCtxt t r
        constrainCtxt t s
      EFix _ s -> constrainCtxt t s
      _ -> pure ()
    pure t)

-- | Given an expression where every subexpression has a higher order relational
-- type and has access to the correct context, generate constraints which
-- encode the typing relationships in the expression and propogate the
-- type to the parent expression.
infer :: Attr CoreExpr' (HORT, Ctxt) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (t, ctxt) e) -> case e of
    EVar x ->
      case M.lookup x ctxt of
        Nothing -> error "each variable should corresponding a predicate"
        -- When x is in the context, we say that its type in the context is a subtype
        -- of the type of the current expression.
        Just t' ->
          if isPrim t then do
             let tv = valueOf t
             let tv' = valueOf t'
             let vx = F.Var (getVar x) (F.exprType tv)
             constrain [F.expr|$tv = @vx && $tv' = @vx|] [t'] t
             pure t
          else t' <: t >> pure t

    EApp st s -> do
      -- When expression is app is indicate that
      -- the output type of the applicand should be a subtype of the full
      -- application and that the input of the applicand is a supertype of
      -- the argument.
      let (s', t') = split st
      s <: s'
      t' <: t
      pure t

    ELam x t' ->
      case M.lookup x ctxt of
        Nothing -> error "each variable should corresponding a predicate"
        Just s ->
          if isPrim s
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

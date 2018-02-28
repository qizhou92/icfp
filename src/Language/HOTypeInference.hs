{-# LANGUAGE QuasiQuotes #-}
module Language.HOTypeInference where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader

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

type Infer a = ReaderT Ctxt (StateT Int (ExceptT InferenceError (Writer [Rule]))) a

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
  let ac = runExceptT (evalStateT (runReaderT (do
      hasHO <- giveType (addFreeVars e)
      let cs = computeClones hasHO
      let hasHO' = annMap snd hasHO
      _ <- infer hasHO'
      pure cs) M.empty) 0)
  in case runWriter ac of
    (Left err, _) -> Left err
    (Right cs, rs) -> Right (cs, Grammar 0 rs)
  where
    -- | Mark each subexpression with the free variables which appear there.
    addFreeVars = annZipWith (\(iden, m, t) vs -> (iden, m, S.toList vs, t)) . freeVars
    -- | Generate a new higher order relational type for every subexpression.
    giveType = fmap unAttrib . traverse (\(iden, m, vs, t) -> (,) iden <$> freshType m vs t) . Attrib

computeClones :: Attr CoreExpr' (ExprID, HORT) -> Clones
computeClones ex = M.elems $ execState (mapM_ (modify . addToMap) (Attrib ex)) M.empty
  where
    addToMap (eid, hort) =
      M.insertWith S.union eid (S.singleton $ nonterminalPrimary $ topPredicate hort)

-- | Given an expression where every subexpression has a higher order
-- relational type, generate constraints which encode the typing relationships
-- in the expression and propogate the type to the parent expression.
infer :: Attr CoreExpr' HORT -> Infer HORT
infer (Fix (Ann t e)) = do
  case e of
    EVar x ->
     M.lookup x <$> ask >>= \case
      Nothing ->
        let tv = valueOf t
            vx = F.Var (getVar x) (view F.varType tv)
        in constrain [F.expr|@tv = @vx|] [] t
      -- When x is in the context, we say that its type in the context is a subtype
      -- of the type of the current expression.
      Just t' -> t' <: t

    EApp app arg -> do
      s <- infer arg
      if isPrim s
      then do
        st <- infer app
        let sv = valueOf s
        let sta = argumentOf st
        subtype [F.expr|@sta = @sv|] [s] st t
      else do
        -- When the argument is not primitive, all we can do is indicate that
        -- the output type of the applicand should be a subtype of the full
        -- application and that the input of the applicand is a supertype of
        -- the argument.
        st <- infer app
        let (s', t') = split st
        t' <: t
        s <: s'

    ELam x e' -> do
      let (s, t'') = split t
      let ta = argumentOf t
      let vx = F.Var (getVar x) (view F.varType ta)
      if isPrim s
      then do
        t' <- infer e'
        subtype [F.expr|@ta = @vx|] [] t' t
      else do
        t' <- local (M.insert x s) (infer e')
        t' <: t''

    EFix{} -> pure ()

    EIf cond consequent alternative -> do
      s <- infer cond
      t' <- infer consequent
      t'' <- infer alternative
      -- If expressions generate two sets of constraints.
      let sv = valueOf s
      -- One says that the consequence is a subtype of the full expression,
      -- as witnessed by the output of the condition being true.
      subtype [F.expr|@sv|] [s] t' t
      -- The other says taht the alternative is a subtype of the full
      -- expression, as witnessed by the output of the condition being false.
      subtype [F.expr|not @sv|] [s] t'' t

    EBin bin arg1 arg2 -> do
      -- For a primitive operation, we can constrain the output of the operation
      -- expression to be equal to performing the actual operation on the outputs
      -- of the subexpressions.
      r <- infer arg1
      s <- infer arg2
      let rv = valueOf r
          sv = valueOf s
          tv = valueOf t
          f = case bin of
            Plus  -> [F.expr|@tv = @rv + @sv|]
            Minus -> [F.expr|@tv = @rv - @sv|]
            Mul   -> [F.expr|@tv = @rv * @sv|]
            Div   -> [F.expr|@tv = @rv / @sv|]
            Eq    -> [F.expr|@tv = (@rv = @sv)|]
            Ne    -> [F.expr|@tv = (not (@rv = @sv))|]
            Lt    -> [F.expr|@tv = (@rv < @sv)|]
            Le    -> [F.expr|@tv = (@rv <= @sv)|]
            And   -> [F.expr|@tv = (@rv && @sv)|]
            Or    -> [F.expr|@tv = (@rv || @sv)|]
            Cons  -> undefined
      constrain f [r, s] t

    EInt i ->
      -- Int literals constrain their output to be equal to the literal.
      let tv = valueOf t
          i' = F.LInt $ toInteger i
      in constrain [F.expr|@tv = $i'|] [] t

    EBool b ->
      -- Bool literals constrain their output to be equal to the literal.
      let tv = valueOf t
          b' = F.LBool b
      in constrain [F.expr|@tv = $b'|] [] t

    ENil -> undefined
    EMatch{} -> undefined
    ECon{} -> undefined
    ELet{} -> undefined
  pure t

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) = subtype (F.LBool True) []

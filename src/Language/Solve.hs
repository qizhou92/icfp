module Language.Solve where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader

import qualified Language.TypeInference as TI
import           Language.RHOTypeInference
import           Language.Types

import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Attributes
import qualified Data.Generics.Fixplate.Traversals as T
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Grammar
import           Formula (runVocabT, MonadVocab, fresh)
import qualified Formula as F

type Result = Either F.Model (Map Symbol F.Expr)

solveCE :: F.Expr -> CoreExpr -> CoreExpr -> IO Result
solveCE q ex1 ex2 =
  evalStateT (do
    e1 <- prepare ex1
    e2 <- prepare ex2
    case (,) <$> TI.typeCheck e1 <*> TI.typeCheck e2 of
      Left err -> error (show err)
      Right (e1', e2') -> runVocabT (do
        te1 <- uniqueNames $ applyTypes e1'
        te2 <- uniqueNames $ applyTypes e2'
        loop q te1 te2)) 0
  where
    prepare = fmap (availableVars . annMap fst) . numberExpressions . emptyAttr
    applyTypes = annMap (\(ctxt, t, (vs, fixed)) ->
      let vs' = S.map (\v -> (v, ctxt M.! v)) vs
      in Annotation fixed fixed vs' t)

loop :: ( MonadIO m
        , MonadState ExprID m
        , MonadVocab m) => F.Expr -> IExpr -> IExpr -> m Result
loop q e1 e2 = do
  e1' <- unwindFix e1
  e2' <- unwindFix e2
  (cs, g) <- boundedInference (Seq.fromList [e1', e2'])
  interpolate g q >>= \case
    Left e -> pure (Left e)
    Right m -> do
      ind <- inductive cs g m
      if M.findWithDefault False (g ^. grammarStart) ind
      then pure (Right m)
      else loop q e1' e2'

boundedInference :: MonadIO m => Seq IExpr -> m (Clones, Grammar)
boundedInference es =
  case runInfer (infer es) of
    Left err -> error (show err)
    Right (_, st, rs) ->
      -- TODO the state has enough information to build the clones set, it
      -- just isn't done yet.
      pure (undefined, Grammar 0 rs)

-- | Use alpha renaming to ensure every binding binds a different variable.
uniqueNames :: MonadVocab m => IExpr -> m IExpr
uniqueNames ex = runReaderT (go ex) M.empty
  where
    go (Fix (Ann (Annotation fid uid tvs t) e)) = do
      e' <- case e of
        EFix x e'    -> newName EFix x e'
        ELam x e'    -> newName ELam x e'
        EVar (Var x) -> EVar . Var . M.findWithDefault x x <$> ask
        _            -> traverse go e
      tvs' <- S.fromList <$> mapM (\(Var x, vt) -> do
        x' <- M.findWithDefault x x <$> ask
        pure (Var x', vt)) (S.toList tvs)

      pure (Fix $ Ann (Annotation fid uid tvs' t) e')

    newName f (Var x) e = do
      x' <- lift (fresh x)
      f (Var x') <$> local (M.insert x x') (go e)

unwindFix :: (MonadVocab m, MonadState ExprID m) => IExpr -> m IExpr
unwindFix ex = runReaderT (unw ex) M.empty
  where
    unw (Fix node@(Ann _ e')) = case e' of
      -- In the case of a fix expression, unwind with the fix expression in the
      -- context, removing the Fix.
      EFix x e -> local (M.insert x node) (unw e)
      -- In the case of a lambda expression, remove the matched fix variable
      -- from the context before recursing over the subexpressions.
      ELam x _ -> T.descendM (local (M.delete x) . unw) (Fix node)
      -- In the case of a variable try to replace it by value in the context.
      EVar x -> M.lookup x <$> ask >>= \case
        Nothing -> pure (Fix node)
        Just content -> do
          nums <- numberExpressions =<< uniqueNames (Fix content)
          pure (annMap (\(n, Annotation fid _ tvs t) -> Annotation fid n tvs t) nums)
      -- In all other cases, recurse over the subexpressions.
      _ -> T.descendM unw (Fix node)


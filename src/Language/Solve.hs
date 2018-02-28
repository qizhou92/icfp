module Language.Solve where

import           Control.Lens
import           Control.Monad.State

import qualified Language.TypeInference as TI
import           Language.RHOTypeInference
import           Language.Types

import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Attributes
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

type Result = Either F.Model (Map Symbol F.Expr)

solveCE :: F.Expr -> CoreExpr -> CoreExpr -> IO Result
solveCE q ex1 ex2 =
  let (e1, e2) = evalState (
        (,) <$> numberExpressions (emptyAttr ex1)
            <*> numberExpressions (emptyAttr ex2)) 0
  in loop (annMap fst e1) (annMap fst e2)
  where
    loop :: Attr CoreExpr' ExprID -> Attr CoreExpr' ExprID -> IO Result
    loop e1 e2 = do
      let e1' = runVocab (uniqueNames $ unwindFix e1)
      let e2' = runVocab (uniqueNames $ unwindFix e2)
      (cs, g) <- boundedInference (Seq.fromList [e1', e2'])
      interpolate g q >>= \case
        Left e -> pure (Left e)
        Right m -> do
          ind <- inductive cs g m
          if M.findWithDefault False (g ^. grammarStart) ind
          then pure (Right m)
          else loop e1' e2'

boundedInference :: Seq (Attr CoreExpr' ExprID)
                 -> IO (Clones, Grammar)
boundedInference es =
  case mapM TI.typeCheck es of
    Left err -> error (show err)
    Right es' -> do
      let es'' = fmap availableVars es'
      let uniqueNumEs = evalState (traverse numberExpressions es'') 0
      let prepped = fmap (annMap prepare) uniqueNumEs
      case runInfer (infer prepped) of
        Left err -> error (show err)
        Right (_, st, rs) ->
          -- TODO the state has enough information to build the clones set, it
          -- just isn't done yet.
          pure (undefined, Grammar 0 rs)
  where
    prepare (unique, (vs, (ctxt, t, fixed))) =
      let vs' = S.map (\v -> (v, ctxt M.!v)) vs
      in Annotation fixed unique vs' t

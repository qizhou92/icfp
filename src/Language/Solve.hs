module Language.Solve where

import           Control.Lens
import           Control.Monad.State

import qualified Language.TypeInference as TI
import           Language.HOTypeInference
import           Language.Types
import           Language.Parser

import           Text.Parsec
import           Data.Generics.Fixplate.Draw
import           Data.Generics.Fixplate.Base
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc
import           Data.Generics.Fixplate.Attributes

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

type Result = Either F.Model (Map Symbol F.Expr)

solveCE :: F.Expr -> CoreExpr -> CoreExpr -> IO Result
solveCE q e1' e2' =  do
  let (e1, e2) = evalState (
        (,) <$> numberExpressions e1' <*> numberExpressions e2') 0
  loop e1 e2
  undefined
  where
    loop :: Attr CoreExpr' ExprID -> Attr CoreExpr' ExprID -> IO Result
    loop e1 e2 = do
      let e1' = runVocab (uniqueNames $ unwindFix e1)
      let e2' = runVocab (uniqueNames $ unwindFix e2)
      (cs1, g1) <- exprGrammar e1'
      (cs2, g2) <- exprGrammar e2'
      let pm = undefined :: Map (Symbol, Symbol) Symbol
          -- TODO grammar product should return this map
      let cs = clonesProduct pm cs1 cs2
      let g = Grammar.product g1 g2
      interpolate g q >>= \case
        Left e -> pure (Left e)
        Right m -> do
          ind <- inductive cs g m
          if M.findWithDefault False (g ^. grammarStart) ind
          then pure (Right m)
          else loop e1' e2'

clonesProduct :: Map (Symbol, Symbol) Symbol -> Clones -> Clones -> Clones
clonesProduct = undefined

exprGrammar :: Attr CoreExpr' ExprID -> IO (Clones, Grammar)
exprGrammar e = undefined
  -- case TI.typeCheck e of
  --   Left (TI.UnificationError t1 t2) -> Left (UnificationError t1 t2)
  --   Left (TI.UnboundError x) -> Left (UnboundError x)
  --   Right e' -> typeConstraints e'

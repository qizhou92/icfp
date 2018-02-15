module Language.UniqueNames where

import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Traversals

import           Language.Types
import           Language.TypeInference

uniqueNames :: CoreExpr -> CoreExpr
uniqueNames e = evalState (topDownTransformM go e) M.empty
  where
    go :: CoreExpr -> State (Map Var Int) CoreExpr
    go (Fix e) = case e of
      EVar x -> evar <$> resolve x
      ELam x e -> do
        M.lookup x <$> get >>= \case
          Nothing -> modify (M.insert x 0)
          Just i  -> modify (M.insert x (i+1))
        elam <$> resolve x <*> pure e
      e' -> pure (Fix e')
    resolve x = M.lookup x <$> get >>= \case
      Nothing -> pure x
      Just i -> pure (Var (getVar x ++ "/" ++ show i))

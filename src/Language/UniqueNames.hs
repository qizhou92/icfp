module Language.UniqueNames where

import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Traversals

import           Language.Types
import           Language.TypeInference

import           Formula (MonadVocab, fresh, fetch)

uniqueNames :: MonadVocab m => CoreExpr -> m CoreExpr
uniqueNames = topDownTransformM go
  where
    go (Fix e) = case e of
      EVar (Var x) -> evar . Var <$> fetch x
      ELam (Var x) e -> do
        x' <- fresh x
        pure (elam (Var x') e)
      e' -> pure (Fix e')

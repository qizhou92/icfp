module Language.Equivalence.Check where

import Language.Equivalence.Derivations
import Language.Equivalence.Types
import Control.Monad.State
import qualified Data.Set as Set

verify :: CoreExpr -> CoreExpr -> IO Bool
verify expr1 expr2 = do
  -- let der1 = (Der RASym expr1 expr1 [] 1)
  -- let der2 = (Der RASym expr2 expr2 [] 2)
  -- checkResult 3 der1 der2
  undefined

checkResult :: CoreExpr ->CoreExpr -> IO Bool
checkResult e1 e2 = do
  -- (isEqual,invariants) <- verifyPairs newDer1 newDer2
  undefined

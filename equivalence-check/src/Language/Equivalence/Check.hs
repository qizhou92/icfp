module Language.Equivalence.Check where

import Language.Equivalence.CkInd
import Language.Equivalence.Derivations
import Language.Equivalence.VerifyDerivation
import Language.Equivalence.Types
import Control.Monad.State
import qualified Data.Set as Set

verify :: CoreExpr -> CoreExpr -> IO Bool
verify expr1 expr2 = do
  let der1 = (Der RASym expr1 [] 1)
  let der2 = (Der RASym expr2 [] 2)
  checkResult 3 der1 der2

checkResult :: Int -> Der -> Der -> IO Bool
checkResult idNumber der1 der2 = do
  let (newDer1,state1) = runState (unwindDer der1) (UnwindResult Set.empty idNumber)
  let (newDer2,(UnwindResult _ nextId)) = runState (unwindDer der2) state1
  print "Derivations"
  print newDer1
  print newDer2
  (isEqual,invariants) <- verifyPairs newDer1 newDer2
  print "verify folding tree"
  print isEqual
  if (not isEqual) then return False
    else do
           isInductive <- checkInductive invariants [newDer1,newDer2]
           print "isInductive"
           print isInductive
           if isInductive then return True
              else checkResult nextId newDer1 newDer2
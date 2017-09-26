module Language.Haskell.Test1 where
import Language.Equivalence.Check
import Language.Equivalence.Types
import Language.Equivalence.CkInd
import Language.Equivalence.Derivations
import Language.Equivalence.VerifyDerivation
import Control.Monad.State
import qualified Data.Set as Set

main = do
  let zero = EInt 0
  let one = EInt 1
  let x1 = EVar (Var "x1")
  let f1 = EVar (Var "f1")
  let xLe0 = EBin Le x1 zero
  let xMinus1 = EBin Minus x1 one
  let fApp = EApp f1 xMinus1
  let onePlustFApp = EBin Plus one fApp
  let ifStats = EIf xLe0 x1 onePlustFApp
  let lambada1 = ELam (Var "x1") ifStats
  let fixExpr1 = EFix (Var "f1") lambada1
  let x2 = EVar (Var "x1")
  let f2 = EVar (Var "f2")
  let x2Le0 = EBin Le x2 zero
  let x2Minus1 = EBin Minus x2 zero
  let fApp2 = EApp f2 x2Minus1
  let onePlustFApp2 = EBin Plus one fApp2
  let ifStats2 = EIf x2Le0 x2 onePlustFApp2
  let lambada2 = ELam (Var "x2") ifStats2
  let fixExpr2 = EFix (Var "f2") lambada2
  result <- verify fixExpr1 fixExpr2
  print result
  

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
  let xLe0 = EBin Le x1 zero
  let onePlustFApp = EBin Plus one x1
  let ifStats = EIf xLe0 x1 onePlustFApp
  let lambada1 = ELam (Var "x1") ifStats
  let x2 = EVar (Var "x2")
  let x2Le0 = EBin Le x2 zero
  let onePlustFApp2 = EBin Plus one x2
  let ifStats2 = EIf x2Le0 x2 onePlustFApp2
  let lambada2 = ELam (Var "x2") ifStats2
  result <- verify lambada1 lambada2
  print result
  

module Language.Equivalence.CkInd where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import Language.Equivalence.TypeInference
import qualified Data.Set as Set
import Language.Equivalence.Derivations
import qualified Language.Equivalence.Types as Types
import qualified Data.Map as Map
import Control.Monad.State

type TestState a = State Int a

getNewOne :: Int -> TestState Int
getNewOne value = do
  return (value + 1)

main = do
  let (value,state) = runState (mapM (getNewOne) [1 .. 1000000000000000]) 0
  print (take 5 value)
  print state

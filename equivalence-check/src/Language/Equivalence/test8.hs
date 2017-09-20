module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.Derivations
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.TypeInference
import Language.Equivalence.VerifyDerivation


main = do
  let zero = Types.EInt 0
  let one = Types.EInt 1
  let x = Types.Var "x"
  let y = Types.Var "y"
  let sum1 = Types.EBin Types.Plus (Types.EVar x) one
  let sum2 = Types.EBin Types.Plus (Types.EVar y) one
  let lambada1 = Types.ELam x sum1
  let lambada2 = Types.ELam y sum2
  let (der1,state1) = runState (makeDerivations lambada1) (UnwindResult Set.empty 0)
  let (der2,state2) = runState (makeDerivations lambada2) state1
  verifyPairs der1 der2
  

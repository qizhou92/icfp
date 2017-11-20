module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import Language.Equivalence.Check
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
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let x = Types.Var "x"
  let y = Types.Var "y"
  let sum1 = Types.EBin Types.Plus (Types.EVar x) one
  let sum2 = Types.EBin Types.Plus (Types.EVar y) two
  let lambada1 = Types.ELam x sum1
  let lambada2 = Types.ELam y sum2
  result <- verify lambada1 lambada2
  print result
  

module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.Derivations
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.TypeInference


main = do
  let zero = Types.EInt 0
  let one = Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let x = Types.Var "x"
  let sum1 = Types.EBin Types.Plus (Types.EVar x) four
  let sum2 = Types.EBin Types.Plus two three
  let coreExpr = Types.ELam x sum1
  let r = infereType coreExpr
  case r of
    Left err -> print err
    Right res -> print res
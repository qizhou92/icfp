module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.VerifyDerivation
import Language.Equivalence.Derivations

main = do
  let one=Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let coreExpr1 = Types.EBin Types.Plus one four
  let coreExpr2 = Types.EBin Types.Plus two three
  let dEnv= []
  let d1 = ((makeDerivations dEnv coreExpr2) !! 0)
  let d2 = ((makeDerivations dEnv coreExpr1) !! 0)
  verifyPairs d1 d2
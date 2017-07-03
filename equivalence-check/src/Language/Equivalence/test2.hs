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
  let zero = Types.EInt 0
  let one = Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let x = Types.Var "x"
  let xLeZero=Types.EBin Types.Lt zero (Types.EVar x)
  let sum1 = Types.EBin Types.Plus one four
  let sum2 = Types.EBin Types.Plus two three
  let coreExpr = Types.EIf xLeZero three three
  let coreExpr2 = Types.EIf xLeZero one three
  let dEnv= [(x,Types.ENil)]
  let d1 = ((makeDerivations dEnv coreExpr coreExpr) !! 0)
  let d2 = ((makeDerivations dEnv coreExpr coreExpr) !! 1)
  let (node1,number) = translateDT 0 d1
  let (node2,number2) = translateDT number d2
  verifyPairs d1 d2
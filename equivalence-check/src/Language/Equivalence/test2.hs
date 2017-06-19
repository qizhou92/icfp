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
  let zero=Types.EInt 0
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let x = Types.Var "x"
  let xLeZero=Types.EBin Types.Le (Types.EVar x) zero
  let coreExpr = Types.EIf xLeZero two three
  let dEnv= [(x,Types.ENil)]
  let d1 = ((makeDerivations dEnv coreExpr) !! 0)
  let d2 = ((makeDerivations dEnv coreExpr) !! 1)
  let (node1,theId2) = (translateDT 0 d1)
  let (node2,theID3) = (translateDT theId2 d2)
  let pairSet = PairRelatingSet [node1] [node2]
  let varList1 = collectDerivationNodeVar node1
  let varList2 = collectDerivationNodeVar node2
  let emptyCHC = CHC [] [] (varList1++varList2) MkEmpty
  let result1 = getAllRulesOfCHC (Set.insert pairSet (Set.empty)) Set.empty emptyCHC
  print result1
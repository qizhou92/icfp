module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.VerifyDerivation

main = do
  let one=Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let core1=Types.EBin Types.Plus four three
  let core2=Types.EBin Types.Plus one three
  let core3=Types.EBin Types.Plus one two
  let core4=Types.EBin Types.Plus core2 core3
  let der1=Der RNConst [] one []
  let der2=Der RNConst [] two []
  let der3=Der RNConst [] three []
  let der4=Der RNConst [] four []
  let der5=Der RNOp [] core1 [der4,der3]
  let der6=Der RNOp [] core2 [der1,der3]
  let der7=Der RNOp [] core3 [der1,der2]
  let der8=Der RNOp [] core4 [der6,der7]
  let (node1,theId2) = (translateDT 0 der5)
  let (node2,theID3) = (translateDT theId2 der7)
  let pairSet = PairRelatingSet [node1] [node2]
  let varList1 = collectDerivationNodeVar node1
  let varList2 = collectDerivationNodeVar node2
  let emptyCHC = CHC [] [] (varList1++varList2) MkEmpty
  let result1 = getAllRulesOfCHC (Set.insert pairSet (Set.empty)) Set.empty emptyCHC
  print result1

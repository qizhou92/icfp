module Language.Equivalence.VerifyDerivation where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set

-- Subexprssion is the data type represents the subexprrsion in derivation, first argument
-- string represents the name of the subexprssion, second argument list of string represents the list of variable name
-- Int represents the count of SubExprssion

data SubExprssion = SubExprssion String [Var] Int


data HyperEdge = HyperEdge Expr [DerivationNode]

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode SubExprssion HyperEdge

-- repalce the int data type by subexpression to get all merge/split subexpression possible set

--


data PairRelatingSet =PairRelatingSet [DerivationNode] [DerivationNode] Function

getAllRulesOfCHC :: (Set.Set PairRelatingSet) -> CHC -> CHC
getAllRulesOfCHC pairRelatingSet theCHC
 |null pairRelatingSet = theCHC
 |otherwise = do
               let singlePairRelatingSet = (Set.elemAt 0 pairRelatingSet)
               let newPairRelatingSet = (Set.deleteAt 0 pairRelatingSet)
               let (newCHC1,newPredicates1) = getStepRules singlePairRelatingSet theCHC
               let (newCHC2,newPredicates2) = getSplitRules singlePairRelatingSet newCHC1
               let newPairSet1 = getNewPairRelatingSet newPairRelatingSet newPredicates1
               let newPairSet2 = getNewPairRelatingSet newPairSet1 newPredicates2
               getAllRulesOfCHC newPairSet2 newCHC2

getNewPairRelatingSet :: (Set.Set PairRelatingSet)->[PairRelatingSet]->(Set.Set PairRelatingSet)
getNewPairRelatingSet = undefined

getStepRules :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
getStepRules = undefined

getSplitRules :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
getSplitRules = undefined

getSuccessors :: DerivationNode -> [DerivationNode]
getSuccessors (DerivationNode _ (HyperEdge _ successors)) = successors

getAllPossibleList:: [Int] -> [ [ [Int] ]]
getAllPossibleList list = case list of
  x:xs -> (insertElementIntoAllList x (getAllPossibleList xs))
  _ -> []

insertElementIntoAllList :: Int -> [ [ [ Int ]]] -> [ [ [Int] ] ]

insertElementIntoAllList element list = case list of
  [] -> [[[element]]]
  _->(insertElementIntoAllList1 element list) ++ (insertElementIntoAllList2 element list)

insertElementIntoAllList1 :: Int -> [ [ [ Int ]]] -> [ [ [Int] ] ]
insertElementIntoAllList1 element list = case list of
  x:xs -> if null x
          then [[element]]:(insertElementIntoAllList1 element xs)
          else ([element]:x):(insertElementIntoAllList1 element xs)
  _ -> []

insertElementIntoAllList2 :: Int -> [ [ [Int] ]]  -> [ [ [Int] ] ]
insertElementIntoAllList2 element list = case list of
	x:xs -> (insertAllIndex element (length(x)) x) ++ (insertElementIntoAllList2 element xs)
	_ -> []

insertAllIndex :: Int -> Int -> [ [Int] ] -> [ [ [Int] ] ]
insertAllIndex element len oldList
  | 0<len = (insertByIndex (len - 1) element oldList) : (insertAllIndex element (len -1) oldList)
  | otherwise = []

insertByIndex :: Int -> Int -> [ [Int] ] -> [ [ Int ] ]
insertByIndex index element (x:xs)
  |0<index = x:(insertByIndex (index -1) element xs)
  |otherwise =  (element:x):xs

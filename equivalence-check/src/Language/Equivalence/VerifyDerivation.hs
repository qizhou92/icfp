module Language.Equivalence.VerifyDerivation where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set

-- Subexprssion is the data type represents the subexprrsion in derivation, first argument
-- string represents the name of the subexprssion, second argument list of string represents the list of variable name
-- Int represents the count of SubExprssion

data SubExprssion = SubExprssion String [Var] Int
 deriving(Show,Eq,Ord)

data HyperEdge = HyperEdge Expr [DerivationNode]
 deriving(Show,Eq,Ord)

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode SubExprssion HyperEdge
 deriving(Show,Eq,Ord)

-- repalce the int data type by subexpression to get all merge/split subexpression possible set

-- 
data Derivation = DT [Var] [Expr] String Expr
--


data PairRelatingSet =PairRelatingSet [DerivationNode] [DerivationNode] Function
 deriving(Show,Eq,Ord)

getAllRulesOfCHC :: (Set.Set PairRelatingSet) -> CHC -> CHC
getAllRulesOfCHC pairRelatingSet theCHC
 |null pairRelatingSet = theCHC
 |otherwise = do
               let singlePairRelatingSet = (Set.elemAt 0 pairRelatingSet)
               let newPairRelatingSet = (Set.deleteAt 0 pairRelatingSet)
               let (newCHC,newPredicates) = updateCHC  singlePairRelatingSet theCHC
               let newPairSet = getNewPairRelatingSet newPairRelatingSet newPredicates
               getAllRulesOfCHC newPairSet newCHC

getNewPairRelatingSet :: (Set.Set PairRelatingSet)->[PairRelatingSet]->(Set.Set PairRelatingSet)
getNewPairRelatingSet sets list = case list of
 x:xs ->(Set.insert x (getNewPairRelatingSet sets xs))
 _ -> sets

updateCHC :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
updateCHC = undefined

getStepRules :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
getStepRules (PairRelatingSet leftList rightList _) theCHC = undefined

getStepRulesOneSide :: [DerivationNode] -> [DerivationNode] -> CHC -> (CHC,[PairRelatingSet])
getStepRulesOneSide beUnwind secondProgram currentCHC = 

getAllStepRules :: Bool->Int -> [DerivationNode] -> [DerivationNode] -> CHC -> (CHC,[PairRelatingSet])
getAllStepRules isLeft index list otherList oldCHC = do
  let (x1,x2) = splitAt index list
  let theDerivaion = head x2
  let newX2 = drop 1 x2
  let (theExpr,successors) = getSingleStepRules newX2
  let newDerivationNodeList = x1 ++ (successors ++ newX2)

 

getSingleStepRules :: DerivationNode -> (Expr,[DerivationNode])
getSingleStepRules (DerivationNode _ (HyperEdge theExpr successors))=(theExpr,successors) 

getSplitRules :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
getSplitRules = undefined


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

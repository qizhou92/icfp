module Language.Equivalence.VerifyDerivation where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import System.Process
-- Subexprssion is the data type represents the subexprrsion in derivation, first argument
-- string represents the name of the subexprssion, second argument list of string represents the list of variable name
-- Int represents the count of SubExprssion


data HyperEdge = HyperEdge Expr [DerivationNode]
 deriving(Show,Eq,Ord)

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode [Var] HyperEdge Int Types.CoreExpr
 deriving(Show,Eq,Ord)

-- need translate the coreExpr

translateDT ::  Int -> Der -> (DerivationNode,Int)
translateDT uniqueId (Der ruleName env coreExpr successors) = case ruleName of
  RNConst -> translateRNConst uniqueId (Der ruleName env coreExpr successors)
  RNVar -> undefined
  RNOp -> translateRNOp uniqueId (Der ruleName env coreExpr successors)
  RNIteTrue -> translateRNIteTrue uniqueId (Der ruleName env coreExpr successors)
  RNIteFalse -> translateRNIteFalse uniqueId (Der ruleName env coreExpr successors)
  RNAbs -> undefined
  RNFix -> undefined
  RNAppLam -> translateRNAppLam uniqueId (Der ruleName env coreExpr successors)  
  RNAppFix -> undefined


translateRNConst :: Int -> Der -> (DerivationNode,Int)
translateRNConst uniqueId (Der ruleName evn coreExpr successors) = case coreExpr of
 Types.EInt value -> do
                let smtVar = Var ("output#"++show(uniqueId)) IntegerSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantInt value))
                let newHyperEdge = HyperEdge smtExpr []
                ((DerivationNode [smtVar] newHyperEdge uniqueId coreExpr),uniqueId+1)
 Types.EBool value -> do
                let smtVar = Var ("output#"++show(uniqueId)) BoolSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantBool value))
                let newHyperEdge = HyperEdge smtExpr []
                ((DerivationNode [smtVar] newHyperEdge uniqueId coreExpr),uniqueId+1)

translateRNOp :: Int -> Der -> (DerivationNode,Int)
translateRNOp uniqueId (Der ruleName env coreExpr list) = do
  let firstDer = list !! 0
  let secondDer = list !! 1
  let (firstDerivationNode,nextId) = translateDT uniqueId firstDer
  let (secondDerivationNode,nextId2) = translateDT nextId secondDer
  let smtExpr = getBinaryExpr firstDerivationNode secondDerivationNode coreExpr
  let  var =  Var ("output#"++show(nextId2)) (translateSort (Der ruleName env coreExpr list))
  let smtExpr2 = MkEq smtExpr (ExprVar var)
  let newHyperEdge = HyperEdge smtExpr2 []
  let newVarlist = (translateVarList uniqueId (Der ruleName env coreExpr list)) ++ [var]
  ((DerivationNode newVarlist newHyperEdge nextId2 coreExpr),nextId2+1)

translateSort :: Der -> Sort
translateSort = undefined

translateVarList :: Int -> Der -> [Var]
translateVarList = undefined

getBinaryExpr :: DerivationNode -> DerivationNode -> Types.CoreExpr -> Expr
getBinaryExpr (DerivationNode varList1 _ _ _) (DerivationNode varList2 _ _ _) (Types.EBin binOp _ _) = case binOp of
  Types.Plus -> MkAdd [(ExprVar (last varList1)), (ExprVar (last varList1))]
  Types.Minus -> MkSub [(ExprVar (last varList1)), (ExprVar (last varList1))]
  Types.Mul -> MkMul [(ExprVar (last varList1)), (ExprVar (last varList1))]
  Types.Div -> MkDiv_1 (ExprVar (last varList1)) (ExprVar (last varList1))
  Types.Eq -> MkEq (ExprVar (last varList1)) (ExprVar (last varList1))
  Types.Ne -> MkNot (MkEq (ExprVar (last varList1)) (ExprVar (last varList1)))
  Types.Lt -> MkLt (ExprVar (last varList1)) (ExprVar (last varList1))
  Types.Le -> MkLe (ExprVar (last varList1)) (ExprVar (last varList1))
  Types.And -> MkAnd [(ExprVar (last varList1)), (ExprVar (last varList1))]
  Types.Or -> MkOr [(ExprVar (last varList1)), (ExprVar (last varList1))]
  _ -> MkEmpty

translateRNIteTrue :: Int -> Der -> (DerivationNode,Int)
translateRNIteTrue uniqueId (Der ruleName env coreExpr list) = do
  let firstDer = list !! 0
  let secondDer = list !! 1
  let ((DerivationNode varlist1 _ _ _),nextId) = translateDT uniqueId firstDer
  let ((DerivationNode varlist2 _ _ _),nextId2) = translateDT nextId secondDer
  let var =  Var ("output#"++show(nextId2)) (translateSort (Der ruleName env coreExpr list))
  let smtExpr = MkAnd [(ExprVar (last varlist1)), (MkEq (ExprVar (last varlist2)) (ExprVar var))]
  let newHyperEdge = HyperEdge smtExpr []
  let newVarlist = (translateVarList uniqueId (Der ruleName env coreExpr list)) ++ [var]
  ((DerivationNode newVarlist newHyperEdge nextId2 coreExpr),nextId2+1)

translateRNIteFalse :: Int -> Der -> (DerivationNode,Int)
translateRNIteFalse uniqueId (Der ruleName env coreExpr list) = do
  let firstDer = list !! 0
  let secondDer = list !! 1
  let ((DerivationNode varlist1 _ _ _),nextId) = translateDT uniqueId firstDer
  let ((DerivationNode varlist2 _ _ _),nextId2) = translateDT nextId secondDer
  let  var =  Var ("output#"++show(nextId2)) (translateSort (Der ruleName env coreExpr list))
  let smtExpr = MkAnd [ (MkNot (ExprVar (last varlist1))), (MkEq (ExprVar (last varlist2)) (ExprVar var))]
  let newHyperEdge = HyperEdge smtExpr []
  let newVarlist = (translateVarList uniqueId (Der ruleName env coreExpr list)) ++ [var]
  ((DerivationNode newVarlist newHyperEdge nextId2 coreExpr),nextId2+1)

translateRNAppLam :: Int -> Der -> (DerivationNode,Int)
translateRNAppLam = undefined

translateRNAppFix :: Int -> Der -> (DerivationNode,Int)
translateRNAppFix = undefined

verifyPairs :: Der -> Der -> IO Bool
verifyPairs tree1 tree2 = do
  let (node1,number) = translateDT 0 tree1
  let (node2,number2) = translateDT (number+1) tree2
  let pairSet = PairRelatingSet [node1] [node2]
  let startSet =Set.insert  pairSet (Set.empty)
  let emptyCHC = CHC [] [] [] MkEmpty
  let theCHC = getAllRulesOfCHC startSet emptyCHC
  (result,theMap) <- chc_execute theCHC
  return result
getSortList :: [Var] -> [Sort]
getSortList list = case list of
  (Var _ sort):xs -> sort : getSortList xs
  _ -> []
getDerivatonNodeSortList :: DerivationNode -> [Sort]
getDerivatonNodeSortList (DerivationNode varList _ _ _)=getSortList varList

getStringName :: DerivationNode -> String -> String
getStringName (DerivationNode list _ uniqueId _) oldName = 
  (show uniqueId) ++ "#" ++ oldName

getFunction:: PairRelatingSet -> Function
getFunction (PairRelatingSet list1 list2) = do
  let sortList = (concat (map getDerivatonNodeSortList list1)) ++ (concat (map getDerivatonNodeSortList list2))
  let uniqueName = (foldr getStringName "" list1) ++ (foldr getStringName "" list2)
  Function uniqueName sortList

getArgList :: [Var] -> [Parameter]
getArgList list = case list of
  x:xs -> (ParameterVar x) : getArgList xs
  _ -> []

getDerivatonNodeArgList :: DerivationNode -> [Parameter]
getDerivatonNodeArgList (DerivationNode varList _ _ _)= getArgList varList

getFunctionExpr :: PairRelatingSet -> Expr
getFunctionExpr (PairRelatingSet list1 list2) = do 
  let function = getFunction  (PairRelatingSet list1 list2)
  let args = (concat (map getDerivatonNodeArgList list1)) ++ (concat (map getDerivatonNodeArgList list2))
  ApplyFunction function args

data PairRelatingSet = PairRelatingSet [DerivationNode] [DerivationNode]
 deriving(Show,Eq,Ord)

getAllRulesOfCHC :: (Set.Set PairRelatingSet) -> CHC -> CHC
getAllRulesOfCHC pairRelatingSet theCHC
 |null pairRelatingSet = theCHC
 |otherwise = do
               let singlePairRelatingSet = (Set.elemAt 0 pairRelatingSet)
               let newPairRelatingSet = (Set.deleteAt 0 pairRelatingSet)
               let chcWithRegister = register_predicate (getFunction singlePairRelatingSet) theCHC
               let (newCHC,newPredicates) = updateCHC  singlePairRelatingSet chcWithRegister
               let newPairSet = getNewPairRelatingSet newPairRelatingSet newPredicates
               getAllRulesOfCHC newPairSet newCHC

getNewPairRelatingSet :: (Set.Set PairRelatingSet)->[PairRelatingSet]->(Set.Set PairRelatingSet)
getNewPairRelatingSet sets list = case list of
 x:xs ->(Set.insert x (getNewPairRelatingSet sets xs))
 _ -> sets

updateCHC :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
updateCHC oldPredicate oldCHC = do
  let stepRuleList = getAllStepRules oldPredicate
  let splitRuleList = getSplitRules oldPredicate
  let newCHC1 = foldr updateStepRule oldCHC stepRuleList
  let newCHC2 = foldr updateSplitRule newCHC1 splitRuleList
  let newPrediactList = (map getStepPredicates stepRuleList) ++ (concat (map getSplitPredicates splitRuleList))
  (newCHC2,newPrediactList)


getStepPredicates :: (Rule,PairRelatingSet) -> PairRelatingSet
getStepPredicates (_,newPredicate) = newPredicate

updateStepRule :: (Rule,PairRelatingSet) -> CHC -> CHC
updateStepRule (r1,_) oldCHC = add_rule r1 oldCHC

getSplitPredicates :: (Rule,[PairRelatingSet]) -> [PairRelatingSet]
getSplitPredicates (_,list) = list

updateSplitRule :: (Rule,[PairRelatingSet]) -> CHC -> CHC
updateSplitRule (r1,_) oldCHC= add_rule r1 oldCHC


getSplitRules :: PairRelatingSet -> [(Rule,[PairRelatingSet])]
getSplitRules (PairRelatingSet oldLeft oldRight) = do
  let leftSplit = splitRelationSet oldLeft
  let rightSplit = splitRelationSet oldRight
  let leftNewRule = map (getPairOfNewRelationSetLeft (PairRelatingSet oldLeft oldRight)) leftSplit 
  let rightNewRule = map (getPairOfNewRelationSetRight (PairRelatingSet oldLeft oldRight))rightSplit
  leftNewRule ++ rightNewRule

getPairOfNewRelationSetLeft :: PairRelatingSet -> ([DerivationNode],[DerivationNode]) -> (Rule,[PairRelatingSet])
getPairOfNewRelationSetLeft (PairRelatingSet oldRight oldLeft) (newLeft1,newLeft2) = do
 let newPairRelatings = [(PairRelatingSet oldRight newLeft1) , (PairRelatingSet oldRight newLeft2)]
 let rule = getRule MkEmpty newPairRelatings (PairRelatingSet oldRight oldLeft)
 (rule,newPairRelatings)

getPairOfNewRelationSetRight :: PairRelatingSet -> ([DerivationNode],[DerivationNode]) ->(Rule, [PairRelatingSet])
getPairOfNewRelationSetRight (PairRelatingSet oldRight oldLeft) (newRight1,newRight2) = do
 let newPairRelatings = [(PairRelatingSet newRight1 oldLeft) , (PairRelatingSet newRight2 oldLeft)]
 let rule = getRule MkEmpty newPairRelatings (PairRelatingSet oldRight oldLeft)
 (rule,newPairRelatings)

splitRelationSet :: [DerivationNode] -> [([DerivationNode],[DerivationNode])]
splitRelationSet  list = do
 map (getSplitPair list) (getPowerSet list)

getSplitPair :: [DerivationNode] -> [DerivationNode] -> ([DerivationNode],[DerivationNode])
getSplitPair list sublist = ( (list List.\\ sublist) , sublist )

getPowerSet :: [DerivationNode] -> [ [DerivationNode] ]
getPowerSet theList = case theList of
  x:xs -> do
           let list = getPowerSet xs
           (map (x: ) list) ++ list
  _ -> [ [] ] 

getAllStepRules :: PairRelatingSet -> [ (Rule,PairRelatingSet) ] 
getAllStepRules (PairRelatingSet left right) = do
 let list1 = getAllRules 0 left
 let list2 = getAllRules 0 right
 let firstResult = map (getRulesAndPairRelatingSetLeft (PairRelatingSet left right)) list1
 let secondResult = map (getRulesAndPairRelatingSetRight (PairRelatingSet left right)) list2
 firstResult ++ secondResult

getRulesAndPairRelatingSetLeft :: PairRelatingSet -> (Expr,[DerivationNode]) -> (Rule,PairRelatingSet)
getRulesAndPairRelatingSetLeft (PairRelatingSet oldLeft oldRight) (expr1,newRelationSet) = do
  let newPairRelatingSet = (PairRelatingSet newRelationSet oldRight)
  let newRule = getRule expr1 [(PairRelatingSet oldLeft oldRight)] newPairRelatingSet
  (newRule,newPairRelatingSet)

getRulesAndPairRelatingSetRight :: PairRelatingSet -> (Expr,[DerivationNode]) -> (Rule,PairRelatingSet)
getRulesAndPairRelatingSetRight (PairRelatingSet oldLeft oldRight) (expr1,newRelationSet) = do
  let newPairRelatingSet = (PairRelatingSet oldRight oldLeft)
  let newRule = getRule expr1 [(PairRelatingSet oldLeft oldRight)] newPairRelatingSet
  (newRule,newPairRelatingSet)

getRule :: Expr -> [PairRelatingSet] -> PairRelatingSet -> Rule
getRule expr bodyPredicaes headPredicate = do
 let listOfPredicatesExpr = map getFunctionExpr bodyPredicaes
 Rule (MkAnd (expr:listOfPredicatesExpr)) (getFunctionExpr headPredicate) 


getAllRules :: Int -> [DerivationNode] -> [(Expr,[DerivationNode])]
getAllRules index list
  | index < length list = (getSuccessors index list) : (getAllRules (index+1) list)
  | otherwise = []    

getSuccessors :: Int -> [DerivationNode] ->(Expr ,[DerivationNode])
getSuccessors index list = do
  let DerivationNode _ (HyperEdge expr successors) _ _= list !! index
  let (x1,x2) = splitAt index list
  (expr,(x1 ++ (successors ++ (tail x2))))

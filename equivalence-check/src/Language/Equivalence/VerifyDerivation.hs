module Language.Equivalence.VerifyDerivation where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Data.List.Split
import Language.Equivalence.Verify
import Language.Equivalence.Derivations
import qualified Language.Equivalence.Types as Types
import System.Process
import qualified Data.Map as Map
-- Subexprssion is the data type represents the subexprrsion in derivation, first argument
-- string represents the name of the subexprssion, second argument list of string represents the list of variable name
-- Int represents the count of SubExprssion

-- function need to implemented, the substitute function, register all var

data HyperEdge = HyperEdge Expr [DerivationNode]
 deriving(Show,Eq,Ord)

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode [Var] HyperEdge Int
 deriving(Eq,Ord)

instance Show DerivationNode where
  show = derivationNode_short_print

data PrimitiveType =  PrimitiveType [PrimitiveType]
                    | PrimitiveBool
                    | PrimitiveInteger

-- need translate the coreExpr
derivationNode_short_print :: DerivationNode -> String
derivationNode_short_print (DerivationNode list (HyperEdge smtExpr successors) value) = do
  let string1 = "------------------------------------------------------\n Value "++show(value)++"\n"
  let string2 = string1 ++ (decl_var_list_pretty_print list)
  let string3 = string2 ++ (show smtExpr)
  let string4 = string3 ++ "\n------------------------------------------------\n"
  string4 ++ (unlines (map derivationNode_short_print successors) )

translateDT ::  Int -> Der -> (DerivationNode,Int)
translateDT uniqueId (Der ruleName expr successors) = case ruleName of
  RNConst -> translateRNConst uniqueId (Der ruleName expr successors)
  RNVar -> translateVar uniqueId (Der ruleName expr successors)
  RNOp -> translateRNOp uniqueId (Der ruleName expr successors)
  RNIteTrue -> translateRNIteTrue uniqueId (Der ruleName expr successors)
  RNIteFalse -> translateRNIteFalse uniqueId (Der ruleName expr successors)
  RNFix -> translateRNFix uniqueId (Der ruleName expr successors)
  RNApp -> translateRNApp uniqueId (Der ruleName expr successors)  

translateVar :: Int -> Der -> (DerivationNode,Int)
translateVar = undefined

translateRNConst :: Int -> Der -> (DerivationNode,Int)
translateRNConst = undefined

translateRNOp :: Int -> Der -> (DerivationNode,Int)
translateRNOp = undefined

getBinaryExpr :: DerivationNode -> DerivationNode -> Types.CoreExpr -> Expr
getBinaryExpr (DerivationNode varList1 _ _) (DerivationNode varList2 _ _) (Types.EBin binOp _ _) = case binOp of
  Types.Plus -> MkAdd [(ExprVar (last varList1)), (ExprVar (last varList2))]
  Types.Minus -> MkSub [(ExprVar (last varList1)), (ExprVar (last varList2))]
  Types.Mul -> MkMul [(ExprVar (last varList1)), (ExprVar (last varList2))]
  Types.Div -> MkDiv_1 (ExprVar (last varList1)) (ExprVar (last varList2))
  Types.Eq -> MkEq (ExprVar (last varList1)) (ExprVar (last varList2))
  Types.Ne -> MkNot (MkEq (ExprVar (last varList1)) (ExprVar (last varList2)))
  Types.Lt -> MkLt (ExprVar (last varList1)) (ExprVar (last varList2))
  Types.Le -> MkLe (ExprVar (last varList1)) (ExprVar (last varList2))
  Types.And -> MkAnd [(ExprVar (last varList1)), (ExprVar (last varList2))]
  Types.Or -> MkOr [(ExprVar (last varList1)), (ExprVar (last varList2))]
  _ -> MkEmpty

translateRNIteTrue :: Int -> Der -> (DerivationNode,Int)
translateRNIteTrue = undefined

translateRNIteFalse :: Int -> Der -> (DerivationNode,Int)
translateRNIteFalse = undefined

translateRNApp :: Int -> Der -> (DerivationNode,Int)
translateRNApp = undefined

bindingArgs :: Types.CoreExpr -> Int -> Int -> Expr
bindingArgs (Types.ELam (Types.Var name) _) uniqueId1 uniqueId2 = do
  let expr1 = (ExprVar (Var (name++"!"++show(uniqueId2)) (Types.getVarSort (Types.Var name))))
  let expr2 = (ExprVar (Var ("output!"++show(uniqueId1)++"@1") (Types.getVarSort (Types.Var name))))
  MkEq expr1 expr2

outputEquals :: Types.CoreExpr -> Int -> Int -> [Expr]
outputEquals doutExpr uniqueId1 uniqueId2 = do
  let sortList = Types.getSort doutExpr
  getEqualExpr uniqueId1 uniqueId2 1 sortList

freeVariablesEqual :: DEnv -> Int -> Int -> [Types.Var] -> [Expr]
freeVariablesEqual denv uniqueId1 uniqueId2 notEqualList = do
  let freeVarList = map (\(x,y) -> x) denv
  let sameVarList = filter (\x -> not (elem x notEqualList)) freeVarList
  map (freeVariableEqual uniqueId1 uniqueId2) sameVarList

translateRNFix :: Int -> Der -> (DerivationNode,Int)
translateRNFix = undefined

freeVariableEqual :: Int -> Int -> Types.Var ->  Expr
freeVariableEqual uniqueId1 uniqueId2 (Types.Var name)=
 MkEq (ExprVar (Var (name++"!"++(show uniqueId1)) (Types.getVarSort (Types.Var name)))) (ExprVar (Var (name++"!"++(show uniqueId2)) (Types.getVarSort (Types.Var name))))

--- translate var list get free variable list qizhou
getFreeVarList :: Int -> DEnv -> [Var]
getFreeVarList uniqueId denv = do
  let freeVarList = map (\(x,y) -> x) denv
  map (typeVarToSMTVar uniqueId) freeVarList

typeVarToSMTVar :: Int -> Types.Var -> Var
typeVarToSMTVar uniqueId (Types.Var name) = Var (name++"!"++(show uniqueId)) (Types.getVarSort (Types.Var name))

---- buld var list according to corresponding sort list
getVarList :: Int ->Int -> [Sort] -> [Var]
getVarList uniqueId index sortList = case sortList of
 x:xs -> (Var ("output!"++show(uniqueId)++"@"++show(index)) x):(getVarList uniqueId (index+1) xs)
 [] -> []

getEqualExpr :: Int -> Int ->Int -> [Sort] -> [Expr]
getEqualExpr uniqueId1 uniqueId2 index sortList = case sortList of
 x:xs -> do
     let expr1 = (ExprVar (Var ("output!"++show(uniqueId1)++"@"++show(index)) x))
     let expr2 = (ExprVar (Var ("output!"++show(uniqueId2)++"@"++show(index)) x))
     let eqExpr = MkEq expr1 expr2
     eqExpr:(getEqualExpr uniqueId1 uniqueId2 (index+1) xs)
 [] -> []


verifyPairs :: Der -> Der -> IO (Bool,(Map.Map Function Expr))
verifyPairs tree1 tree2 = do
  let (node1,number) = translateDT 0 tree1
  let (node2,number2) = translateDT number tree2
  let pairSet = PairRelatingSet [node1] [node2]
  let startSet =Set.insert pairSet (Set.empty)
  let varList1 = collectDerivationNodeVar node1
  let varList2 = collectDerivationNodeVar node2
  let query = generateQuery node1 node2
  let emptyCHC = CHC [] [] (varList1++varList2) query
  let theCHC = getAllRulesOfCHC startSet Set.empty emptyCHC
  (result,theMap) <- chc_execute theCHC
  return (result,theMap)

generateQuery :: DerivationNode ->DerivationNode -> Expr
generateQuery = undefined

generateArgSmtExpr :: Int -> Int -> (Types.Var , Types.CoreExpr) -> Expr
generateArgSmtExpr uniqueId1 uniqueId2 ((Types.Var name),_) = do
   let expr1 = (ExprVar (Var (name++"!"++show(uniqueId1)) IntegerSort))
   let expr2 = (ExprVar (Var (name++"!"++show(uniqueId2)) IntegerSort))
   MkEq expr1 expr2


collectDerivationNodeVar :: DerivationNode -> [Var]
collectDerivationNodeVar (DerivationNode varList (HyperEdge _ successors) theId) =
  varList ++ concat (map collectDerivationNodeVar successors)

getSortList :: [Var] -> [Sort]
getSortList list = case list of
  (Var _ sort):xs -> sort : getSortList xs
  _ -> []
getDerivatonNodeSortList :: DerivationNode -> [Sort]
getDerivatonNodeSortList (DerivationNode varList _ _)=getSortList varList

getStringName :: DerivationNode -> String -> String
getStringName (DerivationNode list _ uniqueId) oldName = 
  (show uniqueId) ++ "!" ++ oldName

getFunction:: PairRelatingSet -> Function
getFunction (PairRelatingSet list1 list2) = do
  let sortList = (concat (map getDerivatonNodeSortList list1)) ++ (concat (map getDerivatonNodeSortList list2))
  let uniqueName ="R"++(foldr getStringName "" list1) ++ (foldr getStringName "" list2)
  Function uniqueName sortList

getArgList :: [Var] -> [Parameter]
getArgList list = case list of
  x:xs -> (ParameterVar x) : getArgList xs
  _ -> []

getDerivatonNodeArgList :: DerivationNode -> [Parameter]
getDerivatonNodeArgList (DerivationNode varList _ _)= getArgList varList

getFunctionExpr :: PairRelatingSet -> Expr
getFunctionExpr (PairRelatingSet list1 list2) = do 
  let function = getFunction  (PairRelatingSet list1 list2)
  let args = (concat (map getDerivatonNodeArgList list1)) ++ (concat (map getDerivatonNodeArgList list2))
  ApplyFunction function args

data PairRelatingSet = PairRelatingSet [DerivationNode] [DerivationNode]
 deriving(Show,Eq,Ord)

getAllRulesOfCHC :: (Set.Set PairRelatingSet) -> (Set.Set PairRelatingSet) -> CHC -> CHC
getAllRulesOfCHC pairRelatingSet doneSet theCHC
 |null pairRelatingSet = theCHC
 |otherwise = do
               let singlePairRelatingSet = (Set.elemAt 0 pairRelatingSet)
               let newPairRelatingSet = (Set.deleteAt 0 pairRelatingSet)
               let newDoneSet = (Set.insert singlePairRelatingSet doneSet)
               let chcWithRegister = register_predicate (getFunction singlePairRelatingSet) theCHC
               let (newCHC,newPredicates) = updateCHC  singlePairRelatingSet chcWithRegister
               let newPairSet = getNewPairRelatingSet newDoneSet newPairRelatingSet newPredicates
               getAllRulesOfCHC newPairSet newDoneSet newCHC

getNewPairRelatingSet :: (Set.Set PairRelatingSet)->(Set.Set PairRelatingSet)->[PairRelatingSet]->(Set.Set PairRelatingSet)
getNewPairRelatingSet doneSet sets list = case list of
 x:xs -> if (Set.member x doneSet) then (getNewPairRelatingSet doneSet sets xs)
            else (Set.insert x (getNewPairRelatingSet doneSet sets xs))
 _ -> sets

updateCHC :: PairRelatingSet -> CHC -> (CHC,[PairRelatingSet])
updateCHC oldPredicate oldCHC = do
  let stepRuleList = getAllStepRules oldPredicate
  let splitRuleList = getSplitRules oldPredicate
  let newCHC1 = foldr updateStepRule oldCHC stepRuleList
  let newCHC2 = foldr updateSplitRule newCHC1 splitRuleList
  let newPrediactList = (map getStepPredicates stepRuleList) ++ (concat (map getSplitPredicates splitRuleList))
  (newCHC2,newPrediactList)
  -- (concat (map getSplitPredicates splitRuleList))


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
getPairOfNewRelationSetLeft (PairRelatingSet oldLeft oldRight) (newLeft1,newLeft2) = do
 let newPairRelatings = [(PairRelatingSet newLeft1 oldRight) , (PairRelatingSet newLeft2 oldRight)]
 let rule = getRule MkEmpty newPairRelatings (PairRelatingSet oldLeft oldRight)
 (rule,newPairRelatings)

getPairOfNewRelationSetRight :: PairRelatingSet -> ([DerivationNode],[DerivationNode]) ->(Rule, [PairRelatingSet])
getPairOfNewRelationSetRight (PairRelatingSet oldLeft oldRight) (newRight1,newRight2) = do
 let newPairRelatings = [(PairRelatingSet oldLeft newRight1) , (PairRelatingSet oldLeft newRight2)]
 let rule = getRule MkEmpty newPairRelatings (PairRelatingSet oldLeft oldRight)
 (rule,newPairRelatings)

splitRelationSet :: [DerivationNode] -> [([DerivationNode],[DerivationNode])]
splitRelationSet  list = eliminateEmptyPair (easySplit ((length list) -1) list)

easySplit :: Int -> [DerivationNode] -> [([DerivationNode],[DerivationNode])]
easySplit index list =
  if index > 0 then (splitAt index list):(easySplit (index-1) list)
    else []

eliminateEmptyPair :: [([DerivationNode],[DerivationNode])] -> [([DerivationNode],[DerivationNode])]
eliminateEmptyPair = filter (\(x1, x2) -> not (null x1) && not (null x2))

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
 let list1 = getFirstRules left
 let list2 = getFirstRules right
 let firstResult = map (getRulesAndPairRelatingSetLeft (PairRelatingSet left right)) list1
 let secondResult = map (getRulesAndPairRelatingSetRight (PairRelatingSet left right)) list2
 firstResult ++ secondResult

getRulesAndPairRelatingSetLeft :: PairRelatingSet -> (Expr,[DerivationNode]) -> (Rule,PairRelatingSet)
getRulesAndPairRelatingSetLeft (PairRelatingSet oldLeft oldRight) (expr1,newRelationSet) = do
  let newPairRelatingSet = (PairRelatingSet newRelationSet oldRight)
  let newRule = getRule expr1  [newPairRelatingSet] (PairRelatingSet oldLeft oldRight)
  (newRule,newPairRelatingSet)

getRulesAndPairRelatingSetRight :: PairRelatingSet -> (Expr,[DerivationNode]) -> (Rule,PairRelatingSet)
getRulesAndPairRelatingSetRight (PairRelatingSet oldLeft oldRight) (expr1,newRelationSet) = do
  let newPairRelatingSet = (PairRelatingSet oldLeft newRelationSet)
  let newRule = getRule expr1 [newPairRelatingSet] (PairRelatingSet oldLeft oldRight)
  (newRule,newPairRelatingSet)

getRule :: Expr -> [PairRelatingSet] -> PairRelatingSet -> Rule
getRule expr bodyPredicaes headPredicate = do
 let listOfPredicatesExpr = map getFunctionExpr (eliminateNullPredicate bodyPredicaes)
 Rule (MkAnd (expr:listOfPredicatesExpr)) (getFunctionExpr headPredicate) 

eliminateNullPredicate :: [PairRelatingSet] -> [PairRelatingSet]
eliminateNullPredicate list = case list of
  (PairRelatingSet x1 x2):xs -> if ((List.null x1) && (List.null x2)) then (eliminateNullPredicate xs)
                                   else (PairRelatingSet x1 x2):(eliminateNullPredicate xs)
  _ -> []

getAllRules :: Int -> [DerivationNode] -> [(Expr,[DerivationNode])]
getAllRules index list
  | index < length list = (getSuccessors index list) : (getAllRules (index+1) list)
  | otherwise = []

getFirstRules :: [DerivationNode] -> [(Expr,[DerivationNode])]
getFirstRules list = case list of
  x:xs -> do 
           let (smtExpr,newList) = (getSuccessors 0 list)
           if (((length newList) > 2) && ((length list) /= 1)) then []
             else [(smtExpr,newList)] 
  _ -> []

getSuccessors :: Int -> [DerivationNode] ->(Expr ,[DerivationNode])
getSuccessors index list = do
  let DerivationNode _ (HyperEdge expr successors) _= list !! index
  let (x1,x2) = splitAt index list
  (expr,(x1 ++ (successors ++ (tail x2))))

getIdList :: String -> [Int]
getIdList name = do
  let list = drop 1 name
  map read (splitOn "!" list)

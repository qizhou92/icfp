module Language.Equivalence.VerifyDerivation where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import Language.Equivalence.TypeInference
import qualified Data.Set as Set
import qualified Data.List as List
import Data.List.Split
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

-- need translate the coreExpr
derivationNode_short_print :: DerivationNode -> String
derivationNode_short_print (DerivationNode list (HyperEdge smtExpr successors) value) = do
  let string1 = "------------------------------------------------------\n Value "++show(value)++"\n"
  let string2 = string1 ++ (decl_var_list_pretty_print list)
  let string3 = string2 ++ (show smtExpr)
  let string4 = string3 ++ "\n------------------------------------------------\n"
  string4 ++ (unlines (map derivationNode_short_print successors) )

type TranslateEnv = [(Var, Type)]



typeToSortList :: Type -> [Sort]
typeToSortList (TVar _) = [IntegerSort]
typeToSortList (TInt) = [IntegerSort]
typeToSortList (TBool) = [BoolSort]
typeToSortList (TArr t1 t2) = (typeToSortList t1) ++ (typeToSortList t2)

generateVar :: String -> Int -> Int -> Sort -> Var
generateVar name uniqueId index sort = Var (name++"@"++show(index)++"!"++show(uniqueId)) sort

freeVarToArguments :: Int -> (Map.Map Types.CoreExpr Type) -> Types.Var -> [Var]
freeVarToArguments uniqueId typeEnv var@(Types.Var name) = do 
  let t1 = Map.findWithDefault TInt (Types.EVar var) typeEnv
  let sortList = typeToSortList t1
  let numberList = [1 .. (length sortList)]
  zipWith (generateVar name uniqueId) numberList sortList

outputToArguments :: Int -> (Map.Map Types.CoreExpr Type) -> Types.CoreExpr -> [Var]
outputToArguments uniqueId typeEnv expr = do 
  let t1 = Map.findWithDefault TInt expr typeEnv
  let sortList = typeToSortList t1
  let numberList = [1 .. (length sortList)]
  zipWith (generateVar "output" uniqueId) numberList sortList


getFreeVarList :: Int -> (Map.Map Types.CoreExpr Type) -> Types.CoreExpr -> [Var]
getFreeVarList uniqueId typeEnv expr = do
  let freeVarList = Set.toList (Types.freeVars expr)
  concat (map (freeVarToArguments uniqueId typeEnv) freeVarList)

setEqualVar :: Var -> Var -> Expr 
setEqualVar var1 var2 = MkEq (ExprVar var1) (ExprVar var2)

translateDT :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateDT typeEnv der@(Der ruleName _ _ _) = case ruleName of
  RNConst -> translateRNConst typeEnv der
  RNVar -> translateVar typeEnv der
  RNOp -> translateRNOp typeEnv der
  RNIte -> translateRNIte typeEnv der
  RNFix -> translateRNFix typeEnv der
  RNApp -> translateRNApp typeEnv der
  RNLam -> translateRNLam typeEnv der
  RASym -> translateRASym typeEnv der
translateVar :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateVar typeEnv der@(Der _ expr _ uniqueId) = do
  let freeVarsList = getFreeVarList uniqueId typeEnv expr
  let outputList = outputToArguments uniqueId typeEnv expr
  let expr = MkAnd (zipWith setEqualVar freeVarsList outputList)
  let hyperEdge = HyperEdge expr []
  DerivationNode (freeVarsList ++ outputList) hyperEdge uniqueId

translateRNConst ::(Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNConst _ der@(Der _ expr _ uniqueId) = case expr of
  Types.EInt value -> do
                let smtVar = Var ("output@1!"++show(uniqueId)) IntegerSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantInt value))
                let newHyperEdge = HyperEdge smtExpr []
                (DerivationNode [smtVar] newHyperEdge uniqueId)
  Types.EBool value -> do
                let smtVar = Var ("output@1!"++show(uniqueId)) BoolSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantBool value))
                let newHyperEdge = HyperEdge smtExpr []
                (DerivationNode [smtVar] newHyperEdge uniqueId)

translateRNOp :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNOp typeEnv der@(Der _ expr list uniqueId) = do
  let firstDer@(Der _ expr1 _ _) = list !! 0
  let secondDer@(Der _ expr2 _ _) = list !! 1
  let dt1@(DerivationNode _ _ id1) = translateDT typeEnv firstDer
  let dt2@(DerivationNode _ _ id2) = translateDT typeEnv secondDer
  let op1FreeVariables = Types.freeVars expr1
  let op2FreeVariables = Types.freeVars expr2
  let allFreeVariables = Set.union op1FreeVariables op2FreeVariables
  let firstEqualFreeVariables =Set.toList (Set.intersection op1FreeVariables allFreeVariables)
  let secondEqualFreeVariables =Set.toList (Set.intersection op2FreeVariables allFreeVariables)
  let op1FreeVariables1 = concat (map (freeVarToArguments id1 typeEnv)  firstEqualFreeVariables)
  let op1FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) firstEqualFreeVariables)
  let op2FreeVariables1 = concat (map (freeVarToArguments id2 typeEnv) secondEqualFreeVariables)
  let op2FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) secondEqualFreeVariables)
  let currentFreeVar = concat (map (freeVarToArguments uniqueId typeEnv) (Set.toList allFreeVariables))
  let allFreeVariablesEqaul = (zipWith setEqualVar op1FreeVariables1 op1FreeVariables2) ++ (zipWith setEqualVar op2FreeVariables1 op2FreeVariables2)
  let allOutput = (outputToArguments uniqueId typeEnv expr) 
  let outputExpr = ExprVar (allOutput !! 0)
  let setEqualResult = MkEq outputExpr (getBinaryExpr dt1 dt2 expr)
  let theWholeSmtExpr = MkAnd (setEqualResult:allFreeVariablesEqaul)
  let newHyperEdge = HyperEdge theWholeSmtExpr [dt1,dt2]
  (DerivationNode (currentFreeVar ++ allOutput) newHyperEdge uniqueId)

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

translateRNIte :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNIte typeEnv der@(Der _ expr list uniqueId) = do
  let condition@(Der _ expr1 _ _) = list !! 0
  let trueBranch@(Der _ expr2 _ _) = list !! 1
  let falseBranch@(Der _ expr3 _ _) = list !! 2
  let dt1@(DerivationNode varList _ id1) = translateDT typeEnv condition
  let dt2@(DerivationNode _ _ id2) = translateDT typeEnv trueBranch
  let dt3@(DerivationNode _ _ id3) = translateDT typeEnv falseBranch
  let op1FreeVariables = Types.freeVars expr1
  let op2FreeVariables = Types.freeVars expr2
  let op3FreeVariables = Types.freeVars expr3
  let allFreeVariables = (Set.union (Set.union op1FreeVariables op2FreeVariables) op3FreeVariables)
  let firstEqualFreeVariables =Set.toList (Set.intersection op1FreeVariables allFreeVariables)
  let secondEqualFreeVariables =Set.toList (Set.intersection op2FreeVariables allFreeVariables)
  let thirdEqualFreeVariables =Set.toList (Set.intersection op3FreeVariables allFreeVariables)
  let op1FreeVariables1 = concat (map (freeVarToArguments id1 typeEnv)  firstEqualFreeVariables)
  let op1FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) firstEqualFreeVariables)
  let op2FreeVariables1 = concat (map (freeVarToArguments id2 typeEnv) secondEqualFreeVariables)
  let op2FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) secondEqualFreeVariables)
  let op3FreeVariables1 = concat (map (freeVarToArguments id3 typeEnv) thirdEqualFreeVariables)
  let op3FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) thirdEqualFreeVariables)
  let currentFreeVar = concat (map (freeVarToArguments uniqueId typeEnv) (Set.toList allFreeVariables))
  let allFreeVariablesEqaul1 = (zipWith setEqualVar op1FreeVariables1 op1FreeVariables2) ++ (zipWith setEqualVar op2FreeVariables1 op2FreeVariables2)
  let allFreeVariablesEqaul2 = (zipWith setEqualVar op1FreeVariables1 op1FreeVariables2) ++ (zipWith setEqualVar op3FreeVariables1 op3FreeVariables2)
  let trueOutput = outputToArguments id2 typeEnv expr2
  let falseOutput = outputToArguments id3 typeEnv expr3
  let output = outputToArguments uniqueId typeEnv expr
  let outputSetEqual1 = (zipWith setEqualVar trueOutput output)
  let outputSetEqual2 = (zipWith setEqualVar falseOutput output)
  let smtExpr1 = MkAnd ((ExprVar (last varList)):(allFreeVariablesEqaul1++outputSetEqual1))
  let smtExpr2 = MkAnd ( (MkNot (ExprVar (last varList))) :(allFreeVariablesEqaul2++outputSetEqual2))
  let smtExpr = MkOr [smtExpr1,smtExpr2]
  let newHyperEdge = HyperEdge smtExpr [dt1,dt2,dt3]
  (DerivationNode (currentFreeVar ++ output) newHyperEdge uniqueId)

translateRNApp :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNApp typeEnv der@(Der _ expr list uniqueId) = do
  let abstraction@(Der _ expr1 _ _) = list !! 0
  let arguments@(Der _ expr2 _ _) = list !! 1
  let dt1@(DerivationNode _ _ id1) = translateDT typeEnv abstraction
  let dt2@(DerivationNode _ _ id2) = translateDT typeEnv arguments
  let op1FreeVariables = Types.freeVars expr1
  let op2FreeVariables = Types.freeVars expr2
  let allFreeVariables = Set.union op1FreeVariables op2FreeVariables
  let firstEqualFreeVariables =Set.toList (Set.intersection op1FreeVariables allFreeVariables)
  let secondEqualFreeVariables =Set.toList (Set.intersection op2FreeVariables allFreeVariables)
  let op1FreeVariables1 = concat (map (freeVarToArguments id1 typeEnv)  firstEqualFreeVariables)
  let op1FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) firstEqualFreeVariables)
  let op2FreeVariables1 = concat (map (freeVarToArguments id2 typeEnv) secondEqualFreeVariables)
  let op2FreeVariables2 = concat (map (freeVarToArguments uniqueId typeEnv) secondEqualFreeVariables)
  let currentFreeVar = concat (map (freeVarToArguments uniqueId typeEnv) (Set.toList allFreeVariables))
  let allFreeVariablesEqaul = (zipWith setEqualVar op1FreeVariables1 op1FreeVariables2) ++ (zipWith setEqualVar op2FreeVariables1 op2FreeVariables2)
  let abstractionOutputs = outputToArguments id1 typeEnv expr1
  let argumentsOutputs = outputToArguments id2 typeEnv expr2
  let appOutputs = outputToArguments uniqueId typeEnv expr
  let setEqualOfArgumentsAndOutput = zipWith setEqualVar abstractionOutputs (argumentsOutputs++appOutputs)
  let smtExpr = MkAnd (allFreeVariablesEqaul ++ setEqualOfArgumentsAndOutput)
  let newHyperEdge = HyperEdge smtExpr [dt1,dt2]
  (DerivationNode (currentFreeVar ++ appOutputs) newHyperEdge uniqueId)

translateRNFix :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNFix typeEnv der@(Der _ expr list uniqueId) = do
  let insideFix = list !! 0
  let dt1@(DerivationNode _ _ id1) = translateDT typeEnv insideFix
  let freeVarlist1 = getFreeVarList id1 typeEnv expr
  let freeVarlist2 = getFreeVarList uniqueId typeEnv expr
  let output1 = outputToArguments id1 typeEnv expr
  let output2 = outputToArguments uniqueId typeEnv expr
  let setFreeEqual = zipWith setEqualVar freeVarlist1 freeVarlist2
  let setOutputEqaul = zipWith setEqualVar output1 output2
  let smtExpr = MkAnd (setFreeEqual++setOutputEqaul)
  let newHyperEdge = HyperEdge smtExpr [dt1]
  (DerivationNode (freeVarlist2 ++ output2) newHyperEdge uniqueId)

translateRNLam :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNLam typeEnv der@(Der _ expr@(Types.ELam var expr1) list uniqueId) = do
  let insideLam@(Der _ expr2 _ _) = list !! 0
  let dt1@(DerivationNode _ _ id1) = translateDT typeEnv insideLam
  let insideLam = Types.freeVars expr1
  let withoutLam =Set.toList (Set.filter (/= var) insideLam)
  let freeVars1 = concat (map (freeVarToArguments id1 typeEnv) withoutLam)
  let freeVars2 = concat (map (freeVarToArguments uniqueId typeEnv) withoutLam)
  let (TArr t1 t2) = Map.findWithDefault (TArr TInt TInt) expr typeEnv
  let insidLamOutputs = outputToArguments id1 typeEnv expr1
  let lamOutputs = outputToArguments uniqueId typeEnv expr
  let dropFirstPart = drop ((length lamOutputs) - (length insidLamOutputs)) lamOutputs
  let setOutputEqual = zipWith setEqualVar insidLamOutputs dropFirstPart
  let freeVarsEqual = zipWith setEqualVar freeVars1 freeVars2
  if (Set.member var insideLam) then do
      let thisVar = freeVarToArguments id1 typeEnv var
      let firstPartEqual = take ((length lamOutputs) - (length insidLamOutputs)) lamOutputs
      let setVarEqual = zipWith setEqualVar thisVar firstPartEqual
      let smtExpr = MkAnd (freeVarsEqual ++ setVarEqual ++ setOutputEqual)
      let newHyperEdge = HyperEdge smtExpr [dt1]
      (DerivationNode (freeVars2 ++ lamOutputs) newHyperEdge uniqueId)
    else do
      let smtExpr = MkAnd (freeVarsEqual ++ setOutputEqual)
      let newHyperEdge = HyperEdge smtExpr [dt1]
      (DerivationNode (freeVars2 ++ lamOutputs) newHyperEdge uniqueId)

translateRASym :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode 
translateRASym typeEnv der@(Der _ expr _ uniqueId) = do
  let freeVarlist = getFreeVarList uniqueId typeEnv expr
  let output = outputToArguments uniqueId typeEnv expr
  let smtExpr = ExprConstant (ConstantBool False)
  let newHyperEdge = HyperEdge smtExpr []
  (DerivationNode (freeVarlist ++ output) newHyperEdge uniqueId)

verifyPairs :: Der -> Der -> IO (Bool,(Map.Map Function Expr))
verifyPairs tree1@(Der _ expr1 _ _) tree2@(Der _ expr2 _ _) = do
  let type1 = infereType expr1
  let type2 = infereType expr2
  case type1 of
    Left err -> return (False, Map.empty)
    Right typeMap1 -> case type2 of
                       Left err2 ->return (False, Map.empty)
                       Right typeMap2 -> verifyPairsWithType tree1 tree2 typeMap1 typeMap2

verifyPairsWithType :: Der -> Der -> (Map.Map Types.CoreExpr Type) -> (Map.Map Types.CoreExpr Type) -> IO (Bool,(Map.Map Function Expr))
verifyPairsWithType tree1@(Der _ expr _ _) tree2 typeMap1 typeMap2 = do 
  let node1@(DerivationNode varList _ _) = translateDT typeMap1 tree1
  let node2 = translateDT typeMap2 tree2
  let pairSet = PairRelatingSet [node1] [node2]
  let startSet =Set.insert pairSet (Set.empty)
  let varList1 = collectDerivationNodeVar node1
  let varList2 = collectDerivationNodeVar node2
  let t1 = Map.findWithDefault TInt expr typeMap1
  let index = (length varList) - (getOutputLength t1) 
  let query = generateQuery index node1 node2
  let emptyCHC = CHC [] [] (varList1++varList2) query
  let theCHC = getAllRulesOfCHC startSet Set.empty emptyCHC
  (result,theMap) <- chc_execute theCHC
  return (result,theMap)

getOutputLength :: Type -> Int
getOutputLength TInt = 1
getOutputLength TBool = 1
getOutputLength (TArr t1 t2) = length (typeToSortList t2)
getOutputLength (TVar _) = 1

generateQuery :: Int -> DerivationNode ->DerivationNode -> Expr
generateQuery index node1@(DerivationNode varList1 _ _) node2@(DerivationNode varList2 _ _) = do
  let (arguments1, outputs1) = splitAt index varList1 
  let (arguments2, outputs2) = splitAt index varList2
  let basePairSet = PairRelatingSet [node1] [node2]
  let predicate = getFunctionExpr basePairSet
  let argumentsEqual = (zipWith setEqualVar arguments1 arguments2)
  let outputEqual = MkAnd (zipWith setEqualVar outputs1 outputs2)
  let outputNotEqual = MkNot outputEqual
  if (length argumentsEqual) > 0  then (MkAnd [predicate, (MkAnd argumentsEqual) ,outputNotEqual])
     else (MkAnd [predicate, outputNotEqual])

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

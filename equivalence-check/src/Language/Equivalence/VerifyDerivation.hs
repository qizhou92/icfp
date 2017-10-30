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

data RelationalType = RelationalLeaf 


data HyperEdge = HyperEdge Expr [DerivationNode]
 deriving(Show,Eq,Ord)

-- Node represents the given derivation, the first argument is current SubExprssion, the second argument is the list of HyperEdge

data DerivationNode = DerivationNode RuleName [Var] HyperEdge Int
 deriving(Eq,Ord)

instance Show DerivationNode where
  show = derivationNode_short_print

-- need translate the coreExpr
derivationNode_short_print :: DerivationNode -> String
derivationNode_short_print (DerivationNode ruleName list (HyperEdge smtExpr successors) value) = do
  let string1 = "------------------------------------------------------\n Value "++show(value)++"\n"
  let string2 = string1 ++ (show ruleName) ++"\n"
  let string3 = string2 ++ (decl_var_list_pretty_print list)
  let string4 = string3 ++ (show smtExpr)
  let string5 = string4 ++ "\n------------------------------------------------\n"
  string5 ++ (unlines (map derivationNode_short_print successors) )

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
translateDT typeEnv der@(Der ruleName _ _ _ _) = case ruleName of
  RNConst -> translateRNConst typeEnv der
  RNVar -> translateVar typeEnv der
  RNOp -> translateRNOp typeEnv der
  RNIte -> translateRNIte typeEnv der
  RNFix -> translateRNFix typeEnv der
  RNApp -> translateRNApp typeEnv der
  RNLam -> translateRNLam typeEnv der
  RASym -> translateRASym typeEnv der

translateVar :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateVar typeEnv der@(Der _ expr oExpr _ uniqueId) = do
  let freeVarsList = getFreeVarList uniqueId typeEnv expr
  let outputList = outputToArguments uniqueId typeEnv oExpr
  let expr = MkAnd (zipWith setEqualVar freeVarsList outputList)
  let hyperEdge = HyperEdge expr []
  DerivationNode RNVar (freeVarsList ++ outputList) hyperEdge uniqueId

translateRNConst ::(Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNConst _ der@(Der _ expr _ _ uniqueId) = case expr of
  Types.EInt value -> do
                let smtVar = Var ("output@1!"++show(uniqueId)) IntegerSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantInt value))
                let newHyperEdge = HyperEdge smtExpr []
                (DerivationNode RNConst [smtVar] newHyperEdge uniqueId)
  Types.EBool value -> do
                let smtVar = Var ("output@1!"++show(uniqueId)) BoolSort
                let smtExpr = MkEq (ExprVar smtVar) (ExprConstant (ConstantBool value))
                let newHyperEdge = HyperEdge smtExpr []
                (DerivationNode RNConst [smtVar] newHyperEdge uniqueId)

translateRNOp :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNOp typeEnv der@(Der _ expr oExpr list uniqueId) = do
  let firstDer@(Der _ expr1 _ _ _) = list !! 0
  let secondDer@(Der _ expr2 _ _ _) = list !! 1
  let dt1@(DerivationNode _ _ _ id1) = translateDT typeEnv firstDer
  let dt2@(DerivationNode _ _ _ id2) = translateDT typeEnv secondDer
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
  let allOutput = (outputToArguments uniqueId typeEnv oExpr) 
  let outputExpr = ExprVar (allOutput !! 0)
  let setEqualResult = MkEq outputExpr (getBinaryExpr dt1 dt2 expr)
  let theWholeSmtExpr = MkAnd (setEqualResult:allFreeVariablesEqaul)
  let newHyperEdge = HyperEdge theWholeSmtExpr [dt1,dt2]
  (DerivationNode RNOp (currentFreeVar ++ allOutput) newHyperEdge uniqueId)

getBinaryExpr :: DerivationNode -> DerivationNode -> Types.CoreExpr -> Expr
getBinaryExpr (DerivationNode _ varList1 _ _) (DerivationNode _ varList2 _ _) (Types.EBin binOp _ _) = case binOp of
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
translateRNIte typeEnv der@(Der _ expr oExpr list uniqueId) = do
  let condition@(Der _ expr1 _ _ _) = list !! 0
  let trueBranch@(Der _ expr2 oExpr2 _ _) = list !! 1
  let falseBranch@(Der _ expr3 oExpr3 _ _) = list !! 2
  let dt1@(DerivationNode _ varList _ id1) = translateDT typeEnv condition
  let dt2@(DerivationNode _ _ _ id2) = translateDT typeEnv trueBranch
  let dt3@(DerivationNode _ _ _ id3) = translateDT typeEnv falseBranch
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
  let trueOutput = outputToArguments id2 typeEnv oExpr2
  let falseOutput = outputToArguments id3 typeEnv oExpr3
  let output = outputToArguments uniqueId typeEnv oExpr
  let outputSetEqual1 = (zipWith setEqualVar trueOutput output)
  let outputSetEqual2 = (zipWith setEqualVar falseOutput output)
  let smtExpr1 = MkAnd ((ExprVar (last varList)):(allFreeVariablesEqaul1++outputSetEqual1))
  let smtExpr2 = MkAnd ( (MkNot (ExprVar (last varList))) :(allFreeVariablesEqaul2++outputSetEqual2))
  let smtExpr = MkOr [smtExpr1,smtExpr2]
  let newHyperEdge = HyperEdge smtExpr [dt1,dt2,dt3]
  (DerivationNode RNIte (currentFreeVar ++ output) newHyperEdge uniqueId)

translateRNApp :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNApp typeEnv der@(Der _ expr oExpr list uniqueId) = do
  let abstraction@(Der _ expr1 oExpr1 _ _) = list !! 0
  let arguments@(Der _ expr2 oExpr2 _ _) = list !! 1
  let dt1@(DerivationNode _ _ _ id1) = translateDT typeEnv abstraction
  let dt2@(DerivationNode _ _ _ id2) = translateDT typeEnv arguments
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
  let abstractionOutputs = outputToArguments id1 typeEnv oExpr1
  let argumentsOutputs = outputToArguments id2 typeEnv oExpr2
  let appOutputs = outputToArguments uniqueId typeEnv oExpr
  let setEqualOfArgumentsAndOutput = zipWith setEqualVar abstractionOutputs (argumentsOutputs++appOutputs)
  let smtExpr = MkAnd (allFreeVariablesEqaul ++ setEqualOfArgumentsAndOutput)
  let newHyperEdge = HyperEdge smtExpr [dt1,dt2]
  (DerivationNode RNApp (currentFreeVar ++ appOutputs) newHyperEdge uniqueId)

translateRNFix :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNFix typeEnv der@(Der _ expr oExpr list uniqueId) = do
  let insideFix = list !! 0
  let dt1@(DerivationNode _ _ _ id1) = translateDT typeEnv insideFix
  let freeVarlist1 = getFreeVarList id1 typeEnv expr
  let freeVarlist2 = getFreeVarList uniqueId typeEnv expr
  let output1 = outputToArguments id1 typeEnv oExpr
  let output2 = outputToArguments uniqueId typeEnv oExpr
  let setFreeEqual = zipWith setEqualVar freeVarlist1 freeVarlist2
  let setOutputEqaul = zipWith setEqualVar output1 output2
  let smtExpr = MkAnd (setFreeEqual++setOutputEqaul)
  let newHyperEdge = HyperEdge smtExpr [dt1]
  (DerivationNode RNFix (freeVarlist2 ++ output2) newHyperEdge uniqueId)

translateRNLam :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode
translateRNLam typeEnv der@(Der _ expr@(Types.ELam var expr1) oExpr@(Types.ELam _ oExpr1) list uniqueId) = do
  let insideLam@(Der _ expr2 _ _ _) = list !! 0
  let dt1@(DerivationNode _ _ _ id1) = translateDT typeEnv insideLam
  let insideLam = Types.freeVars expr1
  let withoutLam =Set.toList (Set.filter (/= var) insideLam)
  let freeVars1 = concat (map (freeVarToArguments id1 typeEnv) withoutLam)
  let freeVars2 = concat (map (freeVarToArguments uniqueId typeEnv) withoutLam)
  let (TArr t1 t2) = Map.findWithDefault (TArr TInt TInt) expr typeEnv
  let insidLamOutputs = outputToArguments id1 typeEnv oExpr1
  let lamOutputs = outputToArguments uniqueId typeEnv oExpr
  let dropFirstPart = drop ((length lamOutputs) - (length insidLamOutputs)) lamOutputs
  let setOutputEqual = zipWith setEqualVar insidLamOutputs dropFirstPart
  let freeVarsEqual = zipWith setEqualVar freeVars1 freeVars2
  if (Set.member var insideLam) then do
      let thisVar = freeVarToArguments id1 typeEnv var
      let firstPartEqual = take ((length lamOutputs) - (length insidLamOutputs)) lamOutputs
      let setVarEqual = zipWith setEqualVar thisVar firstPartEqual
      let smtExpr = MkAnd (freeVarsEqual ++ setVarEqual ++ setOutputEqual)
      let newHyperEdge = HyperEdge smtExpr [dt1]
      (DerivationNode RNLam (freeVars2 ++ lamOutputs) newHyperEdge uniqueId)
    else do
      let smtExpr = MkAnd (freeVarsEqual ++ setOutputEqual)
      let newHyperEdge = HyperEdge smtExpr [dt1]
      (DerivationNode RNLam (freeVars2 ++ lamOutputs) newHyperEdge uniqueId)

translateRASym :: (Map.Map Types.CoreExpr Type) -> Der -> DerivationNode 
translateRASym typeEnv der@(Der _ expr oExpr _ uniqueId) = do
  let freeVarlist = getFreeVarList uniqueId typeEnv oExpr
  let output = outputToArguments uniqueId typeEnv oExpr
  let smtExpr = ExprConstant (ConstantBool False)
  let newHyperEdge = HyperEdge smtExpr []
  (DerivationNode RASym (freeVarlist ++ output) newHyperEdge uniqueId)

verifyPairs :: Der -> Der -> IO (Bool,(Map.Map String Expr))
verifyPairs tree1@(Der _ expr1 _ _ _) tree2@(Der _ expr2 _ _ _) = do
  let type1 = infereType expr1
  let type2 = infereType expr2
  case type1 of
    Left err -> do
                  print err 
                  return (False, Map.empty)
    Right typeMap1 -> case type2 of
                       Left err2 -> do
                                     print err2
                                     return (False, Map.empty)
                       Right typeMap2 -> do
                                          verifyPairsWithType tree1 tree2 typeMap1 typeMap2

verifyPairsWithType :: Der -> Der -> (Map.Map Types.CoreExpr Type) -> (Map.Map Types.CoreExpr Type) -> IO (Bool,(Map.Map String Expr))
verifyPairsWithType tree1@(Der _ expr _ _ _) tree2 typeMap1 typeMap2 = do 
  let node1@(DerivationNode _ varList _ _) = translateDT typeMap1 tree1
  print node1
  let node2 = translateDT typeMap2 tree2
  print node2
  let startLocation = Location [node1] [node2] 
  let startSet =Set.insert startLocation (Set.empty)
  let varList1 = collectDerivationNodeVar node1
  let varList2 = collectDerivationNodeVar node2
  let t1 = Map.findWithDefault TInt expr typeMap1
  let index = (length varList) - (getOutputLength t1) 
  let query = generateQuery index node1 node2
  let emptyCHC = CHC [] [] (varList1++varList2) query
  let theCHC = getAllRulesOfCHC startSet Set.empty emptyCHC
  print theCHC
  (result,theMap) <- chc_execute theCHC
  return (result, (Map.mapKeys fromFunctionToString theMap))

fromFunctionToString :: Function -> String
fromFunctionToString (Function name _) = name

getOutputLength :: Type -> Int
getOutputLength TInt = 1
getOutputLength TBool = 1
getOutputLength (TArr t1 t2) = length (typeToSortList t2)
getOutputLength (TVar _) = 1

generateQuery :: Int -> DerivationNode ->DerivationNode -> Expr
generateQuery index node1@(DerivationNode _ varList1 _ _) node2@(DerivationNode _ varList2 _ _) = do
  let (arguments1, outputs1) = splitAt index varList1 
  let (arguments2, outputs2) = splitAt index varList2
  let basePairSet = Location [node1] [node2]
  let predicate = getFunctionExpr basePairSet
  let argumentsEqual = (zipWith setEqualVar arguments1 arguments2)
  let outputEqual = MkAnd (zipWith setEqualVar outputs1 outputs2)
  let outputNotEqual = MkNot outputEqual
  if (length argumentsEqual) > 0  then (MkAnd [predicate, (MkAnd argumentsEqual) ,outputNotEqual])
     else (MkAnd [predicate, outputNotEqual])


collectDerivationNodeVar :: DerivationNode -> [Var]
collectDerivationNodeVar (DerivationNode _ varList (HyperEdge _ successors) theId) =
  varList ++ concat (map collectDerivationNodeVar successors)

getDerivatonNodeSortList :: DerivationNode -> [Sort]
getDerivatonNodeSortList (DerivationNode _ varList _ _)=map (\x@(Var _ sort) -> sort) varList

getStringName :: DerivationNode -> String -> String
getStringName (DerivationNode _ list _ uniqueId) oldName = 
  (show uniqueId) ++ "!" ++ oldName

getFunction:: Location -> Function
getFunction (Location list1 list2) = do
  let sortList = (concat (map getDerivatonNodeSortList (list1++list2)))
  let uniqueName ="R"++(foldr getStringName "" (list1 ++ list2))
  Function uniqueName sortList

getDerivatonNodeArgList :: DerivationNode -> [Parameter]
getDerivatonNodeArgList (DerivationNode _ varList _ _)= map (\x -> ParameterVar x ) varList

getFunctionExpr :: Location -> Expr
getFunctionExpr location@(Location list1 list2) = do 
  let function = getFunction location
  let args = (concat (map getDerivatonNodeArgList (list1 ++ list2) ))
  ApplyFunction function args

data Location = Location [DerivationNode] [DerivationNode]
 deriving(Show,Eq,Ord)

getAllRulesOfCHC :: (Set.Set Location) -> (Set.Set Location) -> CHC -> CHC
getAllRulesOfCHC locationSet doneSet theCHC
 |null locationSet = theCHC
 |otherwise = do
               let location = (Set.elemAt 0 locationSet)
               let newLocationSet1 = (Set.deleteAt 0 locationSet)
               let newDoneSet = (Set.insert location doneSet)
               let chcWithRegister = register_predicate (getFunction location) theCHC
               let (newCHC,possibleNewLocations) = updateCHC  location chcWithRegister
               let newLocations = filter (\x -> Set.notMember x doneSet) possibleNewLocations
               let newLocationSet2 = foldr Set.insert newLocationSet1 newLocations 
               getAllRulesOfCHC newLocationSet2 newDoneSet newCHC

updateCHC :: Location -> CHC -> (CHC,[Location])
updateCHC location oldCHC = do
  let stepRuleList = getStepRule location
  let splitRuleList = getSplitRules location
  let newCHC1 = foldr (\(rule,location) chc -> add_rule rule chc) oldCHC stepRuleList
  let newCHC2 = foldr (\(rule,location) chc -> add_rule rule chc) newCHC1 splitRuleList
  let newLocations =(concat (map (\(rule,location) -> location) stepRuleList))++ (concat (map (\(rule,location) -> location) splitRuleList))
  (newCHC2,newLocations)


getSplitRules2 :: Location -> [(Rule,[Location])]
getSplitRules2 location@(Location list1 list2) = undefined

getSplitRules :: Location -> [(Rule,[Location])]
getSplitRules location@(Location list1 list2) = do
  let splitLeft = splitLocation list1
  let splitRight = splitLocation list2
  let newLeftLocations = map (\(x,y) -> [(Location x list2),(Location y list2)]) splitLeft
  let newRightLocations = map (\(x,y) -> [(Location list1 x),(Location list1 y)]) splitRight
  map (\x ->( (getRule MkEmpty x location), x) ) (newLeftLocations ++ newRightLocations)


--split might need to change for non-order split
splitLocation :: [DerivationNode] -> [([DerivationNode],[DerivationNode])]
splitLocation location = map  ( (\x y -> splitAt y x) location) [1 .. ((length location)-1)]


getStepRule :: Location -> [(Rule,[Location])]
getStepRule location@(Location [] []) = []
getStepRule location@(Location [x] []) = do
 let (smtExprs, newLocations) = collapseStepRuleLeftMask [] x 
 let newRule = Rule smtExprs (getFunctionExpr location)
 [(newRule , newLocations)]
getStepRule location@(Location [] [x]) = do
 let (smtExprs, newLocations) = collapseStepRuleRightMask [] x
 let newRule = Rule smtExprs (getFunctionExpr location)
 [(newRule , newLocations)]
getStepRule location@(Location [x1] [x2]) = do
 let (smtExprs1, newLocation1) = collapseStepRuleLeftMask [x2] x1
 let newRule1 = Rule smtExprs1 (getFunctionExpr location)
 let (smtExprs2, newLocation2) = collapseStepRuleRightMask [x1] x2
 let newRule2 = Rule smtExprs2 (getFunctionExpr location)
 [(newRule1 , newLocation1) , (newRule2 , newLocation2)]

getStepRule _ = []

collapseStepRuleRightMask :: [DerivationNode] ->  DerivationNode -> (Expr,[Location])
collapseStepRuleRightMask leftList node@(DerivationNode _  _ (HyperEdge smtExpr successors) _ ) = do
 let collapseExpr = map (collapseStepRuleRight leftList) successors
 let (expr, locations) = foldr (\(x,y) (x1,y2)-> (x:x1,y++y2)) ([],[]) collapseExpr
 let newExpr1 =(MkAnd (smtExpr:expr))
 let newLocation = Location leftList []
 let newExpr2 = MkAnd ([(getFunctionExpr newLocation),smtExpr]++expr)
 if (length(successors) /= 0) then (newExpr1,locations)
  else if (length leftList) == 0 then (newExpr1,locations)
         else (newExpr2,[newLocation])

collapseStepRuleRight :: [DerivationNode] ->  DerivationNode -> (Expr,[Location])
collapseStepRuleRight leftList node@(DerivationNode RNFix _ (HyperEdge smtExpr successors) _) = do
  let newLocation = (Location leftList [node])
  (getFunctionExpr newLocation, [newLocation])

collapseStepRuleRight leftList node@(DerivationNode RASym _ (HyperEdge smtExpr successors) _) = do
  let newLocation =  (Location leftList [node])
  (getFunctionExpr newLocation , [newLocation])

collapseStepRuleRight leftList node@(DerivationNode RNIte _ (HyperEdge smtExpr@(MkOr [e1,e2]) successors) _) = do
  let (condExpr,newLocation1) = collapseStepRuleRight leftList (successors !! 0)
  let (trueExpr,newLocation2) = collapseStepRuleRight leftList (successors !! 1)
  let (falseExpr,newLocation3) = collapseStepRuleRight leftList (successors !! 2)
  let newExpr = (MkOr [ (MkAnd [condExpr,trueExpr,e1]),(MkAnd [condExpr,falseExpr,e2])])
  (newExpr, (newLocation1 ++ newLocation2 ++ newLocation3))

collapseStepRuleRight leftList node@(DerivationNode _  _ (HyperEdge smtExpr successors) _ ) = do
 let collapseExpr = map (collapseStepRuleRight leftList) successors
 let (expr, locations) = foldr (\(x,y) (x1,y2)-> (x:x1,y++y2)) ([],[]) collapseExpr
 let newExpr1 =(MkAnd (smtExpr:expr))
 let newLocation = Location leftList []
 let newExpr2 = MkAnd ([(getFunctionExpr newLocation),smtExpr]++expr)
 if (length(successors) /= 0) then (newExpr1,locations)
  else if (length leftList) == 0 then (newExpr1,locations)
         else (newExpr2,[newLocation])

collapseStepRuleLeftMask :: [DerivationNode] ->  DerivationNode -> (Expr,[Location])
collapseStepRuleLeftMask rightList node@(DerivationNode _  _ (HyperEdge smtExpr successors) _ ) = do
 let collapseExpr = map (collapseStepRuleLeft rightList) successors
 let (expr, locations) = foldr (\(x,y) (x1,y2)-> (x:x1,y++y2)) ([],[]) collapseExpr
 let newExpr1 = (MkAnd (smtExpr:expr))
 let newLocation = Location [] rightList
 let newExpr2 = MkAnd ([(getFunctionExpr newLocation),smtExpr]++expr)
 if (length(successors) /= 0) then (newExpr1,locations)
  else if (length rightList) == 0 then (newExpr1,locations)
         else (newExpr2,[newLocation])

collapseStepRuleLeft :: [DerivationNode] ->  DerivationNode -> (Expr,[Location])
collapseStepRuleLeft rightList node@(DerivationNode RNFix _ (HyperEdge smtExpr successors) _) = do
  let newLocation = (Location [node] rightList)
  (getFunctionExpr newLocation, [newLocation])

collapseStepRuleLeft rightList node@(DerivationNode RASym _ (HyperEdge smtExpr successors) _) = do
  let newLocation =  (Location [node] rightList)
  (getFunctionExpr newLocation , [newLocation])

collapseStepRuleLeft rightList node@(DerivationNode RNIte _ (HyperEdge smtExpr@(MkOr [e1,e2]) successors) _) = do
  let (condExpr,newLocation1) = collapseStepRuleLeft rightList (successors !! 0)
  let (trueExpr,newLocation2) = collapseStepRuleLeft rightList (successors !! 1)
  let (falseExpr,newLocation3) = collapseStepRuleLeft rightList (successors !! 2)
  let newExpr = (MkOr [ (MkAnd [condExpr,trueExpr,e1]),(MkAnd [condExpr,falseExpr,e2])])
  (newExpr, (newLocation1 ++ newLocation2 ++ newLocation3))

collapseStepRuleLeft rightList node@(DerivationNode _  _ (HyperEdge smtExpr successors) _ ) = do
 let collapseExpr = map (collapseStepRuleLeft rightList) successors
 let (expr, locations) = foldr (\(x,y) (x1,y2)-> (x:x1,y++y2)) ([],[]) collapseExpr
 let newExpr1 = (MkAnd (smtExpr:expr))
 let newLocation = Location [] rightList
 let newExpr2 = MkAnd ([(getFunctionExpr newLocation),smtExpr]++expr)
 if (length(successors) /= 0) then (newExpr1,locations)
  else if (length rightList) == 0 then (newExpr1,locations)
         else (newExpr2,[newLocation])

getRule :: Expr -> [Location] -> Location -> Rule
getRule expr bodyPredicaes headPredicate = do
 let listOfPredicatesExpr = map getFunctionExpr (filter (\x@(Location list1 list2) -> length(list1 ++ list2) > 0) bodyPredicaes)
 Rule (MkAnd (expr:listOfPredicatesExpr)) (getFunctionExpr headPredicate) 

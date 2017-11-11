module Language.Equivalence.InferRelationalTypes where
import Language.Equivalence.TypeInference
import Language.Equivalence.RelationalTypes
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Language.Equivalence.Types as T
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map


data TemporyResult = TemporyResult Int  (Map.Map (T.CoreExpr,T.CoreExpr) UnfoldPair) (Map.Map T.CoreExpr Type) CHC
  deriving (Show,Eq,Ord)

type UnfoldState a = (State TemporyResult) a

data UnfoldPair = UnfoldPair TypePoint TypePoint [T.Var] T.CoreExpr [T.Var] T.CoreExpr Int [UnfoldEdge]
  deriving (Show,Eq,Ord)

data UnfoldRule = UnfoldLeft | UnfoldRight
  deriving (Show,Eq,Ord)

data UnfoldEdge = UnfoldEdge UnfoldRule [UnfoldPair]
  deriving (Show,Eq,Ord)


constructUnfoldPair :: [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair freeVars1 freeVars2 e1 e2 = do
  (TemporyResult _ result _ _) <- get
  if Map.member (e1,e2) result then return (result Map.! (e1,e2))
    else constructNewUnfoldPair freeVars1 freeVars2 e1 e2

constructNewUnfoldPair :: [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair freeVars1 freeVars2 e1 e2 = do
  (TemporyResult number result typeEnv chc) <- get
  let contextV = constructFreeVariables freeVars1 freeVars2
  let expressionV = constructPairExpressions e1 e2 freeVars1 freeVars2
  let virtualPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number []
  edgeList <- constructUnfoldEdge virtualPair e1 e2
  let newUnfoldPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number edgeList
  put (TemporyResult (number+1) (Map.insert (e1,e2) newUnfoldPair result) typeEnv chc)
  return newUnfoldPair

constructFreeVariables :: [T.Var] -> [T.Var] ->TypePoint
constructFreeVariables = undefined

constructPairExpressions :: T.CoreExpr -> T.CoreExpr -> [T.Var] -> [T.Var] -> TypePoint
constructPairExpressions = undefined


constructUnfoldEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState [UnfoldEdge]
constructUnfoldEdge rootPair e1 e2 = do
  leftEdge  <- unfoldLeftEdge rootPair e1 e2
  rightEdge <- unfoldRightEdge rootPair e1 e2
  return (filter (\(UnfoldEdge _ list) -> if (length list) > 0 then True else False ) [leftEdge,rightEdge])

unfoldLeftEdge ::UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.EBin ob e3 e4) e2 = do
  pair1 <- constructUnfoldPair freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair freeV1 freeV2 e4 e2
  buildBinaryConstrainsLeft ob pair1 pair2 pair
  buildContextEntail pair pair1
  buildContextEntail pair pair1
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.EIf e3 e4 e5) e2 = do
  pair1 <- constructUnfoldPair freeV1 freeV2 e3 e2
  buildContextEntail pair pair1
  pair2 <- constructUnfoldPair freeV1 freeV2 e4 e2
  buildContextForTrue 1 pair1 pair2
  pair3 <- constructUnfoldPair freeV1 freeV2 e5 e2
  buildContextForFalse 1 pair1 pair3
  buildIfStConstrainsLeft pair2 pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.EMatch e3 e4 v1 v2 e5) e2 = do
  pair1 <- constructUnfoldPair freeV1 freeV2 e3 e2
  buildContextEntail pair pair1
  pair2 <- constructUnfoldPair freeV1 freeV2 e4 e2
  pair3 <- constructUnfoldPair (updateFreeList [v1,v2] freeV1) freeV2 e5 e2
  buildContextForLeft 1 pair1 pair2 
  buildContextForRight 1 v1 v2 pair1 pair3
  buildMatchConstrains pair2 pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.ECon e3 e4) e2 = do
  pair1 <- constructUnfoldPair freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair freeV1 freeV2 e4 e2
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  buildConConstrains 1 pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.EApp e3 e4) e2 = do
  pair1 <- constructUnfoldPair  freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair  freeV1 freeV2 e4 e2
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  buildArgsConstrainsLeft pair1 pair2
  buildAppConstrains pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair _ _ freeV1 _ freeV2 _ _ _) (T.ELam v e3) e2 = do 
  pair1 <- constructUnfoldPair (updateFreeList [v] freeV1) freeV2 e3 e2
  buildLamContextLeft pair pair1 v
  buildLamConstrainsLeft v pair1 pair
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge _  _ _ = return (UnfoldEdge UnfoldLeft [])

buildEntail ::Int -> Int -> Int -> Int -> TypePoint -> TypePoint -> UnfoldState ()
buildEntail indicator1 pairId1 indicator2 pairId2 t1 t2 = undefined

buildContextEntail :: UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextEntail = undefined

buildBinaryConstrainsLeft :: T.Binop -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildBinaryConstrainsLeft op (UnfoldPair _ expressionV _ _ _ _ pairId1 _) (UnfoldPair _ _ _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
  let allConstrainsTypePoint =Set.filter (\(TypePoint _ typeEdges _) -> if (length typeEdges) == 0 then True else False) (collectAllTypePoint expressionV)
  let (TypePoint types1 _ _) = expressionV
  let (TypePoint types2 _ _) = expressionV3
  let type1 = types1 !! 0
  let type2 = types2 !! 0
  mapM (buildConstrains op type1 type2 0 pairId1 pairId2 pairId3) (Set.toList allConstrainsTypePoint)
  return ()


buildConstrains :: T.Binop -> TypeWithId -> TypeWithId -> Int -> Int -> Int -> Int -> TypePoint->UnfoldState ()
buildConstrains op t1 t2  indicator pairId1 pairId2 pairId3 t@(TypePoint types _ typeId) = do
  let r1 = getPredicate t pairId1 indicator
  let r2 = getPredicate t pairId2 indicator
  let r3 = getPredicate t pairId3 indicator
  let index = [1 ..  (length types)]
  let mapIndex = tail index
  let eq1 = generateEq t t mapIndex mapIndex indicator indicator pairId1 pairId2
  let eq2 = generateEq t t mapIndex mapIndex indicator indicator pairId1 pairId3
  let var1 = Var (getVarName 1 pairId1 indicator typeId) (getSortFromType t1)
  let var2 = Var (getVarName 1 pairId2 indicator typeId) (getSortFromType t1)
  let var3 = Var (getVarName 1 pairId3 indicator typeId) (getSortFromType t2)
  let binaryConstrains = generateBinaryConstrains op (ExprVar var1) (ExprVar var2) (ExprVar var3)
  let newRule = Rule (MkAnd ([r1,r2,binaryConstrains] ++ eq1 ++ eq2)) r3
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule newRule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildContextForTrue ::Int -> UnfoldPair -> UnfoldPair  -> UnfoldState ()
buildContextForTrue leftOrRight (UnfoldPair _ expressionV _ _ _ _ pairId1 _) (UnfoldPair contextV _ _ _ _ _ pairId2 _) = do
  let (TypePoint types _ _) = expressionV
  let indexMap = foldr (\i m -> Map.insert i (i-2) m) (Map.empty) [3 .. (length types)]
  let correspondingTypePoints =Set.toList (execState (collectNewCorespondingTypePoint expressionV contextV [1,2] [] indexMap) (Set.empty))
  let constrainTypePoint = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints
  mapM (buildTrueConstrain leftOrRight pairId1 pairId2) constrainTypePoint
  return ()

buildTrueConstrain :: Int -> Int -> Int -> (TypePoint,TypePoint) -> UnfoldState ()
buildTrueConstrain leftOrRight pairId1 pairId2 (t1@(TypePoint types1 _ typePointId),t2@(TypePoint types2 _ _)) = do
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId2 0
  let eq = generateEq t1 t2 [3 .. (length types1)] [1 .. (length types2) ] 1 0 pairId1 pairId2
  let expr1 = ExprVar (Var (getVarName leftOrRight pairId1 1 typePointId) BoolSort)
  let rule = Rule (MkAnd ([r1,expr1]++eq)) r2
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

collectCorespondingTypePoint :: TypePoint -> TypePoint -> [Int] -> [Int] -> (Map.Map Int Int) -> (State (Set.Set (TypePoint,TypePoint))) ()
collectCorespondingTypePoint t1 t2 dropList1 dropList2 indexMap = do
  resultSet <- get
  if (Set.member (t1,t2) resultSet ) then return ()
    else collectNewCorespondingTypePoint t1 t2 dropList1 dropList2 indexMap

collectNewCorespondingTypePoint :: TypePoint -> TypePoint -> [Int] -> [Int] -> (Map.Map Int Int) -> (State (Set.Set (TypePoint,TypePoint))) ()
collectNewCorespondingTypePoint t1@(TypePoint _ edgeList1 _) t2@(TypePoint _ edgeList2 _) dropList1 dropList2 indexMap = do
  resultSet <- get
  put (Set.insert (t1,t2) resultSet)
  let allPairsOfEdge =concat (map (\x -> map (\y -> (x,y)) edgeList2) edgeList1)
  let validPairs = filter (\(e1,e2) -> twoEdgeListSame e1 e2 dropList1 dropList2 indexMap) allPairsOfEdge
  mapM (addCorrespondingTypePoint dropList1 dropList2 indexMap) validPairs
  return ()

addCorrespondingTypePoint :: [Int] -> [Int] -> (Map.Map Int Int)-> (TypeEdge,TypeEdge) ->(State (Set.Set (TypePoint,TypePoint))) ()
addCorrespondingTypePoint  dropList1 dropList2 indexMap ((TypeEdge _ _ list1), (TypeEdge _ _ list2)) = do
  let pairTypePoint = zip list1 list2
  mapM (\(t1,t2)-> collectCorespondingTypePoint t1 t2 dropList1 dropList2 indexMap) pairTypePoint
  return ()


twoEdgeListSame :: TypeEdge -> TypeEdge -> [Int] -> [Int] -> (Map.Map Int Int) -> Bool
twoEdgeListSame  (TypeEdge _ index1 _) (TypeEdge _ index2 _) dropIndex1 dropIndex2 indexMap = do
  let dropSet1 = Set.fromList dropIndex1
  let dropSet2 = Set.fromList dropIndex2
  let drop1 = filter (\x -> Set.notMember x dropSet1) index1
  let drop2 = filter (\x -> Set.notMember x dropSet2) index2
  let mapIndex = map (\x -> indexMap Map.! x) drop1
  null ((Set.fromList mapIndex) Set.\\ (Set.fromList drop2))


buildContextForFalse ::Int -> UnfoldPair -> UnfoldPair  -> UnfoldState ()
buildContextForFalse leftOrRight (UnfoldPair _ expressionV _ _ _ _ pairId1 _) (UnfoldPair contextV _ _ _ _ _ pairId2 _) = do
  let (TypePoint types _ _) = expressionV
  let indexMap = foldr (\i m -> Map.insert i (i-2) m) (Map.empty) [3 .. (length types)]
  let correspondingTypePoints =Set.toList (execState (collectNewCorespondingTypePoint expressionV contextV [1,2] [] indexMap) (Set.empty))
  let constrainTypePoint = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints
  mapM (buildFalseConstrain leftOrRight pairId1 pairId2) constrainTypePoint
  return ()

buildFalseConstrain :: Int -> Int -> Int -> (TypePoint,TypePoint) -> UnfoldState ()
buildFalseConstrain leftOrRight pairId1 pairId2 (t1@(TypePoint types1 _ typePointId),t2@(TypePoint types2 _ _)) = do
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId2 0
  let eq = generateEq t1 t2 [3 .. (length types1)] [1 .. (length types2) ] 1 0 pairId1 pairId2
  let expr1 =MkNot (ExprVar (Var (getVarName leftOrRight pairId1 1 typePointId) BoolSort))
  let rule = Rule (MkAnd ([r1,expr1]++eq)) r2
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

-- just handle true and false branch has same type
buildIfStConstrainsLeft :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildIfStConstrainsLeft (UnfoldPair _ expressionV1 _ _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
 buildEntail 1 pairId1 1 pairId3 expressionV1 expressionV2
 buildEntail 1 pairId2 1 pairId3 expressionV1 expressionV3
 return ()
  

-- consider fix type later(it has to be handled)
buildContextForLeft ::Int -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextForLeft leftOrRight (UnfoldPair _ expressionV _ _ _ _ pairId1 _) (UnfoldPair contextV _ _ _ _ _ pairId2 _) = do
  let (TypePoint types edges _) = expressionV
  let (TypeEdge TypePlus _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
  let leftPlus = typePoints !! 0
  let indexMap = foldr (\i m -> Map.insert i (i-2) m) (Map.empty) [3 .. (length types)]
  let correspondingTypePoints =Set.toList (execState (collectNewCorespondingTypePoint leftPlus contextV [1,2] [] indexMap) (Set.empty))
  let constrainTypePoint = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints
  mapM (buildProjectEntailConstrain pairId1 pairId2) constrainTypePoint
  return ()

buildProjectEntailConstrain :: Int -> Int -> (TypePoint,TypePoint) -> UnfoldState ()
buildProjectEntailConstrain pairId1 pairId2 (t1@(TypePoint types1 _ _),t2@(TypePoint types2 _ _)) = do
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId2 0
  let eq = generateEq t1 t2 [3 .. (length types1)] [1 .. (length types2) ] 1 0 pairId1 pairId2
  let rule = Rule (MkAnd (r1:eq)) r2
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildContextForRight :: Int ->T.Var -> T.Var -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextForRight leftOrRight v1 v2 (UnfoldPair _ expressionV oldFreeV1 _ oldFreeV2 _ pairId1 _) pair2= do
  let (TypePoint _ edges _) = expressionV
  let (TypeEdge TypePlus _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
  let (TypePoint _ edges2 _) = typePoints !! 0
  let (TypeEdge TypePlus _ typePoints2) = (filter (\(TypeEdge _ index _) -> if index == ([leftOrRight]) then True else False ) edges2) !! 0
  let point1 = typePoints2 !! 0
  let point2 = typePoints2 !! 1
  if leftOrRight == 1 then buildMatchContextLeft v1 v2 oldFreeV1 point1 point2 pairId1 pair2
    else buildMatchContextRight v1 v2 oldFreeV2 point1 point2 pairId1 pair2

buildMatchContextLeft ::T.Var -> T.Var ->[T.Var]-> TypePoint -> TypePoint -> Int -> UnfoldPair -> UnfoldState ()
buildMatchContextLeft oldV1 oldV2 oldFreeV1 v1@(TypePoint types1 _ _) v2 pairId1 (UnfoldPair contextV _ _ _ _ _ pairId2 _) = do
  let oldFreeWithIndex = zip oldFreeV1 [3 ..]
  let indexWithOutV1V2 = filter (\(v,_)-> if (v == oldV1) || (v == oldV2) then False else True) oldFreeWithIndex
  let v1v2Index =map (\(_,n) -> n) (filter (\(v,_)-> if (v == oldV1) || (v == oldV2) then True else False) oldFreeWithIndex)
  let listForFree1 = map (\(_,n) -> n) indexWithOutV1V2
  let list1 = listForFree1++[((length oldFreeV1)+1) .. (length types1)]
  let list2 = [3 .. (length types1)]
  let indexMap = Map.fromList (zip list1 list2)
  let indexMap1 = Map.insert 1 1 indexMap
  let correspondingTypePoints1 =Set.toList (execState (collectNewCorespondingTypePoint v1 contextV ([2]++v1v2Index)  [2] indexMap1) (Set.empty))
  let constrainTypePoint1 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints1
  let indexMap2 = Map.insert 1 2 indexMap
  let correspondingTypePoints2 =Set.toList (execState (collectNewCorespondingTypePoint v2 contextV ([2]++v1v2Index) [1] indexMap2) (Set.empty))
  let constrainTypePoint2 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints2
  let allPossiblePairs =concat (map (\x -> map (\y -> (x,y)) constrainTypePoint1 ) constrainTypePoint2)
  let allSamePair = filter (\((_,a1),(_,a2)) -> if a1 == a2 then True else False ) allPossiblePairs
  mapM (buildContextRuleLeft list1 list2 pairId1 pairId2) allSamePair
  return ()

buildContextRuleLeft :: [Int] ->[Int] -> Int -> Int -> ((TypePoint,TypePoint),(TypePoint, TypePoint)) -> UnfoldState()
buildContextRuleLeft list1 list2 pairId1 pairId2 ((t1,t2),(t3,_)) = do
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId1 1
  let r3 = getPredicate t3 pairId2 0
  let eq1 = generateEq t1 t3 (1:list1) (1:list2) 1 0 pairId1 pairId2
  let eq2 = generateEq t2 t3 (1:list1) (2:list2) 1 0 pairId1 pairId2
  let rule = Rule (MkAnd ([r1,r2]++eq1++eq2)) r3
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildMatchContextRight :: T.Var -> T.Var ->[T.Var]-> TypePoint -> TypePoint -> Int -> UnfoldPair -> UnfoldState ()
buildMatchContextRight oldV1 oldV2 oldFreeV2 v1@(TypePoint types1 _ _) v2 pairId1 (UnfoldPair contextV _ freeV1 _ _ _ pairId2 _) = do
  let length1 = length freeV1
  let oldFreeWithIndex = zip oldFreeV2 [(length1+1) ..]
  let indexWithOutV1V2 = filter (\(v,_)-> if (v == oldV1) || (v == oldV2) then False else True) oldFreeWithIndex
  let v1v2Index =map (\(_,n) -> n) (filter (\(v,_)-> if (v == oldV1) || (v == oldV2) then True else False) oldFreeWithIndex)
  let listForFree2 = map (\(_,n) -> n) indexWithOutV1V2
  let list1 = [3 .. length1] ++ listForFree2
  let list2 = [1 .. length1] ++  [ (length1+3) .. (length types1) ] 
  let indexMap = Map.fromList (zip [3 .. (length types1)] list2)
  let indexMap1 = Map.insert 1 (length1+1) indexMap
  let correspondingTypePoints1 =Set.toList (execState (collectNewCorespondingTypePoint v1 contextV ([2]++v1v2Index) [length1+1] indexMap1) (Set.empty))
  let constrainTypePoint1 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints1
  let indexMap2 = Map.insert 1 (length1+2) indexMap
  let correspondingTypePoints2 =Set.toList (execState (collectNewCorespondingTypePoint v2 contextV ([2]++v1v2Index) [length1+2] indexMap2) (Set.empty))
  let constrainTypePoint2 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints2
  let allPossiblePairs =concat (map (\x -> map (\y -> (x,y)) constrainTypePoint1 ) constrainTypePoint2 )
  let allSamePair = filter (\((_,a1),(_,a2)) -> if a1 == a2 then True else False ) allPossiblePairs
  mapM (buildContextRuleRight list1 length1 pairId1 pairId2) allSamePair
  return ()

buildContextRuleRight :: [Int] -> Int -> Int -> Int-> ((TypePoint,TypePoint),(TypePoint, TypePoint)) -> UnfoldState()
buildContextRuleRight list1 length1 pairId1 pairId2 ((t1,t2),(t3,_)) = do
  let (TypePoint types _ _) = t1
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId1 1
  let r3 = getPredicate t3 pairId2 0
  let eq1 = generateEq t1 t3 (1:list1) ([1 .. length1] ++[length1+1] ++ [ (length1+3) .. (length types) ]) 1 0 pairId1 pairId2
  let eq2 = generateEq t2 t3 (1:list1) ([1 .. length1] ++[length1+2] ++ [ (length1+3) .. (length types) ]) 1 0 pairId1 pairId2
  let rule = Rule (MkAnd ([r1,r2]++eq1++eq2)) r3
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildMatchConstrains :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildMatchConstrains (UnfoldPair _ expressionV1 _ _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
 buildEntail 1 pairId1 1 pairId3 expressionV1 expressionV2
 buildEntail 1 pairId2 1 pairId3 expressionV1 expressionV3
 return ()

buildConConstrains ::Int -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildConConstrains leftOrRight (UnfoldPair _ expressionV1 _ _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
  let (TypePoint _ edges _) = expressionV3
  let (TypeEdge TypeProduct _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
  let leftProduct = typePoints !! 0
  let rightProduct = typePoints !! 1
  buildEntail 1 pairId1 1 pairId3 expressionV1 leftProduct
  buildEntail 1 pairId2 1 pairId3 expressionV2 rightProduct
  return ()

-- it only work for having one arg
buildArgsConstrainsLeft :: Int -> UnfoldPair -> UnfoldPair  -> UnfoldState ()
buildArgsConstrainsLeft leftOrRight (UnfoldPair _ expressionV1 _ _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) = do
  let (TypePoint types edges _) = expressionV1
  let (TypeEdge TypeArr _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
  let leftArr = typePoints !! 0
  buildEntail 1 pairId1 1 pairId2 expressionV2 leftArr
  return ()

buildAppConstrainsLeft :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildAppConstrainsLeft (UnfoldPair _ expressionV1 _ _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
  let (TypePoint types edges _) = expressionV1
  let (TypeEdge TypeArr _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([1]) then True else False ) edges) !! 0
  let rightArr = typePoints !! 1
  let indexMap =Map.fromList ([(2,2),(3,1)] ++ (zip [4..(length types)] [4..(length types)]))
  let correspondingTypePoints1 =Set.toList (execState (collectNewCorespondingTypePoint rightArr expressionV1 [1] [] indexMap) (Set.empty))
  let constrainTypePoint1 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints1
  let indexMap2 = Map.fromList ([(1,1),(2,2)] ++ (zip [4..(length types)] [4..(length types)]))
  let correspondingTypePoints2 =Set.toList (execState (collectNewCorespondingTypePoint rightArr expressionV3 [3] [] indexMap2) (Set.empty))
  let constrainTypePoint2 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints2
  let allPossiblePairs =concat (map (\x -> map (\y -> (x,y)) constrainTypePoint2) constrainTypePoint1)
  let allValidPair = filter (\((a1,_),(a2,_))-> if a1 == a2 then True else False) allPossiblePairs
  mapM (buildLeftAppRules pairId1 pairId2 pairId3) allValidPair

buildLeftAppRules :: Int -> Int -> Int-> ((TypePoint,TypePoint),(TypePoint, TypePoint)) -> UnfoldState()
buildLeftAppRules pairId1 pairId2 pairid3 ((t1,t2),(_,t3)) = do
  let (TypePoint types _ _) = t1
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId2 1
  let r3 = getPredicate t3 pairId3 1
  let eq1 = generateEq t1 t3 [2 .. (length types)] ([2,1]++[4..(length types)]) 1 1 pairId1 pairId2
  let eq2 = generateEq t2 t3 ([1,2]++[4..(length types)]) ([1,2]++[4..(length types)]) 1 1 pairId1 pairId3
  let rule = Rule (MkAnd ([r1,r2]++eq1++eq2)) r3
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildAppConstrainsRight :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildAppConstrainsRight (UnfoldPair _ expressionV1 freeV1 _ _ _ pairId1 _) (UnfoldPair _ expressionV2 _ _ _ _ pairId2 _) (UnfoldPair _ expressionV3 _ _ _ _ pairId3 _) = do
  let (TypePoint types edges _) = expressionV1
  let (TypeEdge TypeArr _ typePoints) = (filter (\(TypeEdge _ index _) -> if index == ([1]) then True else False ) edges) !! 0
  let rightArr = typePoints !! 1
  let indexMap =Map.fromList (zip [1 .. (length types) [1 ..]])
  let indexMap1 =Map.insert (3 + (length freeV1) 2 (Map.delete (3 + (length freeV1)) (Map.delete 2 indexMap)
  let correspondingTypePoints1 =Set.toList (execState (collectNewCorespondingTypePoint rightArr expressionV1 [2] [] indexMap1) (Set.empty))
  let constrainTypePoint1 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints1
  let indexMap2 = Map.delete (3 + (length freeV1)) indexMap
  let correspondingTypePoints2 =Set.toList (execState (collectNewCorespondingTypePoint rightArr expressionV3 [(3 + (length freeV1)] [] indexMap2) (Set.empty))
  let constrainTypePoint2 = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints2
  let allPossiblePairs =concat (map (\x -> map (\y -> (x,y)) constrainTypePoint2) constrainTypePoint1)
  let allValidPair = filter (\((a1,_),(a2,_))-> if a1 == a2 then True else False) allPossiblePairs
  mapM (buildRightAppRules pairId1 pairId2 pairId3) allValidPair

buildRightAppRules ::Int -> Int -> Int -> Int-> ((TypePoint,TypePoint),(TypePoint, TypePoint)) -> UnfoldState()
buildRightAppRules length1 pairId1 pairId2 pairid3 ((t1,t2),(_,t3)) = do
  let (TypePoint types _ _) = t1
  let r1 = getPredicate t1 pairId1 1
  let r2 = getPredicate t2 pairId2 1
  let r3 = getPredicate t3 pairId3 1
  -- get it back later
  let eq1 = generateEq t1 t3 (1:[3 .. (length types)]) (1:[3 .. (2+length1)])++[2]++[ (3+length1) .. (length types)] 1 1 pairId1 pairId2
  let eq2 = generateEq t2 t3 ([1,2]++[4..(length types)]) ([1,2]++[4..(length types)]) 1 1 pairId1 pairId3
  let rule = Rule (MkAnd ([r1,r2]++eq1++eq2)) r3
  (TemporyResult number result typeEnv chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv newChc)
  return ()

buildLamContextLeft :: UnfoldPair -> UnfoldPair -> T.Var -> UnfoldState ()
buildLamContextLeft = undefined

buildLamConstrains :: Int -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildLamConstrains leftOrRight (UnfoldPair _ expressionV1 _ _ _ _ pairId1) pair2 = do


unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge = undefined

updateFreeList :: [T.Var] -> [T.Var] -> [T.Var]
updateFreeList newFreeVs oldFree = do
  let filterOutList = filter (\x -> if Set.member x (Set.fromList newFreeVs) then False else True) oldFree
  newFreeVs ++ oldFree


data CHCSystem = CHCSystem (Set.Set Int) CHC
  deriving (Show,Eq,Ord)

type CHCState a = (State CHCSystem) a

setEqualVar :: Var -> Var -> Expr 
setEqualVar var1 var2 = MkEq (ExprVar var1) (ExprVar var2)
  

generateEq :: TypePoint -> TypePoint -> [Int] -> [Int] -> Int -> Int -> Int -> Int -> [Expr]
generateEq (TypePoint types1 _ typePId1) (TypePoint types2 _ typePId2) indexList1 indexList2 indicator1 indicator2 pairId1 pairId2 = do
  let typeWithId1 = zip types1 [1 .. ]
  let typeInIndex1 = filter (\(_,n) -> if elem n indexList1 then True else False) typeWithId1
  let typeEq1 = filter (\(t,_) -> isPrimeType t) typeInIndex1
  let typeWithId2 = zip types2 [1 .. ]
  let typeInIndex2 = filter (\(_,n) -> if elem n indexList2 then True else False) typeWithId2
  let typeEq2 = filter (\(t,_) -> isPrimeType t) typeInIndex2  
  let sortList1 = map (\(t,n)-> ((getSortFromType t),n) ) typeEq1
  let varList1 = map(\(s,n) -> Var (getVarName n pairId1 indicator1 typePId1) s) sortList1
  let sortList2 = map (\(t,n)-> ((getSortFromType t),n) ) typeEq2
  let varList2 = map(\(s,n) -> Var (getVarName n pairId2 indicator2 typePId2) s) sortList2
  zipWith setEqualVar varList1 varList2

getPredicate ::  TypePoint -> Int -> Int -> Expr
getPredicate  (TypePoint types _ typePointId) pairId indicator = do
  let typeWithId = zip types [1 .. ]
  let typeWithRightSort = filter (\(t,_) -> isPrimeType t) typeWithId
  let sortList = map (\(t,n)-> ((getSortFromType t),n)) typeWithRightSort
  let varList = map(\(s,n) -> Var (getVarName n pairId indicator typePointId)  s) sortList
  ApplyFunction (Function ("R"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)) (map (\(s,_)->s) sortList)) (map (\x -> ParameterVar x) varList)

generateBinaryConstrains :: T.Binop -> Expr -> Expr -> Expr -> Expr
generateBinaryConstrains T.Plus expr1 expr2 expr3 = MkEq expr3 (MkAnd [expr1,expr2])
generateBinaryConstrains T.Minus expr1 expr2 expr3 = MkEq expr3 (MkSub [expr1,expr2])
generateBinaryConstrains T.Mul expr1 expr2 expr3 = MkEq expr3 (MkMul [expr1,expr2])
generateBinaryConstrains T.Div expr1 expr2 expr3 = MkEq expr3 (MkDiv_1 expr1 expr2)
generateBinaryConstrains T.Eq expr1 expr2 expr3 = MkEq expr3 (MkEq expr1 expr2)
generateBinaryConstrains T.Ne expr1 expr2 expr3 = MkEq expr3 (MkNot (MkEq expr1 expr2))
generateBinaryConstrains T.Lt expr1 expr2 expr3 = MkEq expr3 (MkLt expr1 expr2)
generateBinaryConstrains T.Le expr1 expr2 expr3 = MkEq expr3 (MkLe expr1 expr2)
generateBinaryConstrains T.And expr1 expr2 expr3 = MkEq expr3 (MkAnd [expr1 , expr2])
generateBinaryConstrains T.Or expr1 expr2 expr3 = MkEq expr3 (MkOr [expr1 , expr2])
generateBinaryConstrains T.Cons _ _ _= error "generate binary constrains does not handle Cons"

getVarName :: Int -> Int -> Int -> Int -> String
getVarName  index pairId  indicator typePointId  = "x@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)++"!"++(show index)


getSortFromType :: TypeWithId -> Sort
getSortFromType (TIntId _)  = IntegerSort
getSortFromType (TBoolId _) = BoolSort
getSortFromType _ = error "get sort calles non primitive type"

isPrimeType :: TypeWithId -> Bool
isPrimeType (TIntId _) = True
isPrimeType (TBoolId _) = True
isPrimeType _ = False







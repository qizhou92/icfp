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


constructUnfoldPair :: TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair contextV freeVars1 freeVars2 e1 e2 = do
  (TemporyResult _ result _ _) <- get
  if Map.member (e1,e2) result then return (result Map.! (e1,e2))
    else constructNewUnfoldPair contextV freeVars1 freeVars2 e1 e2

constructNewUnfoldPair ::TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair contextV freeVars1 freeVars2 e1 e2 = do
  (TemporyResult number result typeEnv chc) <- get
  expressionV <- constructPairExpressions e1 e2 freeVars1 freeVars2
  let virtualPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number []
  edgeList <- constructUnfoldEdge virtualPair e1 e2
  let newUnfoldPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number edgeList
  put (TemporyResult (number+1) (Map.insert (e1,e2) newUnfoldPair result) typeEnv chc)
  return newUnfoldPair

constructFreeVariables :: [T.Var] -> [T.Var] ->UnfoldState TypePoint
constructFreeVariables = undefined

constructPairExpressions :: T.CoreExpr -> T.CoreExpr -> [T.Var] -> [T.Var] -> UnfoldState TypePoint
constructPairExpressions = undefined


constructUnfoldEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState [UnfoldEdge]
constructUnfoldEdge rootPair e1 e2 = do
  leftEdge  <- unfoldLeftEdge rootPair e1 e2
  rightEdge <- unfoldRightEdge rootPair e1 e2
  return (filter (\(UnfoldEdge _ list) -> if (length list) > 0 then True else False ) [leftEdge,rightEdge])

unfoldLeftEdge ::UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldLeftEdge pair@(UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) (T.EBin ob e3 e4) e2 = do
  pair1 <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair contextV freeV1 freeV2 e4 e2
  buildBinaryConstrainsLeft ob pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) (T.EIf e3 e4 e5) e2 = do
  pair1@(UnfoldPair _ expressionV1 _ _ _ _ id1 _) <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  (TemporyResult id2 _ _ _) <- get
  contextForTrue  <- buildContextForTrue 1 id1 id2 expressionV1 freeV1 freeV2
  pair2 <- constructUnfoldPair contextForTrue freeV1 freeV2 e4 e2
  (TemporyResult id3 _ _ _) <- get
  contextForFalse <- buildContextForFalse 1 id1 id3 expressionV1 freeV1 freeV2
  pair3 <- constructUnfoldPair contextForFalse freeV1 freeV2 e5 e2
  buildIfStConstrainsLeft pair2 pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge (UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) e1@(T.EMatch e3 e4 v1 v2 e5) e2 = do
  pair1@(UnfoldPair _ expressionV1 _ _ _ _ id1 _) <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  contextForLeft <- buildContextForLeft expressionV1 freeV1 freeV2 e1 e2 id1
  contextForRight <- buildContextForRight expressionV1 v1 v2 freeV1 freeV2 e1 e2 id1
  pair2 <- constructUnfoldPair contextForLeft freeV1 freeV2 e4 e2
  pair3 <- constructUnfoldPair contextForRight (updateFreeList [v1,v2] freeV1) freeV2 e5 e2
  buildMatchConstrainsLeft pair2 pair3 pair1
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair@(UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) (T.ECon e3 e4) e2 = do
  pair1 <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair contextV freeV1 freeV2 e4 e2
  buildConConstrainsLeft pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) (T.EApp e3 e4) e2 = do
  pair1 <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair contextV freeV1 freeV2 e4 e2
  buildArgsConstrainsLeft pair1 pair2
  buildAppConstrains pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair contextV _ freeV1 _ freeV2 _ _ _) (T.ELam v e3) e2 = do
  newContext <- buildLamContextLeft contextV v freeV1 freeV2 
  pair1 <- constructUnfoldPair newContext (updateFreeList [v] freeV1) freeV2 e3 e2
  buildLamConstrainsLeft v pair1 pair
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge _  _ _ = return (UnfoldEdge UnfoldLeft [])

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

buildContextForTrue ::Int -> Int -> Int -> TypePoint -> [T.Var] -> [T.Var]  -> UnfoldState TypePoint
buildContextForTrue leftOrRight pairId1 pairId2 oldContext@(TypePoint types _ _) freeV1 freeV2 = do
  freeTypes1 <- mapM getType freeV1
  freeTypes2 <- mapM getType freeV2
  let newContext = constructVersionSpace [] [] freeTypes1 freeTypes2
  let indexMap = foldr (\i m -> Map.insert i (i-2) m) (Map.empty) [3 .. (length types)]
  let correspondingTypePoints =Set.toList (execState (collectNewCorespondingTypePoint oldContext newContext [1,2] [] indexMap) (Set.empty))
  let constrainTypePoint = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints
  mapM (buildTrueConstrain leftOrRight pairId1 pairId2) constrainTypePoint
  return newContext

buildTrueConstrain :: Int -> Int -> Int -> (TypePoint,TypePoint) -> UnfoldState ()
buildTrueConstrain = undefined

getType :: T.Var -> UnfoldState TypeWithId
getType = undefined

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


 
buildContextForFalse ::Int -> Int -> Int -> TypePoint -> [T.Var] -> [T.Var]  -> UnfoldState TypePoint
buildContextForFalse leftOrRight pairId1 pairId2 oldContext@(TypePoint types _ _) freeV1 freeV2 = do
  freeTypes1 <- mapM getType freeV1
  freeTypes2 <- mapM getType freeV2
  let newContext = constructVersionSpace [] [] freeTypes1 freeTypes2
  let indexMap = foldr (\i m -> Map.insert i (i-2) m) (Map.empty) [3 .. (length types)]
  let correspondingTypePoints =Set.toList (execState (collectNewCorespondingTypePoint oldContext newContext [1,2] [] indexMap) (Set.empty))
  let constrainTypePoint = filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) ->if (length (edgeList1++edgeList2) == 0) then True else False) correspondingTypePoints
  mapM (buildFalseConstrain leftOrRight pairId1 pairId2) constrainTypePoint
  return newContext

buildFalseConstrain :: Int -> Int -> Int -> (TypePoint,TypePoint) -> UnfoldState ()
buildFalseConstrain = undefined

buildIfStConstrainsLeft :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildIfStConstrainsLeft = undefined

buildContextForLeft :: TypePoint -> [T.Var] -> [T.Var] ->T.CoreExpr -> T.CoreExpr -> Int -> UnfoldState TypePoint
buildContextForLeft = undefined

buildContextForRight :: TypePoint -> T.Var -> T.Var -> [T.Var] -> [T.Var] ->T.CoreExpr -> T.CoreExpr -> Int -> UnfoldState TypePoint
buildContextForRight = undefined

buildMatchConstrainsLeft :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildMatchConstrainsLeft = undefined

buildConConstrainsLeft :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildConConstrainsLeft = undefined

buildArgsConstrainsLeft :: UnfoldPair -> UnfoldPair  -> UnfoldState ()
buildArgsConstrainsLeft = undefined

buildAppConstrains :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildAppConstrains = undefined

buildLamContextLeft :: TypePoint -> T.Var -> [T.Var] -> [T.Var] -> UnfoldState TypePoint
buildLamContextLeft = undefined

buildLamConstrainsLeft :: T.Var -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildLamConstrainsLeft = undefined

unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge = undefined

updateFreeList :: [T.Var] -> [T.Var] -> [T.Var]
updateFreeList = undefined


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







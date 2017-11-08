module Language.Equivalence.InferRelationalTypes where
import Language.Equivalence.TypeInference
import Language.Equivalence.RelationalTypes
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Language.Equivalence.Types as T
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map


data TemporyResult = TemporyResult Int  (Map.Map (T.CoreExpr,T.CoreExpr) UnfoldPair) (Map.Map T.CoreExpr Type)
  deriving (Show,Eq,Ord)

type UnfoldState a = (State TemporyResult) a

data UnfoldPair = UnfoldPair TypePoint TypePoint [T.Var] T.CoreExpr [T.Var] T.CoreExpr Int [UnfoldEdge]
  deriving (Show,Eq,Ord)

data UnfoldRule = UnfoldLeft | UnfoldRight
  deriving (Show,Eq,Ord)

data UnfoldEdge = UnfoldEdge UnfoldRule [UnfoldPair]
  deriving (Show,Eq,Ord)


constructUnfoldPair ::TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair contextV freeVars1 freeVars2 e1 e2 = do
  (TemporyResult _ result _) <- get
  if Map.member (e1,e2) result then return (result Map.! (e1,e2))
    else constructNewUnfoldPair contextV freeVars1 freeVars2 e1 e2

constructNewUnfoldPair ::TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair contextV freeVars1 freeVars2 e1 e2 = do
  (TemporyResult number result typeEnv) <- get
  expressionV <- constructPairExpressions e1 e2 freeVars1 freeVars2
  let virtualPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number []
  edgeList <- constructUnfoldEdge virtualPair e1 e2
  let newUnfoldPair = UnfoldPair contextV expressionV freeVars1 e1 freeVars2 e2 number edgeList
  put (TemporyResult (number+1) (Map.insert (e1,e2) newUnfoldPair result) typeEnv)
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

unfoldLeftEdge pair@(UnfoldPair contextV expressionV freeV1 _ freeV2 _ id0 _) e1@(T.EIf e3 e4 e5) e2 = do
  pair1@(UnfoldPair _ expressionV1 _ _ _ _ id1 _) <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  contextForTrue  <- buildContextForTrue expressionV1 freeV1 freeV2 e2 id1
  contextForFalse <- buildContextForFalse expressionV1 freeV1 freeV2 e2 id1  
  pair2 <- constructUnfoldPair contextForTrue freeV1 freeV2 e4 e2
  pair3 <- constructUnfoldPair contextForFalse freeV1 freeV2 e5 e2
  buildIfStConstrainsLeft pair2 pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair@(UnfoldPair contextV expressionV freeV1 _ freeV2 _ id0 _) e1@(T.EMatch e3 e4 v1 v2 e5) e2 = do
  pair1@(UnfoldPair _ expressionV1 _ _ _ _ id1 _) <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  contextForLeft <- buildContextForLeft expressionV1 freeV1 freeV2 e1 e2 id1
  contextForRight <- buildContextForRight expressionV1 v1 v2 freeV1 freeV2 e1 e2 id1
  pair2 <- constructUnfoldPair contextForLeft freeV1 freeV2 e4 e2
  pair3 <- constructUnfoldPair contextForRight (updateFreeList [v1,v2] freeV1) freeV2 e5 e2
  buildMatchConstrainsLeft pair2 pair3 pair1
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair@(UnfoldPair contextV expressionV freeV1 _ freeV2 _ id0 _) e1@(T.ECon e3 e4) e2 = do
  pair1 <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  pair2 <- constructUnfoldPair contextV freeV1 freeV2 e4 e2
  buildConConstrainsLeft pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair contextV expressionV freeV1 _ freeV2 _ id0 _) e1@(T.EApp e3 e4) e2 = do
  pair1@(UnfoldPair _ expressionV1 _ _ _ _ id1 _) <- constructUnfoldPair contextV freeV1 freeV2 e3 e2
  pair2@(UnfoldPair _ expressionV2 _ _ _ _ id2 _) <- constructUnfoldPair contextV freeV1 freeV2 e4 e2
  buildArgsConstrainsLeft pair1 pair2
  buildAppConstrains pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair@(UnfoldPair contextV expressionV freeV1 _ freeV2 _ id0 _) e1@(T.ELam v e3) e2 = do
  newContext <- buildLamContextLeft contextV v freeV1 freeV2 
  pair1 <- constructUnfoldPair newContext (updateFreeList [v] freeV1) freeV2 e3 e2
  buildLamConstrainsLeft v pair1 pair
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge _  e1 e2 = return (UnfoldEdge UnfoldLeft [])

buildBinaryConstrainsLeft :: T.Binop -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildBinaryConstrainsLeft = undefined

buildContextForTrue :: TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> Int -> UnfoldState TypePoint
buildContextForTrue = undefined

buildContextForFalse :: TypePoint -> [T.Var] -> [T.Var] -> T.CoreExpr -> Int -> UnfoldState TypePoint
buildContextForFalse = undefined

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


generateConstrains :: TypePoint -> TypePoint -> CHCState ()
generateConstrains t1@(TypePoint typeList1 _ _) t2 = do
  let listWithVar = filter (isTypeVar) typeList1
  if (length typeList1) == 0 then (generateRule t1 t2)
    else return ()

generateRule :: TypePoint -> TypePoint -> CHCState ()
generateRule = undefined

getSortFromTypes :: [Type] -> [Sort]
getSortFromTypes [] = []
getSortFromTypes (TInt :xs) = IntegerSort : (getSortFromTypes xs)
getSortFromTypes (TBool :xs) = BoolSort : (getSortFromTypes xs)
getSortFromTypes (x:xs) = getSortFromTypes xs

subTypeCheck :: TypePoint -> TypePoint -> CHCState ()
subTypeCheck t1@(TypePoint typeList1 typeEdges1 id1) t2@(TypePoint typeList2 typeEdges2 id2) = do
  if length(typeEdges1) == 0 then (generateConstrains t1 t2)
    else do
          zipWithM subTypeCheckWithSameType typeEdges1 typeEdges2
          return ()

subTypeCheckWithSameType :: TypeEdge -> TypeEdge -> CHCState ()
subTypeCheckWithSameType edge1@(TypeEdge TypeArr _ pointList1) edge2@(TypeEdge TypeArr _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  --- convariant check
  subTypeCheck subPoint2_0 subPoint1_0
  subTypeCheck subPoint1_1 subPoint2_1

subTypeCheckWithSameType edge1@(TypeEdge TypePlus _ pointList1) edge2@(TypeEdge TypePlus _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  subTypeCheck subPoint1_0 subPoint2_0
  subTypeCheck subPoint1_1 subPoint2_1

subTypeCheckWithSameType edge1@(TypeEdge TypeProduct _ pointList1) edge2@(TypeEdge TypeProduct _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  subTypeCheck subPoint1_0 subPoint2_0
  subTypeCheck subPoint1_1 subPoint2_1

subTypeCheckWithSameType edge1@(TypeEdge TypeFix _ pointList1) edge2@(TypeEdge TypeFix _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint2_0 = pointList2 !! 0
  subTypeCheck subPoint1_0 subPoint2_0







module Language.Equivalence.InfereRelationalTypes where
import Language.Equivalence.TypeInference
import Language.Equivalence.RelationalTypes
import qualified Language.Equivalence.Types as CoreExpr
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

data TemporyResult = TemporyResult Int  (Map.Map (CoreExpr.CoreExpr,CoreExpr.CoreExpr) UnfoldPair) (Map.Map CoreExpr.CoreExpr Type)
  deriving (Show,Eq,Ord)

type UnfoldState a = (State TemporyResult) a

data UnfoldPair = UnfoldPair TypePoint TypePoint CoreExpr.CoreExpr CoreExpr.CoreExpr Int [UnfoldEdge]
  deriving (Show,Eq,Ord)

data UnfoldRule = UnfoldLeft | UnfoldRight | UnfoldBoth
  deriving (Show,Eq,Ord)

data UnfoldEdge = UnfoldEdge UnfoldRule [UnfoldPair]
  deriving (Show,Eq,Ord)

constructUnfoldPair :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair c1 c2 = do
  (TemporyResult number result _) <- get
  if Map.member (c1,c2) result then return (result Map.! (c1,c2))
    else constructNewUnfoldPair c1 c2

constructNewUnfoldPair :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair c1 c2 = do
  (TemporyResult number result typeEnv) <- get
  freeVariables <- constructFreeVariables c1 c2
  pairExpressions <- constructPairExpressions c1 c2
  edgeList <- constructUnfoldEdge c1 c2
  let newUnfoldPair = UnfoldPair freeVariables pairExpressions c1 c2 number edgeList
  put (TemporyResult (number+1) (Map.insert (c1,c2) newUnfoldPair result) typeEnv)
  return newUnfoldPair

constructFreeVariables :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState TypePoint
constructFreeVariables c1 c2 = do
  (TemporyResult _ _ typeEnv) <- get
  let freeVariables =Set.toList (Set.union (CoreExpr.freeVars c1) (CoreExpr.freeVars c2))
  let types = map (\x -> typeEnv Map.! (CoreExpr.EVar x) ) freeVariables
  return (constructRelationalDag types)

constructPairExpressions :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr ->UnfoldState TypePoint
constructPairExpressions c1 c2 = do
   (TemporyResult _ _ typeEnv) <- get
   let t1 = typeEnv Map.! c1
   let t2 = typeEnv Map.! c2
   return (constructRelationalDag [t1,t2])


constructUnfoldEdge :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState [UnfoldEdge]
constructUnfoldEdge c1 c2 = do
  leftEdge <- unfoldLeftEdge c1 c2
  rightEdge <- unfoldRightEdge c1 c2
  bothEdge <- unfoldBothEdge c1 c2
  return (filter (\(UnfoldEdge _ list) -> if (length list) > 0 then True else False ) [leftEdge,rightEdge,bothEdge])

unfoldLeftEdge :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState UnfoldEdge
unfoldLeftEdge c1@(CoreExpr.EBin _ e1 e2) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge c1@(CoreExpr.EIf e1 e2 e3) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  pair3 <- constructUnfoldPair e3 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge c1@(CoreExpr.EMatch _ e1 e2 e3) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  pair3 <- constructUnfoldPair e3 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge c1@(CoreExpr.EBind _  _ e1 e2) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge c1@(CoreExpr.EApp e1 e2) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge c1@(CoreExpr.ELam _ e1) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge c1 c2 = return (UnfoldEdge UnfoldLeft [])

unfoldRightEdge :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge c1 c2@(CoreExpr.EBin _ e1 e2) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  return (UnfoldEdge UnfoldRight [pair1,pair2])

unfoldRightEdge c1 c2@(CoreExpr.EIf e1 e2 e3) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  pair3 <- constructUnfoldPair c1 e3
  return (UnfoldEdge UnfoldRight [pair1,pair2,pair3])

unfoldRightEdge c1 c2@(CoreExpr.EMatch _ e1 e2 e3) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  pair3 <- constructUnfoldPair c1 e3
  return (UnfoldEdge UnfoldRight [pair1,pair2,pair3])

unfoldRightEdge c1 c2@(CoreExpr.EBind _ _ e1 e2) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  return (UnfoldEdge UnfoldRight [pair1,pair2])

unfoldRightEdge c1 c2@(CoreExpr.EApp e1 e2) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  return (UnfoldEdge UnfoldRight [pair1,pair2])

unfoldRightEdge c1 c2@(CoreExpr.ELam _ e1)  = do
  pair1 <- constructUnfoldPair c1 e1
  return (UnfoldEdge UnfoldRight [pair1])

unfoldRightEdge c1 c2 = return (UnfoldEdge UnfoldRight [])

unfoldBothEdge :: CoreExpr.CoreExpr -> CoreExpr.CoreExpr -> UnfoldState UnfoldEdge
unfoldBothEdge c1@(CoreExpr.EMatch _ e1 e2 e3) c2@(CoreExpr.EMatch _ e4 e5 e6) = do
  pair1 <- constructUnfoldPair e1 e4
  pair2 <- constructUnfoldPair e2 e5
  pair3 <- constructUnfoldPair e3 e6
  return (UnfoldEdge UnfoldBoth [pair1,pair2,pair3])

unfoldBothEdge c1@(CoreExpr.EBind _ _ e1 e2) c2@(CoreExpr.EBind _ _ e3 e4) = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e2 e4
  return (UnfoldEdge UnfoldBoth [pair1,pair2])

unfoldBothEdge c1@(CoreExpr.EApp e1 e2) c2@(CoreExpr.EApp e3 e4) = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e2 e4
  return (UnfoldEdge UnfoldBoth [pair1,pair2])

unfoldBothEdge c1@(CoreExpr.ELam _ e1) c2@(CoreExpr.ELam _ e2) = do
  pair1 <- constructUnfoldPair e1 e2
  return (UnfoldEdge UnfoldBoth [pair1])

unfoldBothEdge c1 c2 = return (UnfoldEdge UnfoldBoth [])


generateConstrains :: TypePoint -> TypePoint -> Bool
generateConstrains = undefined

subTypeCheck :: TypePoint -> TypePoint -> Bool
subTypeCheck t1@(TypePoint typeList1 typeEdges1 id1) t2@(TypePoint typeList2 typeEdges2 id2) = do
  if length(typeEdges1) == 0 then (generateConstrains t1 t2)
    else do
          length (zipWith subTypeCheckWithSameType typeEdges1 typeEdges2) > 0

subTypeCheckWithSameType :: TypeEdge -> TypeEdge -> Bool
subTypeCheckWithSameType edge1@(TypeEdge TypeArr _ pointList1) edge2@(TypeEdge TypeArr _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  --- convariant check
  let result1 = subTypeCheck subPoint2_0 subPoint1_0
  let result2 = subTypeCheck subPoint1_1 subPoint2_1
  True

subTypeCheckWithSameType edge1@(TypeEdge TypePlus _ pointList1) edge2@(TypeEdge TypePlus _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  let result1 = subTypeCheck subPoint1_0 subPoint2_0
  let result2 = subTypeCheck subPoint1_1 subPoint2_1
  True

subTypeCheckWithSameType edge1@(TypeEdge TypeProduct _ pointList1) edge2@(TypeEdge TypeProduct _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint1_1 = pointList1 !! 1
  let subPoint2_0 = pointList2 !! 0
  let subPoint2_1 = pointList2 !! 1
  let result1 = subTypeCheck subPoint1_0 subPoint2_0
  let result2 = subTypeCheck subPoint1_1 subPoint2_1
  True

subTypeCheckWithSameType edge1@(TypeEdge TypeFix _ pointList1) edge2@(TypeEdge TypeFix _ pointList2) = do
  let subPoint1_0 = pointList1 !! 0
  let subPoint2_0 = pointList2 !! 0
  let result1 = subTypeCheck subPoint1_0 subPoint2_0
  True







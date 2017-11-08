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

data UnfoldRule = UnfoldLeft | UnfoldRight | UnfoldBoth
  deriving (Show,Eq,Ord)

data UnfoldEdge = UnfoldEdge UnfoldRule [UnfoldPair]
  deriving (Show,Eq,Ord)

constructUnfoldPair :: T.CoreExpr -> T.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair c1 c2 = do
  (TemporyResult number result _) <- get
  if Map.member (c1,c2) result then return (result Map.! (c1,c2))
    else constructNewUnfoldPair c1 c2

constructNewUnfoldPair :: T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair c1 c2 = do
  (TemporyResult number result typeEnv) <- get
  freeVariables <- constructFreeVariables c1 c2
  pairExpressions <- constructPairExpressions c1 c2
  edgeList <- constructUnfoldEdge c1 c2
  let newUnfoldPair = UnfoldPair freeVariables pairExpressions c1 c2 number edgeList
  put (TemporyResult (number+1) (Map.insert (c1,c2) newUnfoldPair result) typeEnv)
  return newUnfoldPair

constructFreeVariables :: T.CoreExpr -> T.CoreExpr -> UnfoldState TypePoint
constructFreeVariables c1 c2 = do
  (TemporyResult _ _ typeEnv) <- get
  let freeVariables =Set.toList (Set.union (CoreExpr.freeVars c1) (CoreExpr.freeVars c2))
  let types = map (\x -> typeEnv Map.! (CoreExpr.EVar x) ) freeVariables
  return (constructRelationalDag types)

constructPairExpressions :: T.CoreExpr -> T.CoreExpr ->UnfoldState TypePoint
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

unfoldLeftEdge c1@(CoreExpr.EMatch e1 e2 _ _ e3) c2 = do
  pair1 <- constructUnfoldPair e1 c2
  pair2 <- constructUnfoldPair e2 c2
  pair3 <- constructUnfoldPair e3 c2
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge c1@(CoreExpr.ECon e1 e2) c2 = do
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

unfoldRightEdge c1 c2@(CoreExpr.EMatch e1 e2 _ _ e3) = do
  pair1 <- constructUnfoldPair c1 e1
  pair2 <- constructUnfoldPair c1 e2
  pair3 <- constructUnfoldPair c1 e3
  return (UnfoldEdge UnfoldRight [pair1,pair2,pair3])

unfoldRightEdge c1 c2@(CoreExpr.ECon e1 e2) = do
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
unfoldBothEdge c1@(CoreExpr.EMatch e1 e2 _ _ e3) c2@(CoreExpr.EMatch e4 e5 _ _ e6) = do
  pair1 <- constructUnfoldPair e1 e4
  pair2 <- constructUnfoldPair e2 e5
  pair3 <- constructUnfoldPair e3 e6
  return (UnfoldEdge UnfoldBoth [pair1,pair2,pair3])

unfoldBothEdge c1@(CoreExpr.ECon e1 e2) c2@(CoreExpr.ECon e3 e4) = do
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

data CHCSystem = CHCSystem (Set.Set Int) CHC
  deriving (Show,Eq,Ord)

type CHCState a = (State CHCSystem) a

buildConstrains :: UnfoldPair -> CHCState ()
buildConstrains unfoldPair@(UnfoldPair _ _ _ _ idnumber _) = do
 (CHCSystem visitedPairs chc) <- get 
 if (Set.member idnumber visitedPairs) then return ()
  else buildNewConstrains unfoldPair

buildNewConstrains :: UnfoldPair -> CHCState ()
buildNewConstrains unfoldPair@(UnfoldPair _ _ _ _ _ edgeList) = do
 mapM (buildEdgeConstrains unfoldPair) edgeList
 return ()

buildEdgeConstrains :: UnfoldPair -> UnfoldEdge -> CHCState
buildConstrains unfoldPair unfoldEdge@(UnfoldEdge UnfoldLeft _) = buildLeftConstrains unfoldPair unfoldEdge
buildConstrains unfoldPair unfoldEdge@(UnfoldEdge UnfoldRight _) = buildRightConstrains unfoldPair unfoldEdge
buildConstrains unfoldPair unfoldEdge@(UnfoldEdge UnfoldBoth _) = buildBothConstrains unfoldPair unfoldEdge

buildLeftConstrains :: UnfoldPair -> UnfoldEdge -> CHCState
buildLeftConstrains (UnfoldPair freeVariables pairExpression (CoreExpr.EBin _ _ _) _ idnumber _ ) (UnfoldEdge _ successors) = do
 let (UnfoldPair freeVar1 pairExpr1 _ _ id1 _ ) = successors !! 0
 let (UnfoldPair freeVar2 pairExpr2 _ _ id2 _ ) = successors !! 1
 buildOpConstrains pairExpr1 pairExpr2 pairExpression op
 buildFreeVariables freeVariables freeVar1
 buildFreeVariables freeVariables freeVar2
 mapM buildConstrains successors
 return ()

buildLeftConstrains (UnfoldPair freeVariables pairExpression (CoreExpr.EIf _ _ _) _ idnumber _ ) (UnfoldEdge _ successors) = do
 let (UnfoldPair freeVar1 pairExpr1 _ _ id1 _ ) = successors !! 0
 let (UnfoldPair freeVar2 pairExpr2 _ _ id2 _ ) = successors !! 1
 let (UnfoldPair freeVar3 pairExpr3 _ _ id3 _ ) = successors !! 2
 buildFreeVariables freeVariables freeVar1
 buildFreeVariables (buildJoinTrue pairExpr1 freeVariables) freeVar2
 buildFreeVariables (buildJoinFalse pairExpr2 freeVariables) freeVar3
 subTypeCheck pairExpression pairExpr2
 subTypeCheck pairExpression pairExpr3
 mapM buildConstrains successors
 return ()

buildLeftConstrains (UnfoldPair freeVariables pairExpression (CoreExpr.EMatch _ _ _ _ _ )_ idnumber _ ) (UnfoldEdge _ successors) = do
 let (UnfoldPair freeVar1 pairExpr1 _ _ id1 _ ) = successors !! 0
 let (UnfoldPair freeVar2 pairExpr2 _ _ id2 _ ) = successors !! 1
 let (UnfoldPair freeVar3 pairExpr3 _ _ id3 _ ) = successors !! 2
 buildFreeVariables freeVariables freeVar1
 buildFreeVariables (buildNil ) 


generateConstrains :: TypePoint -> TypePoint -> CHCState ()
generateConstrains t1@(TypePoint typeList1 _ _) t2 = do
  let listWithVar = filter (isTypeVar) typeList1
  if (length typeList1) == 0 then (generateRule t1 t2)
    else return ()

generateRule :: TypePoint -> TypePoint -> CHCState ()
generateRule t1@(TypePoint typeList1 _ id1) t2@(TypePoint typeList2 _ id2) = do
  let sortList = (getSortFromTypes typeList1)
  let r1 = Function ("R@"++ show(id1)) sortList
  let r2 = Function ("R@"++ show(id2)) sortList
  let varList = zipWith (\x y -> (ParameterVar (Var ("arg@"++show(y)) x))) sortList [1 ..]
  let b = ApplyFunction r1 varList
  let h = ApplyFunction r2 varList
  (CHCSystem unfoldPairSet (CHC rules f v q))  <- get
  let newCHC = CHC ((Rule b h):rules) f v q
  put (CHCSystem unfoldPairSet newCHC)

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







module Language.Equivalence.SimpleInferRelationalTypes where
import Language.Equivalence.TypeInference
import Language.Equivalence.SimpleRelationalTypes
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Language.Equivalence.Types as T
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map


data TemporyResult = TemporyResult Int  (Map.Map (T.CoreExpr,T.CoreExpr) UnfoldPair) (Map.Map T.CoreExpr Type) (Map.Map T.CoreExpr [T.Var])  CHC
  deriving (Show,Eq,Ord)

type UnfoldState a = (State TemporyResult) a

data UnfoldPair = UnfoldPair TypePoint TypePoint T.CoreExpr T.CoreExpr Int [UnfoldEdge]
  deriving (Show,Eq,Ord)

data UnfoldRule = UnfoldLeft | UnfoldRight | UnfoldBoth
  deriving (Show,Eq,Ord)

data UnfoldEdge = UnfoldEdge UnfoldRule [UnfoldPair]
  deriving (Show,Eq,Ord)

constructUnfoldPair :: T.CoreExpr -> T.CoreExpr ->UnfoldState UnfoldPair
constructUnfoldPair e1 e2 = do
  (TemporyResult _ result _ _ _) <- get
  if Map.member (e1,e2) result then return (result Map.! (e1,e2))
    else constructNewUnfoldPair e1 e2

constructNewUnfoldPair :: T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldPair
constructNewUnfoldPair e1 e2 = do
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  freeVars1 <- getFreeV e1
  freeVars2 <- getFreeV e2
  contextV <- constructFreeVariables freeVars1 freeVars2
  expressionV <- constructPairExpressions e1 e2 freeVars1 freeVars2
  let virtualPair = UnfoldPair contextV expressionV e1 e2 number []
  edgeList <- constructUnfoldEdge virtualPair e1 e2
  let newUnfoldPair = UnfoldPair contextV expressionV e1 e2 number edgeList
  put (TemporyResult (number+1) (Map.insert (e1,e2) newUnfoldPair result) typeEnv mapToFreeVar chc)
  return newUnfoldPair

getFreeV :: T.CoreExpr -> UnfoldState [T.Var]
getFreeV e = do
  (TemporyResult _ _ _ mapToFreeVar _) <- get
  return (mapToFreeVar Map.! e)

constructFreeVariables :: [T.Var] -> [T.Var] ->UnfoldState TypePoint
constructFreeVariables free1 free2= do
  freeV1 <- mapM (\x->getType (T.EVar x) ) free1
  freeV2 <- mapM (\x->getType (T.EVar x) ) free2
  return (constructVersionSpace [] [] freeV1 freeV2)

constructPairExpressions :: T.CoreExpr -> T.CoreExpr -> [T.Var] -> [T.Var] ->UnfoldState TypePoint
constructPairExpressions e1 e2 free1 free2= do
  t1 <- getType e1
  t2 <- getType e2
  freeV1 <- mapM (\x->getType (T.EVar x) ) free1
  freeV2 <- mapM (\x->getType (T.EVar x) ) free2
  return (constructVersionSpace [t1] [t2] freeV1 freeV2)

getType :: T.CoreExpr -> UnfoldState Type
getType e = do
 (TemporyResult _ _ typeEnv _ _) <- get
 return (typeEnv Map.! e)

constructUnfoldEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState [UnfoldEdge]
constructUnfoldEdge rootPair e1 e2 = do
  leftEdge  <- unfoldLeftEdge rootPair e1 e2
  rightEdge <- unfoldRightEdge rootPair e1 e2
  bothEdge <- unfoldBothEdge rootPair e1 e2
  return (filter (\(UnfoldEdge _ list) -> if (length list) > 0 then True else False ) [leftEdge,rightEdge,bothEdge])

unfoldLeftEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldLeftEdge pair (T.EBin op e1 e2) e3 = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e1 e3
  buildBinaryConstrains 1 op pair1 pair2 pair
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair (T.EIf e1 e2 e3) e4 = do
  pair1 <- constructUnfoldPair e1 e4
  buildContextEntail pair pair1
  pair2 <- constructUnfoldPair e2 e4
  buildContextIfElse True 1 pair1 pair pair2
  pair3 <- constructUnfoldPair e3 e4
  buildContextIfElse False 1 pair1 pair pair3
  buildEntail pair2 pair
  buildEntail pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair (T.EApp e1 e2) e3 = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e2 e3
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  buildArgsConstrains 1 pair1 pair2
  buildAppConstrainsLeft pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair (T.ELam v e1) e2 = do 
  pair1 <- constructUnfoldPair e1 e2
  buildLamContextLeft pair pair1
  buildLamConstrains [1] pair1 pair
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge _  _ _ = return (UnfoldEdge UnfoldLeft [])

buildAppConstrains :: Int -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildAppConstrains leftOrRight pair1 pair2 pair3 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ t2 _ _ pairId2 _) = pair2
 let (UnfoldPair _ t3 _ _ pairId3 _) = pair3
 let (TypePoint _ edges _) = t1
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
 let rightArr = typePoints !! 0
 let indexMap = Map.fromList ([(1,1),(2,2)] )
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 freeV3 <- getAllFreeVar pair3
 let pairs1 = getPairTypePoint rightArr t3 [] [] indexMap
 mapM (buildAppConstrain leftOrRight pairId1 1 pairId2 0 pairId3 0 freeV1 freeV2 freeV3 t2) pairs1
 return ()

buildAppConstrain :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> [T.Var]->[T.Var]->[T.Var] ->TypePoint -> (TypePoint,TypePoint)-> UnfoldState()
buildAppConstrain leftOrRight pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 freeV1 freeV2 freeV3 t2 (t1,t3) = do
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  let (TypePoint _ _ typePointId3) = t3
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  r3 <- getPredicate freeV3 t3 pairId3 indicator3
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId3 indicator3 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 indicator2 typePointId2 pairId3 indicator3 typePointId3) freeIn23
  return ()

allExprEqual :: Int -> Int -> Int -> TypePoint -> Int -> Int ->Int -> [Expr]
allExprEqual = undefined

buildArgsConstrains :: Int -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildArgsConstrains leftOrRight pair1 pair2 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ t2 _ _ pairId2 _) = pair2
 let (TypePoint _ edges _) = t1
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
 let leftArr = typePoints !! 0
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 buildEntail 1 pairId1 leftArr freeV1 1 pairId2 t2 freeV2
 return ()

buildContextIfElse :: Bool -> Int ->UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextIfElse trueOrFalse leftOrRight pair1 pair2 pair3 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair c1 _ _ _ pairId2 _) = pair2
 let (UnfoldPair c2 _ _ _ pairId3 _) = pair3
 let indexMap = Map.empty
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 freeV3 <- getAllFreeVar pair3
 let pairs1 = getPairTypePoint t1 c2 [1,2] [] indexMap
 let pairs2 = getPairTypePoint c1 c2 [1,2] [] indexMap
 let validPairs = filter (\((_,t3),(_,t4)) -> t3 == t4) (zip pairs1 pairs2)
 mapM (buildIfElse trueOrFalse leftOrRight pairId1 1 pairId2 0 pairId3 0 freeV1 freeV2 freeV3) validPairs
 return ()

buildIfElse :: Bool -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> [T.Var]->[T.Var]->[T.Var] ->((TypePoint,TypePoint),(TypePoint,TypePoint))-> UnfoldState()
buildIfElse trueOrFalse leftOrRight pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 freeV1 freeV2 freeV3 ((t1,t3),(t2,_))= do
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  let (TypePoint _ _ typePointId3) = t3
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  r3 <- getPredicate freeV3 t3 pairId3 indicator3
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId3 indicator3 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 indicator2 typePointId2 pairId3 indicator3 typePointId3) freeIn23
  let eq3 = ifElseConstrain trueOrFalse leftOrRight pairId3 indicator3 t3
  let rule = Rule (MkAnd ([r1,r2,eq3]++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

ifElseConstrain :: Bool -> Int -> Int -> Int -> TypePoint -> Expr
ifElseConstrain True 1 pairId indicator t1 =ExprVar ((getLeftExpr pairId indicator t1) !! 0)
ifElseConstrain True 2 pairId indicator t1 =ExprVar ((getRightExpr pairId indicator t1) !! 0)
ifElseConstrain False 1 pairId indicator t1 =MkNot (ExprVar ((getLeftExpr pairId indicator t1) !! 0))
ifElseConstrain False 2 pairId indicator t1 =MkNot (ExprVar ((getRightExpr pairId indicator t1) !! 0))
trueConstrain _ _ _ _ = error "true constrain error"

buildBinaryConstrains :: Int -> T.Binop -> UnfoldPair -> UnfoldPair ->UnfoldPair -> UnfoldState ()
buildBinaryConstrains leftOrRight op pair1 pair2 pair3 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ t2 _ _ pairId2 _) = pair2
 let (UnfoldPair _ t3 _ _ pairId3 _) = pair3
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 freeV3 <- getAllFreeVar pair3
 let indexMap = Map.fromList [(1,1),(1,2)]
 let pairs1 = getPairTypePoint t1 t3 [] [] indexMap
 let pairs2 = getPairTypePoint t2 t3 [] [] indexMap
 let validPairs = filter (\((_,t3),(_,t4)) -> t3 == t4) (zip pairs1 pairs2)
 mapM (buildBinaryConstrain leftOrRight op pairId1 1 pairId2 1 pairId3 1 freeV1 freeV2 freeV3) validPairs
 return ()

getAllFreeVar :: UnfoldPair ->UnfoldState [T.Var]
getAllFreeVar (UnfoldPair _ _ e1 e2 _ _) = do
 freeV1 <- getFreeV e1
 freeV2 <- getFreeV e2
 return $ freeV1 ++ freeV2

buildBinaryConstrain :: Int ->T.Binop -> Int -> Int -> Int -> Int -> Int -> Int -> [T.Var]->[T.Var]->[T.Var] ->((TypePoint,TypePoint),(TypePoint,TypePoint))-> UnfoldState()
buildBinaryConstrain leftOrRight op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 freeV1 freeV2 freeV3 ((t1,t3),(t2,_))= do
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  let (TypePoint _ _ typePointId3) = t3
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  r3 <- getPredicate freeV3 t3 pairId3 indicator3
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId3 indicator3 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 indicator2 typePointId2 pairId3 indicator3 typePointId3) freeIn23
  let eq3 = generateBinary leftOrRight op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3
  let rule = Rule (MkAnd ([r1,r2]++eq3++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()


generateBinary :: Int ->T.Binop -> Int -> Int -> Int -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinary 1 op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3 = generateBinaryLeft op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3
generateBinary 2 op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3 = generateBinaryRight op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3
generateBinary _ _ _ _ _ _ _ _ _ _ _ = error "generateBinary is wrong" 

generateBinaryLeft :: T.Binop -> Int -> Int -> Int -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinaryLeft op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3 = do
  let leftExpr1 = getLeftExpr pairId1 indicator1 t1
  let leftExpr2 = getLeftExpr pairId2 indicator2 t2
  let leftExpr3 = getLeftExpr pairId3 indicator3 t3
  let rightExpr1 = getRightExpr pairId1 indicator1 t1
  let rightExpr2 = getRightExpr pairId2 indicator1 t2
  let rightExpr3 = getRightExpr pairId3 indicator1 t3
  let rE1EqrE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) rightExpr1 rightExpr3
  let rE2EqrE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) rightExpr2 rightExpr3
  let binary = getBinary op (ExprVar (leftExpr1!!0)) (ExprVar (leftExpr2!!0)) (ExprVar (leftExpr3!!0))
  (binary:(rE1EqrE3++rE2EqrE3))

generateBinaryRight :: T.Binop -> Int -> Int -> Int -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinaryRight op pairId1 indicator1 pairId2 indicator2 pairId3 indicator3 t1 t2 t3 = do
  let leftExpr1 = getLeftExpr pairId1 indicator1 t1
  let leftExpr2 = getLeftExpr pairId2 indicator2 t2
  let leftExpr3 = getLeftExpr pairId3 indicator3 t3
  let rightExpr1 = getRightExpr pairId1 indicator1 t1
  let rightExpr2 = getRightExpr pairId2 indicator1 t2
  let rightExpr3 = getRightExpr pairId3 indicator1 t3
  let lE1EqlE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) leftExpr1 leftExpr3
  let lE2EqlE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) leftExpr2 leftExpr3
  let binary = getBinary op (ExprVar (rightExpr1!!0)) (ExprVar (rightExpr2!!0)) (ExprVar (rightExpr3!!0))
  (binary:(lE1EqlE3++lE2EqlE3))

getBinary :: T.Binop -> Expr -> Expr -> Expr -> Expr
getBinary T.Plus expr1 expr2 expr3 = MkEq expr3 (MkAnd [expr1,expr2])
getBinary T.Minus expr1 expr2 expr3 = MkEq expr3 (MkSub [expr1,expr2])
getBinary T.Mul expr1 expr2 expr3 = MkEq expr3 (MkMul [expr1,expr2])
getBinary T.Div expr1 expr2 expr3 = MkEq expr3 (MkDiv_1 expr1 expr2)
getBinary T.Eq expr1 expr2 expr3 = MkEq expr3 (MkEq expr1 expr2)
getBinary T.Ne expr1 expr2 expr3 = MkEq expr3 (MkNot (MkEq expr1 expr2))
getBinary T.Lt expr1 expr2 expr3 = MkEq expr3 (MkLt expr1 expr2)
getBinary T.Le expr1 expr2 expr3 = MkEq expr3 (MkLe expr1 expr2)
getBinary T.And expr1 expr2 expr3 = MkEq expr3 (MkAnd [expr1 , expr2])
getBinary T.Or expr1 expr2 expr3 = MkEq expr3 (MkOr [expr1 , expr2])
getBinary T.Cons _ _ _= error "generate binary constrains does not handle Cons"

generateEq :: Int -> Int -> Int -> Int -> Int -> Int -> T.Var -> UnfoldState [Expr]
generateEq pairId1 indicator1 typePointId1 pairId2 indicator2 typePointId2 v= do
  var1 <- getVarInSmt pairId1 indicator1 typePointId1 v
  var2 <- getVarInSmt pairId2 indicator2 typePointId2 v
  return $ zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var2
 


unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge = undefined

unfoldBothEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldBothEdge = undefined

buildConstrainsForPair :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState ()
buildConstrainsForPair = undefined

getPredicate :: [T.Var] -> TypePoint -> Int -> Int ->UnfoldState Expr
getPredicate freeVs t@(TypePoint typePair _ typePointId) pairId indicator = do
  let leftExpr =getLeftExpr pairId indicator t
  let rightExpr = getRightExpr pairId indicator t
  allFreeVar <- mapM (getVarInSmt pairId indicator typePointId) freeVs
  let allExpr = leftExpr ++ rightExpr ++(concat allFreeVar)
  let sortList = map (\(Var _ sort)-> sort) allExpr
  let predicateName = ("R"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId))
  return $ ApplyFunction (Function predicateName sortList) (map (\x -> ParameterVar x) allExpr)
 

getLeftExpr :: Int -> Int -> TypePoint -> [Var]
getLeftExpr pairId indicator (TypePoint (Pair left1 left2 _ _ _ _) _ typeId) = do
  let allLeft =zip (left1++left2) [1 .. ]
  concat (map (oneExpr "exprLeft!" pairId indicator typeId) allLeft)

getRightExpr :: Int -> Int -> TypePoint -> [Var]
getRightExpr pairId indicator (TypePoint (Pair _ _ right1 right2 _ _) _ typeId) = do
  let allRight =zip (right1++right2) [1 .. ]
  concat (map (oneExpr "exprRight!" pairId indicator typeId) allRight)

oneExpr :: String -> Int -> Int -> Int -> (Type,Int) -> [Var]
oneExpr leftOrRight pairId indicator typePointId (t,index) = do
  let sorts = getSortFromType t
  let names = getVarName pairId indicator typePointId t (T.Var (leftOrRight+show(index)))
  zipWith (\n s -> Var n s) names sorts

getVarInSmt ::Int -> Int ->Int -> T.Var ->UnfoldState  [Var]
getVarInSmt pairId indicator typePointId v = do
  t <- getType (T.EVar v)
  let sorts = getSortFromType t
  let names = getVarName pairId indicator typePointId t v
  let varInSmt = zipWith (\n s -> Var n s) names sorts
  return varInSmt


getVarName pairId  indicator typePointId (TInt)  (T.Var name) = [name +"@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)]
getVarName pairId  indicator typePointId (TBool)  (T.Var name)  = [name +"@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)]
getVarName pairId  indicator typePointId (TList _)  (T.Var name) = do
 let name1 = name +"cell@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)
 let name2 = name +"length@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)
 [name1,name2]

getVarName _ _ _ _ _ = []

getSortFromType :: Type -> [Sort]
getSortFromType (TInt)  = [IntegerSort]
getSortFromType (TBool) = [BoolSort]
getSortFromType (TList _) = [IntegerSort,IntegerSort]
getSortFromType _ = []

getPairTypePoint :: TypePoint -> TypePoint ->[Int] -> [Int] -> (Map.Map Int Int) -> [(TypePoint,TypePoint)]
getPairTypePoint t1 t2 dropList1 dropList2 indexMap = do
  let allPossiblePair =Set.toList (execState (collectNewCorrespondingTypePoint t1 t2 dropList1 dropList2 indexMap) (Set.empty))
  filter (\((TypePoint _ edgeList1 _),(TypePoint _ edgeList2 _)) -> if (length (edgeList1++edgeList2) == 0) then True else False) allPossiblePair

collectCorrespondingTypePoint :: TypePoint -> TypePoint -> [Int] -> [Int] -> (Map.Map Int Int) -> (State (Set.Set (TypePoint,TypePoint))) ()
collectCorrespondingTypePoint t1 t2 dropList1 dropList2 indexMap = do
  resultSet <- get
  if (Set.member (t1,t2) resultSet ) then return ()
    else collectNewCorrespondingTypePoint t1 t2 dropList1 dropList2 indexMap

collectNewCorrespondingTypePoint :: TypePoint -> TypePoint -> [Int] -> [Int] -> (Map.Map Int Int) -> (State (Set.Set (TypePoint,TypePoint))) ()
collectNewCorrespondingTypePoint t1@(TypePoint _ edgeList1 _) t2@(TypePoint _ edgeList2 _) dropList1 dropList2 indexMap = do
  resultSet <- get
  put (Set.insert (t1,t2) resultSet)
  let allPairsOfEdge =concat (map (\x -> map (\y -> (x,y)) edgeList2) edgeList1)
  let validPairs = filter (\(e1,e2) -> twoEdgeListSame e1 e2 dropList1 dropList2 indexMap) allPairsOfEdge
  mapM (addCorrespondingTypePoint dropList1 dropList2 indexMap) validPairs
  return ()

addCorrespondingTypePoint :: [Int] -> [Int] -> (Map.Map Int Int)-> (TypeEdge,TypeEdge) ->(State (Set.Set (TypePoint,TypePoint))) ()
addCorrespondingTypePoint  dropList1 dropList2 indexMap ((TypeEdge _ list1), (TypeEdge _ list2)) = do
  let pairTypePoint = zip list1 list2
  mapM (\(t1,t2)-> collectCorrespondingTypePoint t1 t2 dropList1 dropList2 indexMap) pairTypePoint
  return ()

twoEdgeListSame :: TypeEdge -> TypeEdge -> [Int] -> [Int] -> (Map.Map Int Int) -> Bool
twoEdgeListSame  (TypeEdge index1 _) (TypeEdge index2 _) dropIndex1 dropIndex2 indexMap = do
  let dropSet1 = Set.fromList dropIndex1
  let dropSet2 = Set.fromList dropIndex2
  let drop1 = filter (\x -> Set.notMember x dropSet1) index1
  let drop2 = filter (\x -> Set.notMember x dropSet2) index2
  let mapIndex = map (\x -> indexMap Map.! x) drop1
  mapIndex == drop2



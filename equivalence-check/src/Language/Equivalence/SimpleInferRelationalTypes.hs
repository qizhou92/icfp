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
  pair2 <- constructUnfoldPair e2 e3
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
  buildEntails pair2 pair
  buildEntails pair3 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2,pair3])

unfoldLeftEdge pair (T.EApp e1 e2) e3 = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e2 e3
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  buildArgsConstrains 1 pair1 pair2
  buildAppConstrains 1 pair1 pair2 pair
  return (UnfoldEdge UnfoldLeft [pair1,pair2])

unfoldLeftEdge pair (T.ELam v e1) e2 = do 
  pair1 <- constructUnfoldPair e1 e2
  buildLamContext [1] [v] pair pair1
  buildLamEntail [1] [v] pair1 pair
  return (UnfoldEdge UnfoldLeft [pair1])

unfoldLeftEdge _  _ _ = return (UnfoldEdge UnfoldLeft [])

unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge pair e1 (T.EBin op e2 e3) = do
  pair1 <- constructUnfoldPair e1 e2
  pair2 <- constructUnfoldPair e1 e3
  buildBinaryConstrains 2 op pair1 pair2 pair
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  return (UnfoldEdge UnfoldRight [pair1,pair2])

unfoldRightEdge pair e1 (T.EIf e2 e3 e4) = do
  pair1 <- constructUnfoldPair e1 e2
  buildContextEntail pair pair1
  pair2 <- constructUnfoldPair e1 e3
  buildContextIfElse True 2 pair1 pair pair2
  pair3 <- constructUnfoldPair e1 e4
  buildContextIfElse False 2 pair1 pair pair3
  buildEntails pair2 pair
  buildEntails pair3 pair
  return (UnfoldEdge UnfoldRight [pair1,pair2,pair3])

unfoldRightEdge pair e1 (T.EApp e2 e3) = do
  pair1 <- constructUnfoldPair e1 e2
  pair2 <- constructUnfoldPair e1 e3
  buildContextEntail pair pair1
  buildContextEntail pair pair2
  buildArgsConstrains 2 pair2 pair1
  buildAppConstrains 2 pair1 pair2 pair
  return (UnfoldEdge UnfoldRight [pair1,pair2])

unfoldRightEdge pair e1 (T.ELam v e2) = do 
  pair1 <- constructUnfoldPair e1 e2
  buildLamContext [2] [v] pair pair1
  buildLamEntail [2] [v] pair1 pair
  return (UnfoldEdge UnfoldRight [pair1])

unfoldRightEdge _  _ _ = return (UnfoldEdge UnfoldRight [])

unfoldBothEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldBothEdge pair (T.EMatch e1 e2 v1 v2 e3) (T.EMatch e4 e5 v3 v4 e6) = do
  pair1 <- constructUnfoldPair e1 e4
  buildContextEntail pair pair1
  pair2 <- constructUnfoldPair e2 e5
  buildNilContext pair pair1 pair2
  pair3 <- constructUnfoldPair e3 e6
  buildTailContext v1 v2 v3 v4 pair pair1 pair3
  buildEntails pair2 pair
  buildEntails pair3 pair
  return (UnfoldEdge UnfoldBoth [pair1,pair2,pair3])

unfoldBothEdge pair (T.ELam v1 e1) (T.ELam v2 e2) = do
  pair1 <- constructUnfoldPair e1 e2
  buildLamContext [1,2] [v1,v2] pair pair1
  buildLamEntail [1,2] [v1,v2] pair1 pair
  return (UnfoldEdge UnfoldRight [pair1])

unfoldBothEdge _ _ _ = return (UnfoldEdge UnfoldBoth [])

buildSinglePair :: UnfoldPair -> Int -> T.CoreExpr -> UnfoldState [Expr] 
buildSinglePair (UnfoldPair _ expressionV _ _ pairId _) leftOrRight (T.EInt value1) = do
  let expr = (getExprWithIndex leftOrRight 0 pairId expressionV) !! 0
  return $ [(MkEq (ExprVar expr) (ExprConstant (ConstantInt value1)))]

buildSinglePair (UnfoldPair _ expressionV _ _ pairId _) leftOrRight (T.EBool value1) = do
  let expr = (getExprWithIndex leftOrRight 0 pairId expressionV) !! 0
  return $ [(MkEq (ExprVar expr) (ExprConstant (ConstantBool value1)))]

buildSinglePair (UnfoldPair contextV expressionV _ _ pairId _) leftOrRight (T.EVar value1) = do
  let expr = getExprWithIndex leftOrRight 0 pairId expressionV
  let (TypePoint _ _ typePointId) = contextV
  varInSmt <- getVarInSmt pairId 0 typePointId value1
  return $ (zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) expr varInSmt)

buildSinglePair _ _ _ = error ("there is error in buildSinglePair")

buildConstrainsForPair :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState ()
buildConstrainsForPair pair@(UnfoldPair contextV expressionV _ _ pairId _) e1 e2 = do
  eq1 <- buildSinglePair pair 1 e1
  eq2 <- buildSinglePair pair 2 e2
  freeV1 <- getAllFreeVar pair
  r1 <- getPredicate freeV1 expressionV pairId 1
  r2 <- getPredicate freeV1 contextV pairId 0
  if (length freeV1) == 0 then updateRule (MkAnd (eq1++eq2)) r1
    else updateRule (MkAnd (r2:(eq1++eq2))) r1

updateRule :: Expr -> Expr -> UnfoldState ()
updateRule e1 e2 = do
  let rule = Rule e1 e2
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

buildTailContext :: T.Var -> T.Var -> T.Var -> T.Var -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildTailContext head1 tail1 head2 tail2 pair1 pair2 pair3 = do
  let (UnfoldPair contextV1 _ _ _ pairId1 _) = pair1
  let (UnfoldPair _ expressionV _ _ pairId2 _) = pair2
  let (UnfoldPair contextV2 _ _ _ pairId3 _) = pair3
  let (TypePoint _ _ typePointId1) = contextV1
  let (TypePoint _ _ typePointId2) = expressionV
  let (TypePoint _ _ typePointId3) = contextV2
  freeV1 <- getAllFreeVar pair1
  freeV2 <- getAllFreeVar pair2
  freeV3 <- getAllFreeVar pair3
  r1 <- getPredicate freeV1 contextV1 pairId1 0
  r2 <- getPredicate freeV2 expressionV pairId2 1
  r3 <- getPredicate freeV3 contextV2 pairId3 0
  let leftExpr =  (getLeftExpr pairId2 expressionV)!! 0
  let rightExpr = (getRightExpr pairId2 expressionV)!! 0
  let leftLength = leftExpr !! 1
  let rightLength = rightExpr !! 1
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 0 typePointId1 pairId3 0 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 1 typePointId2 pairId3 0 typePointId3) freeIn23
  headInSmt1 <- getVarInSmt pairId3 0 typePointId3 head1
  headInSmt2 <- getVarInSmt pairId3 0 typePointId3 head2
  tailInSmt1 <- getVarInSmt pairId3 0 typePointId3 tail1
  tailInSmt2 <- getVarInSmt pairId3 0 typePointId3 tail2
  let leftLenghtGt0 = MkGt (ExprVar leftLength) (ExprConstant (ConstantInt 0))
  let rightLenghtGt0 = MkGt (ExprVar rightLength) (ExprConstant (ConstantInt 0))
  let leftLengthMinus1 = MkEq (ExprVar (tailInSmt1 !! 1)) (MkSub [(ExprVar leftLength),(ExprConstant (ConstantInt 1))])
  let rightLengthMinus1 = MkEq (ExprVar (tailInSmt2 !! 1)) (MkSub [(ExprVar rightLength),(ExprConstant (ConstantInt 1))])
  let elemEqual1 =  MkEq (ExprVar (tailInSmt1 !! 0)) (ExprVar (leftExpr !! 0))
  let elemEqual2 =  MkEq (ExprVar (tailInSmt2 !! 0)) (ExprVar (rightExpr !! 0))
  let r2_2 = modified r2 (headInSmt1 !! 0) (headInSmt2 !! 0)
  let conditions = [leftLenghtGt0,rightLenghtGt0,leftLengthMinus1,rightLengthMinus1,elemEqual1,elemEqual2]
  let rule = Rule (MkAnd ([r1,r2,r2_2]++(conditions)++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

modified :: Expr ->Var ->Var -> Expr
modified (ApplyFunction f1 parameterList ) v1 v2 = do
  let ([_,p2,_,p4],tails) = splitAt 4 parameterList
  let newParameterList = [(ParameterVar v1),p2,(ParameterVar v2),p4]++tails
  (ApplyFunction f1 newParameterList)
modified _ _ _ = error "there is error in modified"

buildNilContext :: UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildNilContext pair1 pair2 pair3 = do
  let (UnfoldPair contextV1 _ _ _ pairId1 _) = pair1
  let (UnfoldPair _ expressionV _ _ pairId2 _) = pair2
  let (UnfoldPair contextV2 _ _ _ pairId3 _) = pair3
  let (TypePoint _ _ typePointId1) = contextV1
  let (TypePoint _ _ typePointId2) = expressionV
  let (TypePoint _ _ typePointId3) = contextV2
  freeV1 <- getAllFreeVar pair1
  freeV2 <- getAllFreeVar pair2
  freeV3 <- getAllFreeVar pair3
  r1 <- getPredicate freeV1 contextV1 pairId1 0
  r2 <- getPredicate freeV2 expressionV pairId2 1
  r3 <- getPredicate freeV3 contextV2 pairId3 0
  let leftLength = ((getLeftExpr pairId2 expressionV)!! 0)!! 1
  let rightLength = ((getRightExpr pairId2 expressionV)!! 0)!! 1
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 0 typePointId1 pairId3 0 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 1 typePointId2 pairId3 0 typePointId3) freeIn23
  let eq3 = MkEq (ExprVar leftLength) (ExprConstant (ConstantInt 0))
  let eq4 = MkEq (ExprVar rightLength) (ExprConstant (ConstantInt 0))
  let rule = Rule (MkAnd ([r1,r2,eq3,eq4]++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

buildLamEntail :: [Int] -> [T.Var] -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildLamEntail leftOrRights vars pair1 pair2 = do
 let (UnfoldPair _ expressionV1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ expressionV2 _ _ pairId2 _) = pair2
 let (TypePoint _ edges _) = expressionV2
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == leftOrRights then True else False ) edges) !! 0
 let rightArr = typePoints !! 1
 let indexMap = Map.fromList ([(1,1),(2,2)] )
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 let pairs1 = getPairTypePoint expressionV1 rightArr [] [] indexMap
 mapM (getLamEntails leftOrRights vars 1 pairId1 1 pairId2 freeV1 freeV2) pairs1
 return ()
 
getLamEntails :: [Int] -> [T.Var] -> Int -> Int -> Int -> Int -> [T.Var] -> [T.Var] ->(TypePoint,TypePoint) -> UnfoldState ()
getLamEntails leftOrRights vars indicator1 pairId1 indicator2 pairId2 freeV1 freeV2 (t1,t2)= do
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  let freeIn12 = filter (\x -> elem x freeV1) freeV2
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId2 indicator2 typePointId2) freeIn12
  let indexWithPair = zip leftOrRights vars
  eq2 <- mapM (getLamEntail pairId1 indicator1 t1 pairId2 t2) indexWithPair
  let rule = Rule (MkAnd ([r1]++(concat eq2)++(concat eq1))) r2
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

getLamEntail :: Int -> Int -> TypePoint -> Int -> TypePoint -> (Int,T.Var) ->UnfoldState [Expr]
getLamEntail pairId1 indicator1 t1 pairId2 t2 (leftOrRight,var) = do
  let leftExpr = getExprWithIndex leftOrRight 0 pairId2 t2
  let (TypePoint _ _ typePointId1) = t1
  varInSmt <- getVarInSmt pairId1 indicator1 typePointId1 var
  return (zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2) ) leftExpr varInSmt)


buildLamContext :: [Int] -> [T.Var] -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildLamContext leftOrRights v pair1 pair2 = do
 let (UnfoldPair contextV1 expressionV1 _ _ pairId1 _) = pair1
 let (UnfoldPair contextV2 _ _ _ pairId2 _) = pair2
 let (TypePoint _ edges _) = expressionV1
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == (leftOrRights) then True else False ) edges) !! 0
 let leftArr = typePoints !! 0
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 getLamConstrain leftOrRights v 1 pairId1 leftArr 0 pairId1 contextV1 0 pairId2 contextV2 freeV1 freeV1 freeV2
 return ()

getLamConstrain :: [Int] -> [T.Var] -> Int -> Int -> TypePoint -> Int -> Int -> TypePoint -> Int -> Int -> TypePoint ->[T.Var]->[T.Var]->[T.Var]-> UnfoldState ()
getLamConstrain leftOrRights v indicator1 pairId1 t1 indicator2 pairId2 t2 indicator3 pairId3 t3 freeV1 freeV2 freeV3= do
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  r3 <- getPredicate freeV3 t3 pairId3 indicator3
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  let (TypePoint _ _ typePointId3) = t3
  let freeIn13 = filter (\x -> elem x freeV1) freeV3
  let freeIn23 = filter (\x -> elem x freeV2) freeV3
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId3 indicator3 typePointId3) freeIn13
  eq2 <- mapM (generateEq pairId2 indicator2 typePointId2 pairId3 indicator3 typePointId3) freeIn23
  eq3 <- mapM (getExprEqualVar pairId1 t1 indicator3 pairId3 typePointId3) (zip leftOrRights v)
  let rule = Rule (MkAnd ([r1,r2]++(concat eq3)++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

getExprEqualVar :: Int -> TypePoint -> Int -> Int -> Int -> (Int,T.Var) -> UnfoldState [Expr]
getExprEqualVar pairId1 t1 indicator3 pairId3 typePointId3 (leftOrRight,v) = do
  let expr1 = getExprWithIndex leftOrRight 0 pairId1  t1
  vExpr <- getVarInSmt pairId3 indicator3 typePointId3 v
  return $ zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) vExpr expr1

getExprWithIndex :: Int -> Int ->Int -> TypePoint -> [Var]
getExprWithIndex 1 index pairId t = (getLeftExpr pairId  t) !! index
getExprWithIndex 2 index pairId t = (getRightExpr pairId t) !! index
getExprWithIndex _ _ _ _ = error "get expr with index is wrong"


buildAppConstrains :: Int -> UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildAppConstrains leftOrRight pair1 pair2 pair3 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ t2 _ _ pairId2 _) = pair2
 let (UnfoldPair _ t3 _ _ pairId3 _) = pair3
 let (TypePoint _ edges _) = t1
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
 let rightArr = typePoints !! 1
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
  let eq3 = getAppConstrains leftOrRight pairId1 pairId2 pairId3 t1 t2 t3
  let rule = Rule (MkAnd ([r1,r2]++eq3++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

getAppConstrains :: Int -> Int -> Int-> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
getAppConstrains 1  pairId1 pairId2 pairId3 t1 t2 t3 = do
  let left1 = concat (getLeftExpr pairId1 t1)
  let left2 = concat (getLeftExpr pairId2 t2)
  let left3 = concat (getLeftExpr pairId3 t3)
  let eq1 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) left1 (left2++left3)
  let right1 =concat (getRightExpr pairId1 t1)
  let right2 =concat (getRightExpr pairId2 t2)
  let right3 =concat (getRightExpr pairId3 t3)
  let eq2 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) right1 right2
  let eq3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) right1 right3
  eq1++eq2++eq3

getAppConstrains 2  pairId1 pairId2 pairId3 t1 t2 t3 = do
  let right1 = concat (getRightExpr pairId1 t1)
  let right2 = concat (getRightExpr pairId2 t2)
  let right3 = concat (getRightExpr pairId3 t3)
  let eq1 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) right1 (right2++right3)
  let left1 = concat (getLeftExpr pairId1 t1)
  let left2 = concat (getLeftExpr pairId2 t2)
  let left3 = concat (getLeftExpr pairId3 t3)
  let eq2 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) left1 left2
  let eq3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) left1 left3
  eq1++eq2++eq3

getAppConstrains _ _ _ _ _ _ _ = error "get app constrains error"


buildArgsConstrains :: Int -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildArgsConstrains leftOrRight pair1 pair2 = do
 let (UnfoldPair _ t1 _ _ pairId1 _) = pair1
 let (UnfoldPair _ t2 _ _ pairId2 _) = pair2
 let (TypePoint _ edges _) = t2
 let (TypeEdge _ typePoints) = (filter (\(TypeEdge index _) -> if index == ([leftOrRight]) then True else False ) edges) !! 0
 let leftArr = typePoints !! 0
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 buildEntail 1 pairId1 freeV1 1 pairId2 freeV2 (t1,leftArr)
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
  let eq3 = ifElseConstrain trueOrFalse leftOrRight pairId3 t3
  let rule = Rule (MkAnd ([r1,r2,eq3]++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

ifElseConstrain :: Bool -> Int -> Int -> TypePoint -> Expr
ifElseConstrain True 1 pairId t1 =ExprVar ( (concat (getLeftExpr pairId t1)) !! 0)
ifElseConstrain True 2 pairId t1 =ExprVar ( (concat (getRightExpr pairId t1)) !! 0)
ifElseConstrain False 1 pairId t1 =MkNot (ExprVar ( (concat(getLeftExpr pairId t1)) !! 0))
ifElseConstrain False 2 pairId t1 =MkNot (ExprVar ( (concat(getRightExpr pairId t1)) !! 0))
ifElseConstrain _ _ _ _ = error "true constrain error"

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
  let eq3 = generateBinary leftOrRight op pairId1 pairId2 pairId3 t1 t2 t3
  let rule = Rule (MkAnd ([r1,r2]++eq3++(concat eq2)++(concat eq1))) r3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()


generateBinary :: Int ->T.Binop -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinary 1 op pairId1 pairId2 pairId3 t1 t2 t3 = generateBinaryLeft op pairId1 pairId2 pairId3 t1 t2 t3
generateBinary 2 op pairId1 pairId2 pairId3 t1 t2 t3 = generateBinaryRight op pairId1 pairId2 pairId3 t1 t2 t3
generateBinary _ _ _ _ _ _ _ _ = error "generateBinary is wrong" 

generateBinaryLeft :: T.Binop -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinaryLeft op pairId1 pairId2 pairId3 t1 t2 t3 = do
  let leftExpr1 = concat (getLeftExpr pairId1 t1)
  let leftExpr2 = concat (getLeftExpr pairId2 t2)
  let leftExpr3 = concat (getLeftExpr pairId3 t3)
  let rightExpr1 = concat (getRightExpr pairId1 t1)
  let rightExpr2 = concat (getRightExpr pairId2 t2)
  let rightExpr3 = concat (getRightExpr pairId3 t3)
  let rE1EqrE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) rightExpr1 rightExpr3
  let rE2EqrE3 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) rightExpr2 rightExpr3
  let binary = getBinary op (ExprVar (leftExpr1!!0)) (ExprVar (leftExpr2!!0)) (ExprVar (leftExpr3!!0))
  (binary:(rE1EqrE3++rE2EqrE3))

generateBinaryRight :: T.Binop -> Int -> Int -> Int -> TypePoint -> TypePoint -> TypePoint -> [Expr]
generateBinaryRight op pairId1 pairId2 pairId3 t1 t2 t3 = do
  let leftExpr1 = concat (getLeftExpr pairId1 t1)
  let leftExpr2 = concat (getLeftExpr pairId2 t2)
  let leftExpr3 = concat (getLeftExpr pairId3 t3)
  let rightExpr1 = concat (getRightExpr pairId1 t1)
  let rightExpr2 = concat (getRightExpr pairId2 t2)
  let rightExpr3 = concat (getRightExpr pairId3 t3)
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
 

getPredicate :: [T.Var] -> TypePoint -> Int -> Int ->UnfoldState Expr
getPredicate freeVs t@(TypePoint _ _ typePointId) pairId indicator = do
  let leftExpr = concat (getLeftExpr pairId t)
  let rightExpr = concat (getRightExpr pairId t)
  allFreeVar <- mapM (getVarInSmt pairId indicator typePointId) freeVs
  let allExpr = leftExpr ++ rightExpr ++(concat allFreeVar)
  let sortList = map (\(Var _ sort)-> sort) allExpr
  let predicateName = ("R"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId))
  return $ ApplyFunction (Function predicateName sortList) (map (\x -> ParameterVar x) allExpr)
 

getLeftExpr :: Int -> TypePoint -> [[Var]]
getLeftExpr pairId (TypePoint (Pair left1 left2 _ _ _ _) _ typeId) = do
  let allLeft =zip (left1++left2) [1 .. ]
  map (oneExpr "exprLeft!" pairId 1 typeId) allLeft

getRightExpr :: Int -> TypePoint -> [[Var]]
getRightExpr pairId (TypePoint (Pair _ _ right1 right2 _ _) _ typeId) = do
  let allRight =zip (right1++right2) [1 .. ]
  map (oneExpr "exprRight!" pairId 1 typeId) allRight

oneExpr :: String -> Int -> Int -> Int -> (Type,Int) -> [Var]
oneExpr leftOrRight pairId indicator typePointId (t,index) = do
  let sorts = getSortFromType t
  let names = getVarName pairId indicator typePointId t (T.Var (leftOrRight++show(index)))
  zipWith (\n s -> Var n s) names sorts

getVarInSmt ::Int -> Int ->Int -> T.Var ->UnfoldState  [Var]
getVarInSmt pairId indicator typePointId v = do
  t <- getType (T.EVar v)
  let sorts = getSortFromType t
  let names = getVarName pairId indicator typePointId t v
  let varInSmt = zipWith (\n s -> Var n s) names sorts
  return varInSmt


getVarName pairId  indicator typePointId (TInt)  (T.Var name) = [name ++"@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)]
getVarName pairId  indicator typePointId (TBool)  (T.Var name)  = [name ++"@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)]
getVarName pairId  indicator typePointId (TList _)  (T.Var name) = do
 let name1 = name ++"cell@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)
 let name2 = name ++"length@"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)
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

buildEntails :: UnfoldPair -> UnfoldPair -> UnfoldState ()
buildEntails pair1@(UnfoldPair _ expressionV1 _ _ pairId1 _) pair2@(UnfoldPair _ expressionV2 _ _ pairId2 _) = do
 let indexMap = Map.fromList ([(1,1),(2,2)] )
 let pairs1 = getPairTypePoint expressionV1 expressionV2 [] [] indexMap
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 mapM (buildEntail 1 pairId1 freeV1 1 pairId2 freeV2) pairs1
 return ()

buildEntail :: Int -> Int ->[T.Var] -> Int -> Int ->[T.Var]->(TypePoint,TypePoint) -> UnfoldState ()
buildEntail indicator1 pairId1 freeV1 indicator2 pairId2 freeV2 (t1,t2) = do
  let (TypePoint _ _ typePointId1) = t1
  let (TypePoint _ _ typePointId2) = t2
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  let freeIn12 = filter (\x -> elem x freeV1) freeV2
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId2 indicator2 typePointId2) freeIn12
  let left1 = getLeftExpr pairId1 t1
  let left2 = getLeftExpr pairId2 t2
  let right1 = getRightExpr pairId1 t1
  let right2 = getRightExpr pairId2 t2
  let eq2 = zipWith (\e1 e2 -> MkEq (ExprVar e1) (ExprVar e2)) ((concat left1) ++ (concat right1)) ((concat left2) ++ (concat right2))
  let rule = Rule (MkAnd ([r1]++eq2++(concat eq1))) r2
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()
buildContextEntail :: UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextEntail pair1@(UnfoldPair contextV1 _ _ _ pairId1 _) pair2@(UnfoldPair contextV2 _ _ _ pairId2 _) = do
 freeV1 <- getAllFreeVar pair1
 freeV2 <- getAllFreeVar pair2
 r1 <- getPredicate freeV1 contextV1 pairId1 0
 r2 <- getPredicate freeV2 contextV2 pairId2 0
 let (TypePoint _ _ typePointId1) = contextV1
 let (TypePoint _ _ typePointId2) = contextV2
 let freeIn12 = filter (\x -> elem x freeV1) freeV2
 eq1 <- mapM (generateEq pairId1 0 typePointId1 pairId2 0 typePointId2) freeIn12
 let rule = Rule (MkAnd ([r1]++(concat eq1))) r2
 (TemporyResult number result typeEnv mapToFreeVar chc) <- get
 let newChc = add_rule rule chc
 put (TemporyResult number result typeEnv mapToFreeVar newChc)
 return ()

subTypeCheck :: Set.Set (TypePoint,TypePoint)-> Int -> Int -> Int -> Int -> [T.Var] -> [T.Var]-> TypePoint -> TypePoint ->UnfoldState (Set.Set (TypePoint,TypePoint))
subTypeCheck pairSet pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1 t2 = 
  if Set.member (t1,t2) pairSet then return $ pairSet
    else subTypeCheckNew pairSet pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1 t2

subTypeCheckNew :: Set.Set (TypePoint,TypePoint)-> Int -> Int -> Int -> Int ->[T.Var] -> [T.Var]-> TypePoint -> TypePoint ->UnfoldState (Set.Set (TypePoint,TypePoint))
subTypeCheckNew pairSet pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1@(TypePoint _ edges1 _) t2@(TypePoint _ edges2  _) = do
  let newPairSet = Set.insert (t1,t2) pairSet
  buildSubTypeRules pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1 t2
  let allPossiblePair = concat (map (\x -> map (\y -> (x,y)) edges2) edges1)
  let allValidPairs = filter (\((TypeEdge index1 _),(TypeEdge index2 _)) -> if index1 == index2 then True else False) allPossiblePair
  let leftPair = map (\((TypeEdge _ pairs1),(TypeEdge _ pairs2)) -> ((pairs1 !! 0),(pairs2 !! 0)) ) allValidPairs
  let rightPair = map (\((TypeEdge _ pairs1),(TypeEdge _ pairs2)) -> ((pairs1 !! 1),(pairs2 !! 1)) ) allValidPairs
  finalSet1 <- foldrM (\(t1,t2) oldSet -> subTypeCheck oldSet pairId2 indicator2 pairId1 indicator1 freeV2 freeV1 t2 t1) newPairSet leftPair
  finalSet2 <- foldrM (\(t1,t2) oldSet -> subTypeCheck oldSet pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1 t2 ) newPairSet leftPair
  return $ Set.union finalSet1 finalSet2

buildSubTypeRules ::  Int -> Int -> Int -> Int -> [T.Var] -> [T.Var]->TypePoint -> TypePoint ->UnfoldState ()
buildSubTypeRules  pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1@(TypePoint _ edges1 _) t2@(TypePoint _ edges2 _) = do
  if (length (edges1++edges2)) == 0 then buildRealSubType pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1 t2 else return ()

buildRealSubType ::  Int -> Int -> Int -> Int ->[T.Var] -> [T.Var]-> TypePoint -> TypePoint ->UnfoldState ()
buildRealSubType  pairId1 indicator1 pairId2 indicator2 freeV1 freeV2 t1@(TypePoint _ _ typePointId1) t2@(TypePoint _ _ typePointId2) = do
  r1 <- getPredicate freeV1 t1 pairId1 indicator1
  r2 <- getPredicate freeV2 t2 pairId2 indicator2
  let freeIn12 = filter (\x -> elem x freeV1) freeV2
  eq1 <- mapM (generateEq pairId1 indicator1 typePointId1 pairId2 indicator2 typePointId2) freeIn12
  let left1 = getLeftExpr pairId1 t1
  let left2 = getLeftExpr pairId2 t2
  let right1 = getRightExpr pairId1 t1
  let right2 = getRightExpr pairId2 t2
  let eq2 = zipWith (\e1 e2 -> MkEq (ExprVar e1) (ExprVar e2)) ((concat left1) ++ (concat right1)) ((concat left2) ++ (concat right2))
  let rule = Rule (MkAnd ([r1]++eq2++(concat eq1))) r2
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()

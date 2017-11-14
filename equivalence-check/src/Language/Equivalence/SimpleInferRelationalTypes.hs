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
  buildConstrainsForPair rootPair e1 e2
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
  buildContextForTrue 1 pair1 pair2
  pair3 <- constructUnfoldPair e3 e4
  buildContextForFalse 1 pair1 pair3
  buildIfStConstrains pair2 pair3 pair
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

buildContextForTrue :: Int ->UnfoldPair -> UnfoldPair -> UnfoldPair -> UnfoldState ()
buildContextForTrue leftOrRight (UnfoldPair contextV1 _ e1_1 e2_1 pairId1 _) (UnfoldPair _ expressionV e1_2 e2_2 pairId2 _) (UnfoldPair contextV2 _ e1_3 e2_3 pairId3 _) = do
  

buildBinaryConstrains :: Int -> T.Binop -> UnfoldPair -> UnfoldPair ->UnfoldPair -> UnfoldState ()
buildBinaryConstrains leftOrRight op pair1@(UnfoldPair _ expressionV1 e1_1 e2_1 pairId1 _) pair2@(UnfoldPair _ expressionV2 e1_2 e2_2 pairId2 _) pair3@(UnfoldPair _ expressionV3 e1_3 e2_3 pairId3 _) = do
  let r1@(Function _ sortList1) = getPredicate expressionV1 pairId1 1
  let r2@(Function _ sortList2) = getPredicate expressionV2 pairId2 1
  let r3@(Function _ sortList3) = getPredicate expressionV3 pairId3 1
  freeV1_1 <- getFreeV e1_1
  freeV2_1 <- getFreeV e2_1
  let (TypePoint types1 _ typeId1) = expressionV1
  let argsNames1 =  concat (zipWith (getVarName pairId1 1 typeId1) types1 ([(T.Var "expr1"),(T.Var "expr2")]++freeV1_1++freeV2_1))
  let var1 = zipWith (\name sort -> (Var name sort)) argsNames1 sortList1
  let r1AppVar1 = ApplyFunction r1 (map (\x -> ParameterVar x) var1)
  freeV1_2 <- getFreeV e1_2
  freeV2_2 <- getFreeV e2_2
  let (TypePoint types2 _ typeId2) = expressionV2
  let argsNames2 =  concat (zipWith (getVarName pairId2 1 typeId2) types2 ([(T.Var "expr1"),(T.Var "expr2")]++freeV1_2++freeV2_2))
  let var2 = zipWith (\name sort -> (Var name sort)) argsNames2 sortList2
  let r2AppVar2 = ApplyFunction r2 (map (\x -> ParameterVar x) var2)
  freeV1_3 <- getFreeV e1_3
  freeV2_3 <- getFreeV e2_3
  let (TypePoint types3 _ typeId3) = expressionV3
  let argsNames3 =  concat (zipWith (getVarName pairId3 1 typeId3) types3 ([(T.Var "expr1"),(T.Var "expr2")]++freeV1_3++freeV2_3))
  let var3 = zipWith (\name sort -> (Var name sort)) argsNames3 sortList3
  let r3AppVar3 = ApplyFunction r3 (map (\x -> ParameterVar x) var3)
  let shareBy1_3 = filter (\x -> elem x (freeV1_1++freeV1_2)) (freeV1_3 ++ freeV2_3)
  let shareBy2_3 = filter (\x -> elem x (freeV2_1++freeV2_2)) (freeV1_3 ++ freeV2_3)
  eq1 <- mapM (generateEq 1 pairId1 typeId1 1 pairId3 typeId3) shareBy1_3
  eq2 <- mapM (generateEq 1 pairId1 typeId1 1 pairId3 typeId3) shareBy1_3
  constrains <- generateBinary leftOrRight op pair1 pair2 pair3
  let smtExpr = (concat eq1) ++ (concat eq2)++constrains
  let rule = Rule (MkAnd ([r1AppVar1,r2AppVar2]++smtExpr)) r3AppVar3
  (TemporyResult number result typeEnv mapToFreeVar chc) <- get
  let newChc = add_rule rule chc
  put (TemporyResult number result typeEnv mapToFreeVar newChc)
  return ()


generateBinary :: Int -> T.Binop -> UnfoldPair -> UnfoldPair -> UnfoldPair ->UnfoldState [Expr]
generateBinary 1 op pair1 pair2 pair3 = generateBinaryLeft op pair1 pair2 pair3
generateBinary 2 op pair1 pair2 pair3 = generateBinaryRight op pair1 pair2 pair3
generateBinary _ _ _ _ _ = error "generateBinary is wrong" 

generateBinaryLeft ::T.Binop -> UnfoldPair -> UnfoldPair -> UnfoldPair ->UnfoldState [Expr]
generateBinaryLeft op (UnfoldPair _ expressionV1 e1_1 e2_1 pairId1 _) (UnfoldPair _ expressionV2 e1_2 e2_2 pairId2 _) (UnfoldPair _ expressionV3 e1_3 e2_3 pairId3 _) = do
  let (TypePoint types1 _ typeId1) = expressionV1
  let (TypePoint types2 _ typeId2) = expressionV2
  let (TypePoint types3 _ typeId3) = expressionV3
  let name1 = getVarName pairId1 1  typeId1 (types1 !! 1) (T.Var "expr2")
  let name2 = getVarName pairId2 1  typeId2 (types2 !! 1) (T.Var "expr2")
  let name3 = getVarName pairId3 1  typeId3 (types3 !! 1) (T.Var "expr2")
  let sort1 = getSortFromType (types1 !! 1)
  let sort2 = getSortFromType (types2 !! 1)
  let sort3 = getSortFromType (types3 !! 1)
  let var1 = zipWith (\ name sort ->  (Var name sort)) name1 sort1
  let var2 = zipWith (\ name sort ->  (Var name sort)) name2 sort2
  let var3 = zipWith (\ name sort ->  (Var name sort)) name3 sort3
  let eq1 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var2
  let eq2 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var3
  let name1_2 = getVarName pairId1 1  typeId1 (types1 !! 0) (T.Var "expr1")
  let name2_2 = getVarName pairId2 1  typeId2 (types2 !! 0) (T.Var "expr1")
  let name3_2 = getVarName pairId3 1  typeId3 (types3 !! 0) (T.Var "expr1")
  let sort1_2 = getSortFromType (types1 !! 0)
  let sort2_2 = getSortFromType (types2 !! 0)
  let sort3_2 = getSortFromType (types3 !! 0)
  let var1_2 = zipWith (\ name sort ->  (Var name sort)) name1_2 sort1_2
  let var2_2 = zipWith (\ name sort ->  (Var name sort)) name2_2 sort2_2
  let var3_2 = zipWith (\ name sort ->  (Var name sort)) name3_2 sort3_2
  let binConstrains = getBinary op (ExprVar (var1_2!!0)) (ExprVar (var2_2!!0)) (ExprVar (var3_2!!0))
  return (binConstrains:(eq1++eq2))

generateBinaryRight ::T.Binop -> UnfoldPair -> UnfoldPair -> UnfoldPair ->UnfoldState [Expr]
generateBinaryRight op (UnfoldPair _ expressionV1 e1_1 e2_1 pairId1 _) (UnfoldPair _ expressionV2 e1_2 e2_2 pairId2 _) (UnfoldPair _ expressionV3 e1_3 e2_3 pairId3 _) = do
  let (TypePoint types1 _ typeId1) = expressionV1
  let (TypePoint types2 _ typeId2) = expressionV2
  let (TypePoint types3 _ typeId3) = expressionV3
  let name1 = getVarName pairId1 1 typeId1 (types1 !! 0) (T.Var "expr1")
  let name2 = getVarName pairId2 1 typeId2 (types2 !! 0) (T.Var "expr1")
  let name3 = getVarName pairId3 1 typeId3 (types3 !! 0) (T.Var "expr1")
  let sort1 = getSortFromType (types1 !! 0)
  let sort2 = getSortFromType (types2 !! 0)
  let sort3 = getSortFromType (types3 !! 0)
  let var1 = zipWith (\ name sort ->  (Var name sort)) name1 sort1
  let var2 = zipWith (\ name sort ->  (Var name sort)) name2 sort2
  let var3 = zipWith (\ name sort ->  (Var name sort)) name3 sort3
  let eq1 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var2
  let eq2 = zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var3
  let name1_2 = getVarName pairId1 1 typeId1 (types1 !! 1) (T.Var "expr2")
  let name2_2 = getVarName pairId2 1 typeId2 (types2 !! 1) (T.Var "expr2")
  let name3_2 = getVarName pairId3 1 typeId3 (types3 !! 1) (T.Var "expr2")
  let sort1_2 = getSortFromType (types1 !! 1)
  let sort2_2 = getSortFromType (types2 !! 1)
  let sort3_2 = getSortFromType (types3 !! 1)
  let var1_2 = zipWith (\ name sort ->  (Var name sort)) name1_2 sort1_2
  let var2_2 = zipWith (\ name sort ->  (Var name sort)) name2_2 sort2_2
  let var3_2 = zipWith (\ name sort ->  (Var name sort)) name3_2 sort3_2
  let binConstrains = getBinary op (ExprVar (var1_2!!0)) (ExprVar (var2_2!!0)) (ExprVar (var3_2!!0))
  return (binConstrains:(eq1++eq2))

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
generateEq indicator1 pairId1 typeId1 indicator2 pairId2 typeId2 var = do
  t1 <- getType (T.EVar var)
  let name1 = getVarName pairId1 indicator1 typeId1 t1 var
  let name2 = getVarName pairId1 indicator2 typeId2 t1 var
  let sorts = getSortFromType t1
  let var1 = zipWith (\ name sort ->  (Var name sort)) name1 sorts
  let var2 = zipWith (\ name sort ->  (Var name sort)) name2 sorts
  return (zipWith (\v1 v2 -> MkEq (ExprVar v1) (ExprVar v2)) var1 var2)

unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge = undefined

unfoldBothEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldBothEdge = undefined

buildConstrainsForPair :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState ()
buildConstrainsForPair = undefined

getPredicate ::  TypePoint -> Int -> Int -> Function
getPredicate  (TypePoint types _ typePointId) pairId indicator = do
  let sortList =concat (map (\t-> getSortFromType t) types)
  Function ("R"++(show pairId)++"@"++(show indicator)++"@"++(show typePointId)) sortList


getVarName ::Int -> Int -> Int -> Type -> T.Var ->  [String]
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





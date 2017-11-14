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
unfoldLeftEdge pair (T.EBin ob e1 e2) e3 = do
  pair1 <- constructUnfoldPair e1 e3
  pair2 <- constructUnfoldPair e1 e3
  buildBinaryConstrains 1 ob pair1 pair2 pair
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

unfoldRightEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldRightEdge = undefined

unfoldBothEdge :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState UnfoldEdge
unfoldBothEdge = undefined

buildConstrainsForPair :: UnfoldPair -> T.CoreExpr -> T.CoreExpr -> UnfoldState ()
buildConstrainsForPair = undefined

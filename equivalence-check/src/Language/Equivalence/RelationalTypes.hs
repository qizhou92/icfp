module Language.Equivalence.RelationalTypes where

import Language.Equivalence.TypeInference
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

data TypePoint = TypePoint [Type] [TypeEdge] Int
  deriving (Show,Eq,Ord)

data TypeConstructor = TypeArr | TypePlus | TypeProduct | TypeFix
  deriving (Show,Eq,Ord)

data TypeEdge = TypeEdge TypeConstructor [Int] [TypePoint]
  deriving (Show,Eq,Ord)

--- type of left expr, right expr, left free variables, and right free variables
data Pair = Pair Type Type [Type] [Type]
  deriving (Show,Eq,Ord)

data ConstructResult = ConstructResult Int  (Map.Map Pair TypePoint)
  deriving (Show,Eq,Ord)

type ConstructState a = (State ConstructResult) a

constructRelationalDag :: Pair -> TypePoint
constructRelationalDag pair = evalState (constructPoint pair) (ConstructResult 0 (Map.empty))

constructPoint :: Pair -> ConstructState TypePoint
constructPoint pair = do
  (ConstructResult _ result) <- get
  if Map.member pair result then return (result Map.! pair)
    else constructNewPoint pair

constructNewPoint :: Pair -> ConstructState TypePoint
constructNewPoint pair@(Pair exprT1 exprT2 freeT1 freeT2) = do
 let types = exprT1:(exprT2:(freeT1++freeT2))
 arrTypeEdges <- constructEdges TypeArr pair  (getTypeIndex isTypeArr types)
 plusTypeEdges <- constructEdges TypePlus pair (getTypeIndex isTypePlus types)
 productTypeEdges <- constructEdges TypeProduct pair (getTypeIndex isTypeProduct types)
 fixTypeEdges <- constructEdges TypeFix pair  (getTypeIndex isTypeFix types)
 (ConstructResult number result) <- get
 let newTypePoint = TypePoint types (arrTypeEdges ++ plusTypeEdges ++ productTypeEdges ++ fixTypeEdges) number
 put (ConstructResult (number+1) (Map.insert pair newTypePoint result))
 return newTypePoint

constructEdges :: TypeConstructor -> Pair -> [Int] -> ConstructState [TypeEdge]
constructEdges typeConstructor types index = do
 let allPossibleIndexs = powerSet index
 mapM (constructEdge typeConstructor types) allPossibleIndexs

constructEdge :: TypeConstructor -> Pair -> [Int] -> ConstructState TypeEdge
constructEdge TypeFix (Pair exprT1 exprT2 freeT1 freeT2) index = do
 let types = exprT1:(exprT2:(freeT1++freeT2))
 let length1 = length freeT1
 let typeWithIndex = zip types [1 .. ]
 let newTypes = map (getNewTypes getFixType (Set.fromList index)) typeWithIndex
 let (headList,newFreeT2) = splitAt (2+length1) newTypes
 let (exprList,newFreeT1) = splitAt 2 headList
 let newExprT1 = exprList !! 0
 let newExprT2 = exprList !! 1 
 typePoint <- constructPoint (Pair newExprT1 newExprT2 newFreeT1 newFreeT2)
 return (TypeEdge TypeFix index [typePoint])

constructEdge TypeArr (Pair (TArr t1 t2) exprT2 freeT1 freeT2) [1] = do
  typePoint1 <- constructPoint (Pair t1 exprT2 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair t2 exprT2 (t1:freeT1) freeT2 )
  return (TypeEdge TypeArr [1] [typePoint1,typePoint2])

constructEdge TypeArr (Pair exprT1 (TArr t1 t2) freeT1 freeT2) [2] = do
  typePoint1 <- constructPoint (Pair exprT1 t1 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair exprT1 t2 freeT1 (t1:freeT2))
  return (TypeEdge TypeArr [2] [typePoint1,typePoint2])

constructEdge TypeArr (Pair (TArr t1 t2) (TArr t3 t4) freeT1 freeT2) [1,2] = do 
  typePoint1 <- constructPoint (Pair t1 t3 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair t2 t4 (t1:freeT1) (t3:freeT2))
  return (TypeEdge TypeArr [1,2] [typePoint1,typePoint2])
  
constructEdge TypePlus pair index = constructEdgeBinaryConstructor TypePlus getTPlusLeft getTPlusRight pair index
constructEdge TypeProduct pair index = constructEdgeBinaryConstructor TypeProduct getTProductLeft getTProductRight pair index
constructEdge _ _ _ = error "constructEdge in relational type didnt mtach"

constructEdgeBinaryConstructor :: TypeConstructor -> (Type -> Type) -> (Type -> Type) -> Pair -> [Int] -> ConstructState TypeEdge
constructEdgeBinaryConstructor typeConstructor leftF rightF (Pair exprT1 exprT2 freeT1 freeT2) index = do
 let types = exprT1:(exprT2:(freeT1++freeT2))
 let length1 = length freeT1
 let typeWithIndex = zip types [1 .. ]
 let newTypes1 = map (getNewTypes leftF (Set.fromList index)) typeWithIndex
 let newTypes2 = map (getNewTypes rightF (Set.fromList index)) typeWithIndex
 let (headList_1,newFreeT2_1) = splitAt (2+length1) newTypes1
 let (exprList_1,newFreeT1_1) = splitAt 2 headList_1
 let newExprT1_1 = exprList_1 !! 0
 let newExprT2_1 = exprList_1 !! 1
 let (headList_2,newFreeT2_2) = splitAt (2+length1) newTypes2
 let (exprList_2,newFreeT1_2) = splitAt 2 headList_2
 let newExprT1_2 = exprList_2 !! 0
 let newExprT2_2 = exprList_2 !! 1  
 typePoint1 <- constructPoint (Pair newExprT1_1 newExprT2_1 newFreeT1_1 newFreeT2_1)
 typePoint2 <- constructPoint (Pair newExprT1_2 newExprT2_2 newFreeT1_2 newFreeT2_2)
 return (TypeEdge typeConstructor index [typePoint1,typePoint2])


getNewTypes :: (Type -> Type) -> (Set.Set Int) -> (Type,Int) -> Type
getNewTypes replaceF indexs (theType,theIndex) = do
 if (Set.member theIndex indexs) then (replaceF theType)
  else theType 

getTypeIndex :: (Type -> Bool) -> [Type] -> [Int]
getTypeIndex filterF list = do
 let result1 = zip (map filterF list) [1 ..]
 map (\(_,y) -> y) (filter (\(x,_) -> x ) result1)

isTypeVar :: Type -> Bool
isTypeVar (TVar _ ) = True
isTypeVar _ = False

isTypeArr :: Type -> Bool
isTypeArr (TArr _ _) = True
isTypeArr _ = False


isTypePlus :: Type -> Bool
isTypePlus (TPlus _ _)  = True
isTypePlus _ = False

isTypeProduct :: Type -> Bool
isTypeProduct (TProduct _ _) = True
isTypeProduct _ = False

isTypeFix :: Type -> Bool
isTypeFix (TFix _ _) = True
isTypeFix _ = False

getFixType :: Type -> Type
getFixType (TFix _ t) = t
getFixType _ = error "get fix type error"

getTArrLeft :: Type -> Type
getTArrLeft (TArr t _) = t
getTArrLeft _ = error "get TArr left error"

getTArrRight :: Type -> Type
getTArrRight (TArr _ t) = t
getTArrRight _ = error "get TArr right error"

getTPlusLeft :: Type -> Type
getTPlusLeft (TPlus t _) = t
getTPlusLeft _ = error "get TPLus left error"

getTPlusRight :: Type -> Type
getTPlusRight (TPlus _ t) = t
getTPlusRight _ = error "get TPlus right error"

getTProductLeft :: Type -> Type
getTProductLeft (TProduct t _) = t
getTProductLeft _ = error "get TProduct left error"

getTProductRight :: Type -> Type
getTProductRight (TProduct _ t) = t
getTProductRight _ = error "getTProduct right error"

powerSet :: [Int] -> [[Int]]
powerSet (x:xs) = do
 let set = powerSet xs
 (map (x:) set) ++ set
powerSet [] = []



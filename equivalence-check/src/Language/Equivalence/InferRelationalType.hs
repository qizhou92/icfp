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
data ConstructResult = ConstructResult Int  (Map.Map [Type] TypePoint)
  deriving (Show,Eq,Ord)

type ConstructState a = (State ConstructResult) a

constructRelationalDag :: [Type] -> TypePoint
constructRelationalDag types = evalState (constructPoint types) (ConstructResult 0 (Map.empty))

constructPoint :: [Type] -> ConstructState TypePoint
constructPoint types = do
  (ConstructResult _ result) <- get
  if Map.member types result then return (result Map.! types)
    else constructNewPoint types

constructNewPoint :: [Type] -> ConstructState TypePoint
constructNewPoint types = do
 arrTypeEdges <- constructEdges TypeArr types  (getTypeIndex isTypeArr types)
 plusTypeEdges <- constructEdges TypePlus types (getTypeIndex isTypePlus types)
 productTypeEdges <- constructEdges TypeProduct types (getTypeIndex isTypeProduct types)
 fixTypeEdges <- constructEdges TypeFix types  (getTypeIndex isTypeFix types)
 (ConstructResult number result) <- get
 let newTypePoint = TypePoint types (arrTypeEdges ++ plusTypeEdges ++ productTypeEdges ++ fixTypeEdges) number
 put (ConstructResult (number+1) (Map.insert types newTypePoint result))
 return newTypePoint

constructEdges :: TypeConstructor -> [Type] -> [Int] -> ConstructState [TypeEdge]
constructEdges typeConstructor types index = do
 let allPossibleIndexs = powerSet index
 mapM (constructEdge typeConstructor types) allPossibleIndexs

constructEdge :: TypeConstructor -> [Type] -> [Int] -> ConstructState TypeEdge
constructEdge TypeFix types index = do
 let typeWithIndex = zip types [1 .. ]
 let newTypes = map (getNewTypes getFixType (Set.fromList index)) typeWithIndex
 typePoint <- constructPoint newTypes
 return (TypeEdge TypeFix index [typePoint])
constructEdge TypeArr types index = constructEdgeBinaryConstructor TypeArr getTArrLeft getTArrRight types index
constructEdge TypePlus types index = constructEdgeBinaryConstructor TypePlus getTPlusLeft getTPlusRight types index
constructEdge TypeProduct types index = constructEdgeBinaryConstructor TypeProduct getTProductLeft getTProductRight types index

constructEdgeBinaryConstructor :: TypeConstructor -> (Type -> Type) -> (Type -> Type) -> [Type] -> [Int] -> ConstructState TypeEdge
constructEdgeBinaryConstructor typeConstructor leftF rightF types index = do
 let typeWithIndex = zip types [1 .. ]
 let newTypes1 = map (getNewTypes leftF (Set.fromList index)) typeWithIndex
 let newTypes2 = map (getNewTypes rightF (Set.fromList index)) typeWithIndex
 typePoint1 <- constructPoint newTypes1
 typePoint2 <- constructPoint newTypes2
 return (TypeEdge typeConstructor index [typePoint1,typePoint2])


getNewTypes :: (Type -> Type) -> (Set.Set Int) -> (Type,Int) -> Type
getNewTypes replaceF indexs (theType,theIndex) = do
 if (Set.member theIndex indexs) then (replaceF theType)
  else theType 

getTypeIndex :: (Type -> Bool) -> [Type] -> [Int]
getTypeIndex filterF list = do
 let result1 = zip (map filterF list) [1 ..]
 map (\(x,y) -> y) (filter (\(x,y) -> x ) result1)

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

getTArrLeft :: Type -> Type
getTArrLeft (TArr t _) = t

getTArrRight :: Type -> Type
getTArrRight (TArr _ t) = t

getTPlusLeft :: Type -> Type
getTPlusLeft (TPlus t _) = t

getTPlusRight :: Type -> Type
getTPlusRight (TPlus _ t) = t

getTProductLeft :: Type -> Type
getTProductLeft (TProduct t _) = t

getTProductRight :: Type -> Type
getTProductRight (TProduct _ t) = t

powerSet :: [Int] -> [[Int]]
powerSet (x:xs) = do
 let set = powerSet xs
 (map (x:) set) ++ set
powerSet [] = []



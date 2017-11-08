module Language.Equivalence.RelationalTypes where

import Language.Equivalence.TypeInference
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map

type TV = String
data TypeWithId = TVarId TV Int
                 |TIntId Int
                 |TBoolId Int
                 |TArrId TypeWithId TypeWithId Int
                 |TPlusId TypeWithId TypeWithId Int
                 |TProductId TypeWithId TypeWithId Int
                 |TFixId TV TypeWithId Int
                 |TNilId Int
  deriving (Show,Eq,Ord)

typeToTypeWithId :: Type -> TypeWithId
typeToTypeWithId t1 = evalState (buildTypeWithId t1) 0

buildTypeWithId ::Type -> (State Int) TypeWithId
buildTypeWithId (TVar name) = do
  idnumber <- get
  put (idnumber+1)
  return (TVarId name idnumber)

buildTypeWithId (TInt) = do
  idnumber <- get
  put (idnumber+1)
  return (TIntId idnumber)

buildTypeWithId (TBool) = do
  idnumber <- get
  put (idnumber+1)
  return (TBoolId idnumber)

buildTypeWithId (TArr t1 t2) = do
  typeWithId1 <- buildTypeWithId t1
  typeWithId2 <- buildTypeWithId t2
  idnumber <- get
  put (idnumber+1)
  return (TArrId typeWithId1 typeWithId2 idnumber)

buildTypeWithId (TPlus t1 t2) = do
  typeWithId1 <- buildTypeWithId t1
  typeWithId2 <- buildTypeWithId t2
  idnumber <- get
  put (idnumber+1)
  return (TPlusId typeWithId1 typeWithId2 idnumber)

buildTypeWithId (TProduct t1 t2) = do
  typeWithId1 <- buildTypeWithId t1
  typeWithId2 <- buildTypeWithId t2
  idnumber <- get
  put (idnumber+1)
  return (TProductId typeWithId1 typeWithId2 idnumber)

buildTypeWithId (TFix name t1) = do
  typeWithId <- buildTypeWithId t1
  idnumber <- get
  put (idnumber+1)
  return (TFixId name typeWithId idnumber)

buildTypeWithId (TNil) = do
  idnumber <- get
  put (idnumber+1)
  return (TNilId idnumber)

buildTypeWithId (TList _) = error "buildTypeWithId should not have type list"

data TypePoint = TypePoint [TypeWithId] [TypeEdge] Int
  deriving (Eq,Ord)

instance Show TypePoint where
   show = typePointPrettyPrint 

typePointPrettyPrint :: TypePoint -> String
typePointPrettyPrint t1 = do
  let allTypePoints = Set.toList (collectAllTypePoint t1)
  foldr (\x y-> y ++ "\n" ++ (singleTypePointPrettyPrint x))  "" allTypePoints

collectAllTypePoint :: TypePoint -> Set.Set TypePoint
collectAllTypePoint t@(TypePoint _ edges _) = 
  Set.union (Set.unions (map (\(TypeEdge _ _ points) -> (Set.unions (map collectAllTypePoint points))) edges)) (Set.singleton t)

singleTypePointPrettyPrint :: TypePoint -> String
singleTypePointPrettyPrint (TypePoint types edges idn) = 
 "Id:" ++ (show idn) ++ "   Types:" ++ (show types)++"\n"++ (foldr (\x y ->y ++"\n" ++ (typeEdgePrettyPrint x)) "Edges:" edges)

data TypeConstructor = TypeArr | TypePlus | TypeProduct | TypeFix
  deriving (Show,Eq,Ord)

data TypeEdge = TypeEdge TypeConstructor [Int] [TypePoint]
  deriving (Eq,Ord)

instance Show TypeEdge where
  show = typeEdgePrettyPrint 

typeEdgePrettyPrint (TypeEdge ruleName index points) = do
  let partString ="Edge:" ++ (show ruleName) ++ (foldr (\x y ->y ++ (show x) ++ ",") "   Index:" index)
  let secondParts = (foldr (\(TypePoint _ _ idn) y ->y ++ (show idn) ++ ",") "Points:" points)
  partString ++ secondParts
--- type of left expr, right expr, left free variables, and right free variables
data Pair = Pair TypeWithId TypeWithId [TypeWithId] [TypeWithId]
  deriving (Show,Eq,Ord)

data ConstructResult = ConstructResult Int  (Map.Map Pair TypePoint)
  deriving (Show,Eq,Ord)

type ConstructState a = (State ConstructResult) a

constructVersionSpace :: Type->Type->[Type] -> [Type] -> TypePoint
constructVersionSpace exprT1 exprT2 freeT1 freeT2 = do
 let exprT1WithId = typeToTypeWithId exprT1
 let exprT2WithId = typeToTypeWithId exprT2
 let freeT1WithId = map typeToTypeWithId freeT1
 let freeT2WithId = map typeToTypeWithId freeT2
 constructRelationalDag (Pair exprT1WithId exprT2WithId freeT1WithId freeT2WithId)

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

constructEdge TypeArr (Pair (TArrId t1 t2 _) exprT2 freeT1 freeT2) [1] = do
  typePoint1 <- constructPoint (Pair t1 exprT2 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair t2 exprT2 (t1:freeT1) freeT2 )
  return (TypeEdge TypeArr [1] [typePoint1,typePoint2])

constructEdge TypeArr (Pair exprT1 (TArrId t1 t2 _) freeT1 freeT2) [2] = do
  typePoint1 <- constructPoint (Pair exprT1 t1 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair exprT1 t2 freeT1 (t1:freeT2))
  return (TypeEdge TypeArr [2] [typePoint1,typePoint2])

constructEdge TypeArr (Pair (TArrId t1 t2 _) (TArrId t3 t4 _) freeT1 freeT2) [1,2] = do 
  typePoint1 <- constructPoint (Pair t1 t3 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair t2 t4 (t1:freeT1) (t3:freeT2))
  return (TypeEdge TypeArr [1,2] [typePoint1,typePoint2])
  
constructEdge TypePlus pair index = constructEdgeBinaryConstructor TypePlus getTPlusLeft getTPlusRight pair index
constructEdge TypeProduct pair index = constructEdgeBinaryConstructor TypeProduct getTProductLeft getTProductRight pair index
constructEdge _ _ _ = error "constructEdge in relational type didnt mtach"

constructEdgeBinaryConstructor :: TypeConstructor -> (TypeWithId -> TypeWithId) -> (TypeWithId -> TypeWithId) -> Pair -> [Int] -> ConstructState TypeEdge
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


getNewTypes :: (TypeWithId -> TypeWithId) -> (Set.Set Int) -> (TypeWithId,Int) -> TypeWithId
getNewTypes replaceF indexs (theType,theIndex) = do
 if (Set.member theIndex indexs) then (replaceF theType)
  else theType 

getTypeIndex :: (TypeWithId -> Bool) -> [TypeWithId] -> [Int]
getTypeIndex filterF list = do
 let result1 = zip (map filterF list) [1 ..]
 map (\(_,y) -> y) (filter (\(x,_) -> x ) result1)

isTypeVar :: TypeWithId -> Bool
isTypeVar (TVarId _ _) = True
isTypeVar _ = False

isTypeArr :: TypeWithId -> Bool
isTypeArr (TArrId _ _ _) = True
isTypeArr _ = False


isTypePlus :: TypeWithId -> Bool
isTypePlus (TPlusId _ _ _)  = True
isTypePlus _ = False

isTypeProduct :: TypeWithId -> Bool
isTypeProduct (TProductId _ _ _) = True
isTypeProduct _ = False

isTypeFix :: TypeWithId -> Bool
isTypeFix (TFixId _ _ _) = True
isTypeFix _ = False

getFixType :: TypeWithId -> TypeWithId
getFixType (TFixId _ t _) = t
getFixType _ = error "get fix type error"

getTArrLeft :: TypeWithId -> TypeWithId
getTArrLeft (TArrId t _ _) = t
getTArrLeft _ = error "get TArr left error"

getTArrRight :: TypeWithId -> TypeWithId
getTArrRight (TArrId _ t _) = t
getTArrRight _ = error "get TArr right error"

getTPlusLeft :: TypeWithId -> TypeWithId
getTPlusLeft (TPlusId t _ _) = t
getTPlusLeft _ = error "get TPLus left error"

getTPlusRight :: TypeWithId -> TypeWithId
getTPlusRight (TPlusId _ t _) = t
getTPlusRight _ = error "get TPlus right error"

getTProductLeft :: TypeWithId -> TypeWithId
getTProductLeft (TProductId t _ _) = t
getTProductLeft _ = error "get TProduct left error"

getTProductRight :: TypeWithId -> TypeWithId
getTProductRight (TProductId _ t _) = t
getTProductRight _ = error "getTProduct right error"

powerSet :: [Int] -> [[Int]]
powerSet ([x]) = [[x]]
powerSet (x:xs) = do
 let set = powerSet xs
 (map (x:) set) ++ set
powerSet [] = []



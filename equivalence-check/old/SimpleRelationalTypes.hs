module Language.Equivalence.SimpleRelationalTypes where
import qualified Language.Equivalence.Types as T
import Control.Monad.State
import Language.Equivalence.Expr
import qualified Data.Map as Map
import qualified Data.Set as Set

data GivenTypePoint = GivenTypePoint [GivenTypeEdge] [Var] Expr
  deriving (Show,Eq,Ord)

data GivenTypeEdge = GivenTypeEdge [Int] [GivenTypePoint]
  deriving (Show,Eq,Ord)

data TypePoint = TypePoint Pair [TypeEdge] Int
  deriving (Show,Eq,Ord)

data TypeEdge = TypeEdge [Int] [TypePoint]
  deriving (Show,Eq,Ord)

data Pair = Pair [T.Type] [T.Type] [T.Type] [T.Type] [T.Type] [T.Type]
  deriving (Show,Eq,Ord)

data ConstructResult = ConstructResult Int  (Map.Map Pair TypePoint)
  deriving (Show,Eq,Ord)

type ConstructState a = (State ConstructResult) a

collectAllTypePoint :: TypePoint -> Set.Set TypePoint
collectAllTypePoint t@(TypePoint _ edges _) = 
  Set.union (Set.unions (map (\(TypeEdge _ points) -> (Set.unions (map collectAllTypePoint points))) edges)) (Set.singleton t)

constructVersionSpace :: [T.Type] -> [T.Type] ->[T.Type] -> [T.Type] -> TypePoint
constructVersionSpace exprT1 exprT2 freeT1 freeT2 = 
 constructRelationalDag (Pair [] [] exprT1 exprT2 freeT1 freeT2)

constructRelationalDag :: Pair -> TypePoint
constructRelationalDag pair = evalState (constructPoint pair) (ConstructResult 0 (Map.empty))

constructPoint :: Pair -> ConstructState TypePoint
constructPoint pair = do
  (ConstructResult _ result) <- get
  if Map.member pair result then return (result Map.! pair)
    else constructNewPoint pair

constructNewPoint :: Pair -> ConstructState TypePoint
constructNewPoint pair@(Pair _ _ exprT1 exprT2 _ _) = do
 arrTypeEdges <- constructEdges pair (getTypeIndex isTypeArr (exprT1++exprT2) )
 (ConstructResult number result) <- get
 let newTypePoint = TypePoint pair arrTypeEdges number
 put (ConstructResult (number+1) (Map.insert pair newTypePoint result))
 return newTypePoint

constructEdges :: Pair -> [Int] -> ConstructState [TypeEdge]
constructEdges pair index = do
 let allPossibleIndexs = powerSet index
 mapM (constructEdge pair) allPossibleIndexs

constructEdge :: Pair -> [Int] -> ConstructState TypeEdge
constructEdge (Pair left right [(T.TArr t1 t2)] exprT2 freeT1 freeT2) [1] = do
  typePoint1 <- constructPoint (Pair left right [t1] exprT2 freeT1 freeT2)
  typePoint2 <- constructPoint (Pair ([t1]++left) right [t2] exprT2 freeT1 freeT2)
  return (TypeEdge [1] [typePoint1,typePoint2])

constructEdge (Pair left right [] [(T.TArr t1 t2)] freeT1 freeT2) [1] = do
  typePoint1 <- constructPoint (Pair left right [ ] [t1] freeT1 freeT2)
  typePoint2 <- constructPoint (Pair left (right++[t1]) [ ] [t2] freeT1 freeT2)
  return (TypeEdge [1] [typePoint1,typePoint2])

constructEdge (Pair left right exprT1 [(T.TArr t1 t2)] freeT1 freeT2) [2] = do
  typePoint1 <- constructPoint (Pair left right exprT1 [t1] freeT1 freeT2)
  typePoint2 <- constructPoint (Pair left (right++[t1]) exprT1 [t2] freeT1 freeT2)
  return (TypeEdge [2] [typePoint1,typePoint2])

constructEdge (Pair left right [(T.TArr t1 t2)] [(T.TArr t3 t4)] freeT1 freeT2) [1,2] = do 
  typePoint1 <- constructPoint (Pair left right [t1] [t3] freeT1 freeT2)
  typePoint2 <- constructPoint (Pair (left++[t1]) (right++[t3]) [t2] [t4] (freeT1) (freeT2))
  return (TypeEdge [1,2] [typePoint1,typePoint2])

constructEdge _ _  = error "in simple relational types, it should not has other edges"

getTypeIndex :: (T.Type -> Bool) -> [T.Type] -> [Int]
getTypeIndex filterF list = do
 let result1 = zip (map filterF list) [1 ..]
 map (\(_,y) -> y) (filter (\(x,_) -> x ) result1)
 
isTypeArr :: T.Type -> Bool
isTypeArr (T.TArr _ _) = True
isTypeArr _ = False


powerSet :: [Int] -> [[Int]]
powerSet list = filter (\x -> if (length x) == 0 then False else True) (powerSet1 list)

powerSet1 :: [Int] -> [[Int]]
powerSet1 ([x]) = [[x]]
powerSet1 (x:xs) = do
 let set = powerSet xs
 (map (x:) set) ++ set
powerSet1 [] = []
{-# LANGUAGE QuasiQuotes #-}
module Language.RHORT where

import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Data (Data)
import           Data.Tree
import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.List as L

import           Language.Types
import           Grammar
import qualified Formula as F

-- RHORT is relatioanl high order refinement type
data RHORT = RHORT
-- getRHORT returns the DAG the represent the relational high order refinement type
  {  getRHORT :: RHORTNode
-- getBasicTypes returns all basic types for the vector of expressions
   , getBasicTypes :: [Type]
   , getVarLength :: Int
  } deriving (Show, Read, Eq, Data)

-- RHORTNode is the node of the RHORT DAG, get predicate returns the nonterminal if it
-- is a leaf node, getEdges returns the outgoing edge of this node
data RHORTNode = RHORTNode 
   {  getPredicate    :: (Maybe Nonterminal) 
    , getEdges        :: [RHORTEdge]
   } deriving (Show,Read,Eq,Data)

-- RHORTEdge is the directed edge of RHORT DAG, get indexs return the index list of this unwinding
-- getNodes returns the RHORT nodes this edge points to.
data RHORTEdge = RHORTEdge
    {  getIndexs :: [Int]
     , getNodes  :: [RHORTNode]
    } deriving (Show,Read,Eq,Data)

-- |Given a relational higher order refinement type, the unique id of the expression and the corresponding index, 
-- fetch the formula (variable) which represents the value of the expression.
valueOf :: Int -> Int -> RHORT -> F.Var
valueOf uniqueId index rhort = 
  let t = safeGet "valueOf given the index over the basic length" index (getBasicTypes rhort)
    in case t of
         TBool -> mkVarArg ("arg#"++(show uniqueId)) (TBool, lastIndex t)
         TInt  -> mkVarArg ("arg#"++(show uniqueId)) (TBool, lastIndex t)
         _ -> error "this type is not supported (argumentOf in RHORT)"  
  where
    lastIndex t = 
       let flattedTypes = flattenType t
           prims = filter isPrimitiveType flattedTypes
        in (length prims)

-- | Given a relational higher order refinement type, the unique id of the expression and the corresponding index, 
-- fetch the formula (variable) which represents the first argument of the expression and its type is primitive type.
argumentOf :: Int -> Int -> RHORT -> F.Var
argumentOf uniqueId index rhort = 
  let t = safeGet "argumentOf given the index over the basic length" index (getBasicTypes rhort)
    in case t of
          TArr t1 _ -> mkVarArg ("arg#"++(show uniqueId)) (t1,1)
          _ -> error "this type is not supported (argumentOf in RHORT)"  

-- FlatType is the type the collect all first order argument into one type
data FlatType = 
  FlatType Int [Type]
 |FlatTypeArr Int FlatType FlatType
 deriving (Show,Eq)


-- wheater the given flat type is a primitive type
isPrimFlatType :: FlatType -> Bool
isPrimFlatType (FlatType _ _) = True
isPrimFlatType _ = False

-- convert the type to the flat type

getFlatType :: Type -> FlatType
getFlatType t= evalState (convertToFlatType t) 1

convertToFlatType :: Type ->State Int FlatType
convertToFlatType t = do
 let flattenTypes = flattenType t
 let (basicTypes,highOrderTypes) = L.partition isPrimitiveType flattenTypes
 uniqueTypeId <- get
 put (uniqueTypeId + 1)
 let flatType = FlatType uniqueTypeId basicTypes
 if (null highOrderTypes) then (return $ flatType)
       else do
              allFlattenTypes <- mapM convertToFlatType highOrderTypes
              constructFlatType (allFlattenTypes++[flatType])

constructFlatType :: [FlatType] ->State Int FlatType
constructFlatType [] = error "construct flat type cannot accept empty list"
constructFlatType ([x]) = return x
constructFlatType (x:xs) = do
 uniqueTypeId <- get
 put (uniqueTypeId + 1)
 secondIdType <- constructFlatType xs
 return (FlatTypeArr uniqueTypeId x secondIdType)

flattenType :: Type -> [Type]
flattenType = \case
  TInt -> [TInt]
  TBool -> [TBool]
  TArr s t -> s : flattenType t
  t -> error ("error in flattenType " ++ show t)



-- | Whether or not the given index type is primitive.
isPrim :: Int -> RHORT -> Bool
isPrim index rhort = 
  let t = safeGet "is Prim get index over the length of list" index (getBasicTypes rhort)
    in isPrimitiveType t


freshType :: MonadState Int m => [(Var,Type)] -> [Type] -> [Int] -> m RHORT
freshType  = undefined


getDAGNode :: MonadState Int m => [(Var,FlatType)] -> [Int] -> [FlatType] -> StateT (Map [Int] RHORTNode) m RHORTNode
getDAGNode  varPairs exprIds exprTypes = do
  let varTypes = map (\(_,t) -> t ) varPairs
  let indexList = map getFlatTypeId (varTypes ++ exprTypes)
  visitedMap <- get
  case (M.lookup indexList visitedMap) of
    Just dagNode -> return dagNode
    Nothing -> freshDAGNode varPairs exprIds exprTypes
  where
    getFlatTypeId flatType = case flatType of
      FlatType i _ -> i
      FlatTypeArr i _ _ -> i

freshDAGNode ::  MonadState Int m => [(Var,FlatType)] -> [Int] -> [FlatType] -> StateT (Map [Int] RHORTNode) m RHORTNode
freshDAGNode varPairs exprIds exprTypes = do
  let varTypes = map (\(_,t) -> t) varPairs
  let flatTypeList = varTypes ++ exprTypes 
  let possibleIndexs = filter (\(t,_) ->not (isPrimFlatType t)) (zip flatTypeList [0 .. ]) 
  if (null possibleIndexs)
    then do 
           let varName = map(\(v,_) -> v) varPairs
           predicate <- (lift (mkPredicate flatTypeList varName exprIds))
           return (RHORTNode (Just predicate) [])
    else do 
          let allPossibleIndex = getAllPossibleIndex (map (\(_,i)->i) possibleIndexs)
          allEdges <- mapM (constructEdge varPairs exprIds exprTypes) allPossibleIndex
          return (RHORTNode Nothing allEdges)

-- each list is an index, which only contains one integer
getAllPossibleIndex :: [Int] -> [[Int]]
getAllPossibleIndex [] = []
getAllPossibleIndex (x:xs) = ([x]):(getAllPossibleIndex xs)


constructEdge :: MonadState Int m => [(Var,FlatType)] -> [Int] -> [FlatType] -> [Int] -> StateT (Map [Int] RHORTNode) m RHORTEdge
constructEdge varPairs exprIds exprTypes edgeIndexs= do
  let varTypes = map (\(_,t) -> t) varPairs
  let varName = map(\(v,_) -> v) varPairs
  let flatTypeList = varTypes ++ exprTypes
  let leftFlatTypeList = foldr getLeftFlatType flatTypeList  edgeIndexs
  let rightFlatTypeList =foldr getRightFlatType flatTypeList edgeIndexs
  let (leftVarType,leftExprType) = L.splitAt (length varTypes) leftFlatTypeList
  let (rightVarType,rightExprType) = L.splitAt (length varTypes) rightFlatTypeList
  leftNode <- getDAGNode (zip varName leftVarType) exprIds leftExprType
  rightNode <- getDAGNode (zip varName rightVarType) exprIds rightExprType
  return (RHORTEdge edgeIndexs [leftNode,rightNode])
  where
    getLeftFlatType index flatTypeList  = case (safeGet "cannot get this type from getLeftFlatType" index flatTypeList) of
      FlatTypeArr _ t1 _ -> let (left,right) = L.splitAt (index+1) flatTypeList
                            in ((init left) ++ [t1] ++ right)
      _ -> error "primitive type cannot get left type"

    getRightFlatType index flatTypeList  = case (safeGet "cannot get this type from getLeftFlatType" index flatTypeList) of
      FlatTypeArr _ _ t1 -> let (left,right) = L.splitAt (index+1) flatTypeList
                            in ((init left) ++ [t1] ++ right)
      _ -> error "primitive type cannot get right type"




mkPredicate :: MonadState Int m => [FlatType] -> [Var] -> [Int] ->m Nonterminal
mkPredicate flatTypes varName uniqueIds = do
  idNumber <- get
  let (aVarTypes,exprTypes) = L.splitAt (length varName) flatTypes
  let varListArg = concat (zipWith mkVarArgs varName aVarTypes)
  let exprListArg = concat (zipWith mkExprArgs uniqueIds exprTypes)
  let nonterminal = Nonterminal (ConcreteID idNumber) (varListArg++exprListArg)
  put (idNumber + 1)
  return nonterminal

mkVarArgs :: Var -> FlatType -> [F.Var]
mkVarArgs _ (FlatTypeArr _ _ _) = error "mkVarArgs would not accept flat type that is not all primitive"
mkVarArgs (Var name) (FlatType _ typeList) = map (mkVarArg name) (zip typeList [1 ..])

mkVarArg :: String -> (Type,Int) -> F.Var
mkVarArg name (t,uniqueId) = case t of
  TInt -> F.Var (name++"/"++(show uniqueId)) F.Int
  TBool -> F.Var (name++"/"++(show uniqueId)) F.Bool
  _ -> error "it is not an primitive type  free vars (mkVarArg in RHORT)"

mkExprArgs :: Int -> FlatType -> [F.Var]
mkExprArgs _ (FlatTypeArr _ _ _) = error "mkExprArgs would not accept flat type that is not all primitive"
mkExprArgs uniqueId (FlatType _ typeList) = map (mkVarArg ("arg#"++(show uniqueId))) (zip typeList [1 ..])


-- | Split a relational high order refinement type at the arrow position with index
split :: Int -> RHORT -> (RHORT,RHORT)
split index rhort = case (safeGet "split is over index" index (getBasicTypes rhort)) of
  TArr t1 t2 ->  let dagNode = getRHORT rhort
                     varLength = getVarLength rhort
                     validEdges = filter (\(RHORTEdge indexs _) -> indexs == [varLength + index]) (getEdges dagNode)
                     nodes = getNodes (safeGet "split should find one valid edge" 0 validEdges)
                     leftNode = safeGet "split should find left node" 0 nodes
                     rightNode = safeGet "split should find right node" 1 nodes
                     types = getBasicTypes rhort
                     (leftTypes,rightTypes) = L.splitAt (index+1) types
                     newLeftTypes = (L.init leftTypes) ++ [t1] ++ rightTypes
                     newRightTypes = (L.init leftTypes) ++ [t2] ++ rightTypes
                     leftRHORT = (RHORT leftNode newLeftTypes varLength)
                     rightRHORT = (RHORT rightNode newRightTypes varLength)
                   in (leftRHORT,rightRHORT)
  _ ->  error "not a supported type (split in RHORT)"

-- | print an given the message is current list is less then the index
safeGet :: String -> Int -> [a] -> a
safeGet message index list = 
  if (length list) <= index then (error message)
    else (list !! index)

{-# LANGUAGE QuasiQuotes #-}
module Language.RHORT where

import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad
import           Data.Data (Data)
import           Data.Tree
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import Data.Foldable (toList)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.List as L
import Control.Lens

import           Language.Types
import           Grammar
import qualified Formula as F

import Debug.Trace

-- RHORT is relatioanl high order refinement type
data RHORT = RHORT
  -- getRHORT returns the DAG the represent the relational high order refinement type
  {  getRHORT :: RHORTNode
  -- getAvailable returns the all basic types for the vecotr of available
   , getAvailable ::  [Type]
  -- getBasicTypes returns all basic types for the vector of expressions
   , getBasicTypes :: [Type]
  } deriving (Show, Read, Eq, Ord, Data)

-- RHORTNode is the node of the RHORT DAG, get predicate returns the nonterminal if it
-- is a leaf node, getEdges returns the outgoing edge of this node
data RHORTNode = RHORTNode
  { getPredicate :: Maybe ([Int], Nonterminal)
  , getEdges :: [RHORTEdge]
  } deriving (Show, Read, Eq, Ord, Data)

-- RHORTEdge is the directed edge of RHORT DAG, get indexs return the index list of this unwinding
-- getNodes returns the RHORT nodes this edge points to.
data RHORTEdge = RHORTEdge
  { getIndexs :: [Int]
  , getNodes  :: [RHORTNode]
  } deriving (Show, Read, Eq, Ord, Data)

-- |Given a relational higher order refinement type, the unique id of the expression and the corresponding index, 
-- fetch the formula (variable) which represents the value of the expression.
valueOf :: Int -> Int -> RHORT -> F.Var
valueOf uniqueId index rhort = 
  let t = safeGet "valueOf given the index over the basic length" index (getBasicTypes rhort)
      prims = filter isPrimitiveType (flattenType t)
      lastT = L.last prims
    in case lastT of
          TBool -> mkVarArg ("arg#" ++ show uniqueId) (TBool, (length prims))
          TInt  -> mkVarArg ("arg#" ++ show uniqueId) (TInt, (length prims))
          _ -> error "this type is not supported (argumentOf in RHORT)"

-- | Given a relational higher order refinement type, the unique id of the expression and the corresponding index, 
-- fetch the formula (variable) which represents the first argument of the expression and its type is primitive type.
argumentOf :: Int -> Int -> RHORT -> F.Var
argumentOf uniqueId index rhort =
  let t = safeGet "argumentOf given the index over the basic length" index (getBasicTypes rhort)
  in case t of
    TArr t1 _ -> mkVarArg ("arg#" ++ show uniqueId) (t1,1)
    _ -> error "this type is not supported (argumentOf in RHORT)"  

-- FlatType is the type the collect all first order argument into one type
data FlatType
  = FlatType Int [Type]
  | FlatTypeArr Int FlatType FlatType
  deriving (Show, Read, Eq, Ord, Data)


-- Whether the given flat type is a primitive type.
isPrimFlatType :: FlatType -> Bool
isPrimFlatType (FlatType _ _) = True
isPrimFlatType _ = False

-- Convert a type to a flat type.
getFlatType :: Type -> FlatType
getFlatType t = evalState (convertToFlatType t) 1

convertToFlatType :: Type -> State Int FlatType
convertToFlatType t = do
  let flattenTypes = flattenType t
  let (basicTypes,highOrderTypes) = L.partition isPrimitiveType flattenTypes
  uniqueTypeId <- get
  put (uniqueTypeId + 1)
  let flatType = FlatType uniqueTypeId basicTypes
  if null highOrderTypes
  then return flatType
  else do
    allFlattenTypes <- mapM convertToFlatType highOrderTypes
    constructFlatType (allFlattenTypes++[flatType])

constructFlatType :: [FlatType] -> State Int FlatType
constructFlatType [] = error "construct flat type cannot accept empty list"
constructFlatType [x] = return x
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

freshType :: MonadState Int m => Set (Var, Type) -> Seq Type -> Seq Int -> m RHORT
freshType  varTypesSet types uniqueIds = do
  let flattenTypeList = map (\(v,t)->(v,(getFlatType t))) (S.toList varTypesSet)
  let exprTypeList = map getFlatType (toList types)
  rhortNode <- evalStateT (getDAGNode flattenTypeList (toList uniqueIds) exprTypeList) M.empty
  let basicTypes = toList types
  let varTypes = map (\(_,t) -> t) (S.toList varTypesSet)
  return (RHORT rhortNode varTypes basicTypes)

fetchVarComponents :: Var -> Type -> [F.Var]
fetchVarComponents v t = mkVarArgs v (getFlatType t)

fetchExprComponents :: ExprID -> Type -> [F.Var]
fetchExprComponents i t= mkExprArgs i (getFlatType t)

getDAGNode :: MonadState Int m
           => [(Var, FlatType)] -> [Int] -> [FlatType]
           -> StateT (Map [Int] RHORTNode) m RHORTNode
getDAGNode  varPairs exprIds exprTypes = do
  let varTypes = map snd varPairs
  let indexList = map getFlatTypeId (varTypes ++ exprTypes)
  visitedMap <- get
  case M.lookup indexList visitedMap of
    Just dagNode -> return dagNode
    Nothing -> do
      newDAGNode <- freshDAGNode varPairs exprIds exprTypes
      put (M.insert indexList newDAGNode visitedMap)
      return newDAGNode

getFlatTypeId :: FlatType -> Int
getFlatTypeId = \case
  FlatType i _ -> i
  FlatTypeArr i _ _ -> i

freshDAGNode ::  MonadState Int m => [(Var,FlatType)] -> [Int] -> [FlatType] -> StateT (Map [Int] RHORTNode) m RHORTNode
freshDAGNode varPairs exprIds exprTypes = do
  let varTypes = map snd varPairs
  let flatTypeList = varTypes ++ exprTypes 
  let possibleIndexs = filter (\(t,_) ->not (isPrimFlatType t)) (zip flatTypeList ([0 .. ]::[Int])) 
  if null possibleIndexs
  then do
    let varName = map fst varPairs
    predicate <- lift (mkPredicate flatTypeList varName exprIds)
    let flatIdList = map getFlatTypeId flatTypeList
    return (RHORTNode (Just (flatIdList, predicate)) [])
  else do 
    let allPossibleIndex = getAllPossibleIndex (map snd possibleIndexs)
    allEdges <- mapM (constructEdge varPairs exprIds exprTypes) allPossibleIndex
    return (RHORTNode Nothing allEdges)

-- each list is an index, which only contains one integer
getAllPossibleIndex :: [Int] -> [[Int]]
getAllPossibleIndex = map (: [])

constructEdge :: MonadState Int m => [(Var,FlatType)] -> [Int] -> [FlatType] -> [Int] -> StateT (Map [Int] RHORTNode) m RHORTEdge
constructEdge varPairs exprIds exprTypes edgeIndexs= do
  let varTypes = map snd varPairs
  let varName = map fst varPairs
  let flatTypeList = varTypes ++ exprTypes
  let leftFlatTypeList  = foldr getLeftFlatType flatTypeList  edgeIndexs
  let rightFlatTypeList = foldr getRightFlatType flatTypeList edgeIndexs
  let (leftVarType,leftExprType) = L.splitAt (length varTypes) leftFlatTypeList
  let (rightVarType,rightExprType) = L.splitAt (length varTypes) rightFlatTypeList
  leftNode <- getDAGNode (zip varName leftVarType) exprIds leftExprType
  rightNode <- getDAGNode (zip varName rightVarType) exprIds rightExprType
  return (RHORTEdge edgeIndexs [leftNode,rightNode])
  where
    getLeftFlatType index flatTypeList =
      case safeGet "cannot get this type from getLeftFlatType" index flatTypeList of
        FlatTypeArr _ t1 _ ->
          let (left,right) = L.splitAt (index+1) flatTypeList
          in (init left ++ [t1] ++ right)
        _ -> error "primitive type cannot get left type"

    getRightFlatType index flatTypeList =
      case safeGet "cannot get this type from getLeftFlatType" index flatTypeList of
        FlatTypeArr _ _ t1 ->
          let (left,right) = L.splitAt (index+1) flatTypeList
          in (init left ++ [t1] ++ right)
        _ -> error "primitive type cannot get right type"

mkPredicate :: MonadState Int m => [FlatType] -> [Var] -> [Int] -> m Nonterminal
mkPredicate flatTypes varName uniqueIds = do
  idNumber <- get
  traceM (show idNumber ++ " " ++ show varName)
  let (aVarTypes,exprTypes) = L.splitAt (length varName) flatTypes
  let varListArg = concat (zipWith mkVarArgs varName aVarTypes)
  let exprListArg = concat (zipWith mkExprArgs uniqueIds exprTypes)
  let nonterminal = Nonterminal (ConcreteID idNumber) (varListArg++exprListArg)
  put (idNumber + 1)
  return nonterminal

mkVarArgs :: Var -> FlatType -> [F.Var]
mkVarArgs _ FlatTypeArr{} = error "mkVarArgs would not accept flat type that is not all primitive"
mkVarArgs (Var name) (FlatType _ typeList) = map (mkVarArg name) (zip typeList [1 ..])

mkVarArg :: String -> (Type,Int) -> F.Var
mkVarArg name (t,uniqueId) = case t of
  TInt -> F.Var (name ++ "/" ++ show uniqueId) F.Int
  TBool -> F.Var (name ++ "/" ++ show uniqueId) F.Bool
  _ -> error "it is not an primitive type  free vars (mkVarArg in RHORT)"

mkExprArgs :: Int -> FlatType -> [F.Var]
mkExprArgs _ FlatTypeArr{} = error "mkExprArgs would not accept flat type that is not all primitive"
mkExprArgs uniqueId (FlatType _ typeList) = map (mkVarArg ("arg#" ++ show uniqueId)) (zip typeList [1 ..])


-- | Split a relational high order refinement type at the arrow position with index
split :: Int -> RHORT -> (RHORT,RHORT)
split index rhort = case safeGet "split is over index" index (getBasicTypes rhort) of
  TArr t1 t2 -> 
    let dagNode = getRHORT rhort
        availableVar = getAvailable rhort
        varLength = length (availableVar)
        validEdges = filter (\(RHORTEdge indexs _) -> indexs == [index++varLength]) (getEdges dagNode)
        nodes = getNodes (safeGet "split should find one valid edge" 0 validEdges)
        leftNode = safeGet "split should find left node" 0 nodes
        rightNode = safeGet "split should find right node" 1 nodes
        types = getBasicTypes rhort
        (leftTypes,rightTypes) = L.splitAt (index+1) types
        newLeftTypes = L.init leftTypes ++ [t1] ++ rightTypes
        newRightTypes = L.init leftTypes ++ [t2] ++ rightTypes
        leftRHORT = RHORT leftNode availableVar newLeftTypes 
        rightRHORT = RHORT rightNode availableVar newRightTypes
    in (leftRHORT, rightRHORT)
  _ ->  error "not a supported type (split in RHORT)"


-- given three rhrot, condition, oldContext, and newContext to build the subtype relations
ctxtJoin :: MonadWriter [Rule] m => F.Expr -> RHORT -> RHORT -> RHORT -> m ()
ctxtJoin constraint condition oldContext newContext = do
  let leafNode = getAnLeafNode (getRHORT condition)
  let nonTerminal = safeGetNonterminal leafNode
  constrain' constraint [nonTerminal] [oldContext] newContext

getAnLeafNode :: RHORTNode -> RHORTNode
getAnLeafNode node =
  let edges = getEdges node
  in if null edges then node
     else getAnLeafNode (safeGet "there is no node in get an leftNode" 0 (getNodes (head edges)))

-- given three rhrot, abs,arg, and app to build the subtype relations
-- when arg is prim
appJoin :: MonadWriter [Rule] m => Int -> F.Expr -> RHORT -> RHORT -> RHORT -> m ()
appJoin index constraint absRhort argRhort appRhort = do
  let rightMostNode1 = getRightMostNode index (getRHORT absRhort)
  let rightMostNode2 = getRightMostNode index (getRHORT appRhort)
  visitedSet <- witnessNode constraint [] [rightMostNode1, getRHORT argRhort] rightMostNode2
  -- _ <- execStateT (witnessNode' constraint [] [getRHORT absRhort, getRHORT argRhort] (getRHORT appRhort)) visitedSet
  return ()

--getRightMostNode respect the idnex
getRightMostNode :: Int -> RHORTNode -> RHORTNode
getRightMostNode index node =
  let edges = getEdges node
      oneEdge = filter (\edge -> getIndexs edge == [index]) edges
  in if length oneEdge == 0 then node
       else if length oneEdge == 1 then getRightMostNode index (safeGet "there is no right node" 1 (getNodes (oneEdge !! 0)))
          else error "there is error in get rightMostNode"

constrain :: MonadWriter [Rule] m => F.Expr -> [RHORT] -> RHORT -> m ()
constrain e = constrain' e []

-- given two HORT has same structure and the constraint, build the
-- subtype relations between two HORT
constrain' :: MonadWriter [Rule] m => F.Expr -> [Nonterminal] -> [RHORT] -> RHORT -> m ()
constrain' constraint fixTerminals bodys headNode = do
  _ <- witnessNode constraint fixTerminals (map getRHORT bodys) (getRHORT headNode)
  return ()

-- given two RHORT has same structure, build the subtype relations between two RHORT
subtype :: MonadWriter [Rule] m => RHORT -> RHORT -> m ()
subtype rhort1 = constrain' (F.LBool True) [] [rhort1]

-- given a set of HORTNode, get there predicates
getPredicates :: [RHORTNode] -> [Nonterminal]
getPredicates = map safeGetNonterminal

safeGetNonterminal :: RHORTNode -> Nonterminal
safeGetNonterminal node = case getPredicate node of
  Just (_,nonterminal) -> nonterminal
  Nothing -> error "there is no nonterminal to get"


-- TODO:  needs to get varlist not set to equall
buildConstrains :: F.Expr ->[Nonterminal] -> [Nonterminal] -> Nonterminal -> Rule
buildConstrains constraint fixTerminals bodys headN = 
 let varsLists = map (\(Nonterminal _ vars)->vars) bodys
     Nonterminal _ headVars = headN
     equalExprs =
       traceShow (toListOf F.vars constraint) $
       F.manyAnd (map (buildEqExpr (toListOf F.vars constraint) headVars) varsLists)
 in Rule L headN (equalExprs `F.mkAnd` constraint) (fixTerminals ++ bodys)

buildEqExpr :: [F.Var] -> [F.Var] -> [F.Var] -> F.Expr
buildEqExpr fVars vars1 vars2 =
  let list1 = filter (`notElem` fVars) vars1
      list2 = filter (`notElem` fVars) vars2
  in F.manyAnd (zipWith (\x y -> F.mkEql (view F.varType x) (F.V x) (F.V y)) list1 list2)


-- given the witnessNode position to build the corresponding constrains and return the visited Node
witnessNode :: MonadWriter [Rule] m => F.Expr ->[Nonterminal] -> [RHORTNode] -> RHORTNode -> m (Set RHORTNode) 
witnessNode constraint fixTerminals bodys node = execStateT (witnessNode' constraint fixTerminals bodys node) S.empty

witnessNode' :: MonadWriter [Rule] m => F.Expr ->[Nonterminal] -> [RHORTNode] -> RHORTNode -> StateT (Set RHORTNode) m ()
witnessNode' constraint fixTerminals bodys node = do
  visitedNodes <- get
  if S.member node visitedNodes then return ()
  else do
    put (S.insert node visitedNodes)
    case getPredicate node of
      Just (_, nonterminal) ->lift (tell [buildConstrains constraint fixTerminals (getPredicates bodys) nonterminal])
      Nothing -> do
        let headEdges = getEdges node
        let validEdgesList = map (sameEdges (map getEdges bodys)) headEdges
        let leftNodesList = map getLeftNodes validEdgesList 
        let rightNodesList = map getRightNodes validEdgesList
        let leftNodes = getLeftNodes headEdges
        let rightNodes = getRightNodes headEdges
        _ <- zipWithM (witnessNode' constraint fixTerminals) leftNodesList leftNodes
        _ <- zipWithM (witnessNode' constraint fixTerminals) rightNodesList rightNodes
        return ()

-- get the left side nodes based on the pair of given edges
getLeftNodes :: [RHORTEdge] -> [RHORTNode]
getLeftNodes = map getLeftNode
  where getLeftNode edge = safeGet "there is no left node" 0 (getNodes edge)

-- get the right side nodes based on the pair of given edges
getRightNodes :: [RHORTEdge] -> [RHORTNode]
getRightNodes = map getRightNode
  where getRightNode edge = safeGet "there is no right node" 1 (getNodes edge)

-- given a list of lists of edges, and the same edges, choose the edges has the same indexs
sameEdges :: [[RHORTEdge]] -> RHORTEdge -> [RHORTEdge]
sameEdges listOfEdges headEdge =
  let indexs = getIndexs headEdge
  in map (safeFind indexs) listOfEdges

safeFind :: [Int] -> [RHORTEdge] -> RHORTEdge
safeFind indexs edges =
  let oneEdge = filter (\edge -> getIndexs edge == indexs) edges
  in if length oneEdge == 1 then head oneEdge
  else error "there is not right number of edge match the index"


-- | print an given the message is current list is less then the index
safeGet :: String -> Int -> [a] -> a
safeGet message index list =
  if length list <= index
  then error message
  else list !! index

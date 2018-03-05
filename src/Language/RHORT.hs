{-# LANGUAGE QuasiQuotes #-}
module Language.RHORT where

import           Control.Arrow
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.List as L
import           Data.Foldable (toList, foldrM)
import Control.Lens

import           Language.Types
import           Grammar
import qualified Formula as F

-- RHORT is relatioanl high order refinement type
data RHORT = RHORT
  -- refinementDAG returns the DAG the represent the relational high order refinement type
  {  refinementDAG :: RefinementDAG
  -- getAvailable returns the all basic types for the vecotr of available
   , getAvailable ::  [Type]
  -- getBasicTypes returns all basic types for the vector of expressions
   , getBasicTypes :: Seq Type
  } deriving (Show, Read, Eq, Ord, Data)

-- RefinementDAG is the node of the RHORT DAG, get predicate returns the nonterminal if it
-- is a leaf node, getEdges returns the outgoing edge of this node
data RefinementDAG
  = SimpleRHORT (Seq Int) Nonterminal
  | CompositeRHORT [RHORTEdge]
  deriving (Show, Read, Eq, Ord, Data)

getEdges :: RefinementDAG -> [RHORTEdge]
getEdges = \case
  SimpleRHORT{} -> Empty
  CompositeRHORT es -> es

-- RHORTEdge is the directed edge of RHORT DAG, get indexs return the index list of this unwinding
-- getNodes returns the RHORT nodes this edge points to.
data RHORTEdge = RHORTEdge
  { getIndexs :: [Int]
  , getNodes  :: [RefinementDAG]
  } deriving (Show, Read, Eq, Ord, Data)

-- | Given a relational higher order refinement type, the unique id of the
-- expression and the corresponding index, fetch the formula (variable) which
-- represents the value of the expression.
valueOf :: Int -> Int -> RHORT -> F.Var
valueOf uniqueId idx rhort =
  let t = safeGet "valueOf given the index over the basic length" idx (getBasicTypes rhort)
      prims = filter isPrimitiveType (flattenType t)
  in case L.last prims of
       TBool -> mkBoundVar uniqueId TBool (length prims)
       TInt  -> mkBoundVar uniqueId TInt (length prims)
       _ -> error "this type is not supported (argumentOf in RHORT)"

-- | Given a relational higher order refinement type, the unique id of the
-- expression and the corresponding index, fetch the formula (variable) which
-- represents the first argument of the expression and its type is primitive
-- type.
argumentOf :: Int -> Int -> RHORT -> F.Var
argumentOf uniqueId idx rhort =
  let t = safeGet "argumentOf given the index over the basic length" idx (getBasicTypes rhort)
  in case t of
    TArr t1 _ -> mkBoundVar uniqueId t1 1
    _ -> error "this type is not supported (argumentOf in RHORT)"

-- FlatType is the type the collect all first order argument into one type
data FlatType
  = FlatType Int [Type]
  | FlatTypeArr Int FlatType FlatType
  deriving (Show, Read, Eq, Ord, Data)

getFlatTypeId :: FlatType -> Int
getFlatTypeId = \case
  FlatType i _ -> i
  FlatTypeArr i _ _ -> i

-- Whether the given flat type is a primitive type.
isPrimFlatType :: FlatType -> Bool
isPrimFlatType = \case
  FlatType{} -> True
  _ -> False

flatTypeArgument :: FlatType -> Maybe FlatType
flatTypeArgument = \case
  FlatTypeArr _ _ t -> Just t
  _ -> Nothing

flatTypeApplicand :: FlatType -> Maybe FlatType
flatTypeApplicand = \case
  FlatTypeArr _ t _ -> Just t
  _ -> Nothing

increment :: MonadState Int m => m Int
increment = state (\x -> (x, x+1))

-- Convert a type to a flat type.
mkFlatType :: Type -> FlatType
mkFlatType ty = evalState (go ty) 1
  where
    go :: Type -> State Int FlatType
    go t = do
      let (basicTs, hoTs) = L.partition isPrimitiveType (flattenType t)
      -- Construct the type which represents all primitive types in the given signature.
      flatType <- FlatType <$> increment <*> pure basicTs
      -- Recursively construct flat types for the non-primitive types in the signature
      -- and construct arrow types between them.
      foldrM (\t1 t2 -> FlatTypeArr <$> increment <*> go t1 <*> pure t2)
        flatType hoTs

flattenType :: Type -> [Type]
flattenType = \case
  TInt -> [TInt]
  TBool -> [TBool]
  TArr s t -> s : flattenType t
  t -> error ("error in flattenType " ++ show t)

-- | Whether or not the given index type is primitive.
isPrim :: Int -> RHORT -> Bool
isPrim idx rhort =
  let t = safeGet "is Prim get index over the length of list" idx (getBasicTypes rhort)
  in isPrimitiveType t

freshType :: MonadState Int m => Set (Var, Type) -> Seq Type -> Seq ExprID -> m RHORT
freshType varTypesSet types uniqueIds = do
  let flattenTypeList = map (second mkFlatType) (S.toList varTypesSet)
  let exprTypes = fmap mkFlatType types
  dag <- evalStateT (mkTypeDAG flattenTypeList uniqueIds exprTypes) M.empty
  let varTypes = map snd (S.toList varTypesSet)
  return (RHORT dag varTypes types)

fetchVarComponents :: Var -> Type -> [F.Var]
fetchVarComponents v t = mkVarArgs v (mkFlatType t)

fetchExprComponents :: ExprID -> Type -> [F.Var]
fetchExprComponents i t= mkExprArgs i (mkFlatType t)

mkTypeDAG :: MonadState Int m
          => [(Var, FlatType)]
          -> Seq ExprID
          -> Seq FlatType
          -> StateT (Map (Seq Int) RefinementDAG) m RefinementDAG
mkTypeDAG varPairs exprIds exprTypes =
  let indexList = fmap getFlatTypeId flatTypes
  in M.lookup indexList <$> get >>= \case
    Just dagNode -> return dagNode
    Nothing -> do
      newDAGNode <- freshDAGNode
      modify (M.insert indexList newDAGNode)
      return newDAGNode
  where
    varName = map fst varPairs
    varTypes = map snd varPairs
    flatTypes = Seq.fromList varTypes <> exprTypes

    freshDAGNode = do
      let possibleIndexes =
            zip (toList flatTypes) ([0..] :: [Int])
            & filter (not . isPrimFlatType . fst)
            & map snd
      case possibleIndexes of
        Empty -> do
          predicate <- lift (mkPredicate flatTypes varName exprIds)
          let flatIds = fmap getFlatTypeId flatTypes
          return (SimpleRHORT flatIds predicate)
        -- To construct a composite rhort, we have to continue building
        -- the dag by looking a potential children.
        _ -> CompositeRHORT <$> traverse (mkEdge . (: [])) possibleIndexes

    mkEdge edgeIdxs = do
      leftNode  <- mkChild flatTypeApplicand
      rightNode <- mkChild flatTypeArgument
      return (RHORTEdge edgeIdxs [leftNode, rightNode])
      where
        mkChild f = do
          let childTypes = foldr (unfoldChild f) flatTypes edgeIdxs
          let (childVarType,childExprType) = Seq.splitAt (length varTypes) childTypes
          mkTypeDAG (zip varName (toList childVarType)) exprIds childExprType

        unfoldChild f idx ts =
          case f (safeGet "cannot get this type from unfoldChild" idx flatTypes) of
            Just t -> Seq.update idx t ts
            Nothing -> error "primitive type cannot get indexed type"

mkPredicate :: MonadState Int m => Seq FlatType -> [Var] -> Seq ExprID -> m Nonterminal
mkPredicate flatTypes varName uniqueIds = do
  idNumber <- increment
  let (aVarTypes, exprTypes) = Seq.splitAt (length varName) flatTypes
  let varListArg = concat (zipWith mkVarArgs varName (toList aVarTypes))
  let exprListArg = concat (zipWith mkExprArgs (toList uniqueIds) (toList exprTypes))
  return $ Nonterminal (ConcreteID idNumber) (varListArg ++ exprListArg)

mkVarArgs :: Var -> FlatType -> [F.Var]
mkVarArgs _ FlatTypeArr{} = error "`mkVarArgs` does not accept non-primitive flat types."
mkVarArgs (Var name) (FlatType _ typeList) = zipWith (mkVarArg name) typeList [1 ..]

mkExprArgs :: Int -> FlatType -> [F.Var]
mkExprArgs _ FlatTypeArr{} = error "`mkExprArgs` does notaccept non-primitive flat types."
mkExprArgs uniqueId (FlatType _ typeList) = zipWith (mkBoundVar uniqueId) typeList [1 ..]

mkVarArg :: String -> Type -> Int -> F.Var
mkVarArg name t uniqueId = case t of
  TInt -> F.Var (name ++ "/" ++ show uniqueId) F.Int
  TBool -> F.Var (name ++ "/" ++ show uniqueId) F.Bool
  t -> error (show t ++ " is not an primitive type (mkVarArg in RHORT).")

mkBoundVar :: Int -> Type -> Int -> F.Var
mkBoundVar uid = mkVarArg ("arg#" ++ show uid)

split :: Int -> RHORT -> (RHORT,RHORT)
split idx rhort = case safeGet "split is over index" idx (getBasicTypes rhort) of
  TArr t1 t2 ->
    ( child "split should find left node"  0 t1
    , child "split should find right node" 1 t2
    )
  _ ->  error "not a supported type (split in RHORT)"
  where
    availableVar = getAvailable rhort
    varLength = length availableVar
    validEdges = filter (\(RHORTEdge idxs _) -> idxs == [idx+varLength])
      (getEdges (refinementDAG rhort))
    types = getBasicTypes rhort
    nodes = getNodes (safeGet' "split should find one valid edge" 0 validEdges)

    child msg idx' t =
      let node = safeGet' msg idx' nodes
          newTs = Seq.update idx t types
      in RHORT node availableVar newTs

-- given the new var, the id of this lambada expression, the index of this expression
-- the varHort, oldContext Hort, and newContext Hort to build the subtype relations
addNewVarIntoContext :: MonadWriter [Rule] m => Var -> Int -> Int -> RHORT -> RHORT -> RHORT -> m ()
addNewVarIntoContext newVar uniqueId idx varHort oldContext newContext = do
  let samePairNodes = pairDagsAtIdx idx (refinementDAG varHort) (refinementDAG newContext)
  let rightPairs = map (first getAnLeafNode) samePairNodes
  let types = getOrderOfFlattenType (mkFlatType (Seq.index (getBasicTypes varHort) idx) )
  _ <- zipWithM (buildConstrainForAddNewVar newVar uniqueId idx (refinementDAG oldContext)) types rightPairs
  return () 

buildConstrainForAddNewVar :: MonadWriter [Rule] m => Var -> Int -> Int -> RefinementDAG -> FlatType  -> (RefinementDAG,RefinementDAG)  -> m ()
buildConstrainForAddNewVar var uniqueId idx oldContext t (newVar,newContext) = do
  let vcs = mkVarArgs var t
  let ecs = mkExprArgs uniqueId t
  let f = F.manyAnd (zipWith (\v1 v2 -> [F.expr|@v1 = @v2|]) vcs ecs)
  _ <- witnessNode f [safeGetNonterminal newVar] [oldContext] newContext
  return ()

pairDagsAtIdx :: Int -> RefinementDAG -> RefinementDAG -> [(RefinementDAG,RefinementDAG)]
pairDagsAtIdx idx t1 t2 =
  let validEdges = findEdges [idx] (getEdges t1) in
  if null validEdges then [(t1, t2)]
  else let correspondingEdge = safeFind [0] (getEdges t2)
           theEdge = head validEdges
           l1 = safeGet' "there is no left node" 0 (getNodes theEdge)
           l2 = safeGet' "there is no left node" 0 (getNodes correspondingEdge)
           r1 = safeGet' "there is no right node" 1 (getNodes theEdge)
           r2 = safeGet' "there is no right node" 1 (getNodes correspondingEdge)
       in pairDagsAtIdx idx l1 l2 ++
          pairDagsAtIdx idx r1 r2

getOrderOfFlattenType :: FlatType -> [FlatType]
getOrderOfFlattenType t@(FlatType _ _) = [t]
getOrderOfFlattenType (FlatTypeArr _ t1 t2) = getOrderOfFlattenType t1 ++ getOrderOfFlattenType t2

-- given three rhrot, condition, oldContext, and newContext to build the subtype relations
ctxtJoin :: MonadWriter [Rule] m => F.Expr -> RHORT -> RHORT -> RHORT -> m ()
ctxtJoin constraint condition oldContext newContext = do
  let leafNode = getAnLeafNode (refinementDAG condition)
  let nonTerminal = safeGetNonterminal leafNode
  constrain' constraint [nonTerminal] [oldContext] newContext

getAnLeafNode :: RefinementDAG -> RefinementDAG
getAnLeafNode node =
  let edges = getEdges node
  in if null edges then node
     else getAnLeafNode (safeGet' "there is no node in get an leftNode" 0 (getNodes (head edges)))

-- given three rhrot, abs,arg, and app to build the subtype relations
-- when arg is prim
appJoin :: MonadWriter [Rule] m => Int -> F.Expr -> RHORT -> RHORT -> RHORT -> m ()
appJoin idx constraint absRhort argRhort appRhort = do
  let rightMostNode1 = rightmostNode idx (refinementDAG absRhort)
  let rightMostNode2 = rightmostNode idx (refinementDAG appRhort)
  evalStateT (do
    witnessNode' constraint [] [rightMostNode1, refinementDAG argRhort] rightMostNode2
    witnessNode' constraint [] [refinementDAG absRhort, refinementDAG argRhort]
      (refinementDAG appRhort)) S.empty

-- The rightmost node, respecting the given index.
rightmostNode :: Int -> RefinementDAG -> RefinementDAG
rightmostNode idx node =
  let edges = getEdges node
      oneEdge = filter (\edge -> getIndexs edge == [idx]) edges
  in if null oneEdge then node
     else if length oneEdge == 1
     then rightmostNode idx (safeGet' "there is no right node" 1 (getNodes (head oneEdge)))
     else error "there is error in get rightMostNode"

constrain :: MonadWriter [Rule] m => F.Expr -> [RHORT] -> RHORT -> m ()
constrain e = constrain' e []

-- given two HORT has same structure and the constraint, build the
-- subtype relations between two HORT
constrain' :: MonadWriter [Rule] m => F.Expr -> [Nonterminal] -> [RHORT] -> RHORT -> m ()
constrain' constraint fixTerminals bodys headNode =
  witnessNode constraint fixTerminals (map refinementDAG bodys) (refinementDAG headNode)

-- given two RHORT has same structure, build the subtype relations between two RHORT
subtype :: MonadWriter [Rule] m => RHORT -> RHORT -> m ()
subtype rhort1 = constrain' (F.LBool True) [] [rhort1]

-- given a set of HORTNode, get there predicates
getPredicates :: [RefinementDAG] -> [Nonterminal]
getPredicates = map safeGetNonterminal

safeGetNonterminal :: RefinementDAG -> Nonterminal
safeGetNonterminal node = case node of
  SimpleRHORT _ nonterminal -> nonterminal
  _ -> error "there is no nonterminal to get"


-- TODO:  needs to get varlist not set to equall
buildConstrains :: F.Expr ->[Nonterminal] -> [Nonterminal] -> Nonterminal -> Rule
buildConstrains constraint fixTerminals bodys headN = 
 let varsLists = map (\(Nonterminal _ vars)->vars) bodys
     Nonterminal _ headVars = headN
     equalExprs =
       F.manyAnd (map (buildEqExpr (toListOf F.vars constraint) headVars) varsLists)
 in Rule L headN (equalExprs `F.mkAnd` constraint) (fixTerminals ++ bodys)

buildEqExpr :: [F.Var] -> [F.Var] -> [F.Var] -> F.Expr
buildEqExpr fVars vars1 vars2 =
  let list1 = filter (`notElem` fVars) vars1
      list2 = filter (`notElem` fVars) vars2
  in F.manyAnd (zipWith (\x y -> F.mkEql (view F.varType x) (F.V x) (F.V y)) list1 list2)


-- given the witnessNode position to build the corresponding constrains and return the visited Node
witnessNode :: MonadWriter [Rule] m
            => F.Expr -> [Nonterminal] -> [RefinementDAG] -> RefinementDAG
            -> m ()
witnessNode constraint fixTerminals bodys node =
  evalStateT (witnessNode' constraint fixTerminals bodys node) S.empty

witnessNode' :: MonadWriter [Rule] m
             => F.Expr -> [Nonterminal] -> [RefinementDAG] -> RefinementDAG
             -> StateT (Set RefinementDAG) m ()
witnessNode' constraint fixTerminals bodys node =
  S.member node <$> get >>= \case
    True -> pure ()
    False -> do
      modify (S.insert node)
      case node of
        SimpleRHORT _ nonterminal ->
          lift (tell [buildConstrains constraint fixTerminals (getPredicates bodys) nonterminal])
        CompositeRHORT{} -> do
          constrainChild getLeftNodes
          constrainChild getRightNodes
  where
    hdEdges = getEdges node
    validEdges = map (sameEdges (map getEdges bodys)) hdEdges
    constrainChild accessor =
      let body = map accessor validEdges
          hd = accessor hdEdges
      in zipWithM_ (witnessNode' constraint fixTerminals) body hd


-- get the left side nodes based on the pair of given edges
getLeftNodes :: [RHORTEdge] -> [RefinementDAG]
getLeftNodes = map getLeftNode
  where getLeftNode edge = safeGet' "there is no left node" 0 (getNodes edge)

-- get the right side nodes based on the pair of given edges
getRightNodes :: [RHORTEdge] -> [RefinementDAG]
getRightNodes = map getRightNode
  where getRightNode edge = safeGet' "there is no right node" 1 (getNodes edge)

-- given a list of lists of edges, and the same edges, choose the edges has the same indexs
sameEdges :: [[RHORTEdge]] -> RHORTEdge -> [RHORTEdge]
sameEdges listOfEdges headEdge =
  let idxs = getIndexs headEdge
  in map (safeFind idxs) listOfEdges

safeFind :: [Int] -> [RHORTEdge] -> RHORTEdge
safeFind idxs edges =
  let oneEdge = filter (\edge -> getIndexs edge == idxs) edges
  in if length oneEdge == 1 then head oneEdge
  else error "there is not right number of edge match the index"

findEdges :: [Int] -> [RHORTEdge] -> [RHORTEdge]
findEdges idxs = filter (\edge -> getIndexs edge == idxs)

-- | print an given the message is current list is less then the index
safeGet :: String -> Int -> Seq a -> a
safeGet message idx s =
  if length s <= idx
  then error message
  else Seq.index s idx

safeGet' :: String -> Int -> [a] -> a
safeGet' message idx s =
  if length s <= idx
  then error message
  else s !! idx

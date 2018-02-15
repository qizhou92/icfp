module Language.HORT where

import           Control.Monad.State
import           Data.Data (Data)
import           Data.Tree
import           Data.Map (Map)
import qualified Data.Map as M

import           Language.Types
import           Grammar
import qualified Formula as F

data HORT = HORT
  { getHORT :: Tree Nonterminal
  , getBasicType :: Type
  } deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype ::HORT -> HORT -> [Rule]
subtype hort1 hort2 = buildSubType (getHORT hort1) (getHORT hort2)
  

buildSubType :: Tree Nonterminal -> Tree Nonterminal -> [Rule]
buildSubType (Node n1 subTrees1) (Node n2 subTrees2) =
  let rule = Rule L n2 (F.LBool True) [n1]
      rules = concat (zipWith buildSubType subTrees2 subTrees1)
  in rule : rules

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the value of the expression.
valueOf :: HORT -> F.Expr
valueOf hort1 = do
 let (Node nonterminal _) = getHORT hort1
 let (Nonterminal _ vars) = nonterminal
 F.V (last vars)

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the first argument of the expression and its type is primitive type.
argumentOf :: HORT -> F.Expr
argumentOf hort = 
  let (Node (Nonterminal predicateId _) _) = getHORT hort
  in case (getBasicType hort) of
     TArr t1 _ -> case t1 of
               TInt ->F.V (F.Var ("arg" ++ "1#" ++ show predicateId) F.Int)
               TBool ->F.V (F.Var ("arg" ++ "1#" ++ show predicateId) F.Bool)
               _ -> error "this type is not support (argumentOf in HORT)"
     _ -> error "this type is not support (argumentOf in HORT)"


-- | Whether or not this type is primitive.
isPrim :: HORT -> Bool
isPrim hort1 = case getBasicType hort1 of
  TInt ->  True
  TBool -> True
  TArr _ _ -> False
  _ -> error "this type should not in HORT"

-- | Given a list of free variables and a basic type, construct
-- a higher order refinement type.
fresh :: MonadState Int m => Map Var Type -> [Var] -> Type -> m HORT
fresh freeVarMaps freeVars exprType = do
  let primitiveVars = filter (\(_, basicType) -> isPrimitiveType basicType) (M.toList freeVarMaps)
  tree <- buildTreeNode primitiveVars exprType
  return (HORT tree exprType)

buildTreeNode :: MonadState Int m => [(Var, Type)] -> Type ->m (Tree Nonterminal)
buildTreeNode freeVarMaps exprType = do
  let (highOrderTypes, basicTypes) = getCollectType ([], []) exprType
  rootNonterminal <- freeRootPredicate freeVarMaps basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node rootNonterminal subTrees)

buildHighOrderTreeNode :: MonadState Int m => Type ->m (Tree Nonterminal)
buildHighOrderTreeNode exprType = do
  let (highOrderTypes, basicTypes) = getCollectType ([], []) exprType
  rootNonterminal <- freePredicate basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node rootNonterminal subTrees)

-- | Given a pair of list of types, the first list is the list of high order types,
-- the second list is current primitive type
getCollectType :: ([Type], [Type]) -> Type -> ([Type], [Type])
getCollectType (currentHighOrderTypes, basicTypes) currentType = case currentType of
  TInt -> (currentHighOrderTypes,basicTypes++[TInt])
  TBool -> (currentHighOrderTypes,basicTypes++[TBool])
  TArr t1 t2 -> case t1 of
                TInt -> getCollectType (currentHighOrderTypes, basicTypes++[TInt]) t2
                TBool -> getCollectType (currentHighOrderTypes, basicTypes++[TBool]) t2
                TArr _ _ -> getCollectType (currentHighOrderTypes++[t1], basicTypes) t2
                _ -> error "this type should not in getCollectType 2"
  _ -> error "this type should not in getCollectType 1"

freePredicate :: MonadState Int m =>[Type] -> m Nonterminal
freePredicate types = do
  idNumber <- get
  let varList =  map (buildFVar idNumber) (zip types [1 ..])
  let nonterminal = Nonterminal idNumber varList
  put (idNumber+1)
  return nonterminal

freeRootPredicate :: MonadState Int m =>[(Var,Type)] -> [Type] -> m Nonterminal
freeRootPredicate freeVarsWithType types = do
  idNumber <- get
  let varList =  map (buildFVar idNumber) (zip types [1 ..])
  let freeVarList = map buildFreeVar freeVarsWithType
  let nonterminal = Nonterminal idNumber (freeVarList ++ varList)
  put (idNumber+1)
  return nonterminal

buildFreeVar :: (Var,Type) -> F.Var
buildFreeVar (Var name, basicType) = case basicType of
  TInt -> F.Var name F.Int
  TBool -> F.Var name F.Bool
  _ -> error "it is not an primitive type  free vars (buildFreeVar in HORT)"

buildFVar :: Int -> (Type,Int) -> F.Var
buildFVar predicateId (types,index) = case types of
  TInt -> F.Var ("arg" ++ show index ++ "#" ++ show predicateId) F.Int
  TBool -> F.Var ("arg" ++ show index ++ "#" ++ show predicateId) F.Bool
  _ -> error "this is not a valid type in buildFVar"
-- | Split a refinement type at the arrow position.
split :: HORT -> Maybe (HORT, HORT)
split hort = case (getBasicType hort) of
  TInt -> Nothing
  TBool -> Nothing
  TArr t1 t2 -> let (Node root subTrees) = getHORT hort
                in Just ((HORT (head subTrees) t1),(HORT (Node root (tail subTrees)) t2))
  _ -> error "it is not a support type (split in HORT)"

-- Generate a set of rules which constrains that all higher order refinement types
-- are primitive

constrainForPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constrainForPrimitive headHort body constraint =
  let (Node h _) = getHORT headHort
      bodys = map (\(Node root _) -> root) (map getHORT body)
  in [(Rule L h constraint bodys)]

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an app expression and the argument is primitve
constrainForAppPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constrainForAppPrimitive headHort body constraint = 
  let (Node root subTrees) = getHORT headHort
      (Node abst subTrees2) = getHORT (head body)
      (Node arg _) = getHORT (last body)
  in let rule = Rule L root constraint [abst,arg]
         rules = concat (zipWith (buildSubType) subTrees subTrees2)
      in rule:rules

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an lam expression and the variable is primitve
constraintForLamPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constraintForLamPrimitive headHort body constraint =
  let (Node root subTrees) = getHORT headHort
      (Node expr subTrees2) = getHORT (head body)
  in let rule = Rule L root constraint [expr]
         rules = concat (zipWith (buildSubType) subTrees subTrees2)
      in rule:rules

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an if expression
constraintForIf :: HORT -> [HORT] -> F.Expr -> [Rule]
constraintForIf headHort body constraint = 
  let (Node root subTrees) = getHORT headHort
      (Node condition _ )  = getHORT (head body)
      (Node true subTrees2) = getHORT (body !! 1)
      (Node false subTrees3) = getHORT (body !! 2)
  in let rule = Rule L root constraint [condition,true,false]
         rules1 = concat (zipWith (buildSubType) subTrees subTrees2)
         rules2 = concat (zipWith (buildSubType) subTrees subTrees3)
      in rule:(rules1++rules2)

-- | Generate a set of rules which constrain the higher order refinement types
-- by the given formula.
constrain :: HORT -> [HORT] -> F.Expr -> [Rule]
constrain head body constraint = undefined
  -- TODO constrain the shared free variables
  -- TODO construct grammar rule(s?)

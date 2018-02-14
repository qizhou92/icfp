module Language.HORT where

import           Control.Monad.State
import           Data.Data (Data)
import           Data.Tree
import           Language.Types
import           Grammar
import qualified Formula as F
import qualified Data.Map as Map

data HORT = HORT { getHORT :: Tree Nonterminal
                      , getBasicType :: Type} 
  deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype :: HORT -> HORT -> [Rule]
subtype = undefined

buildSubType :: Category -> (Tree Nonterminal) -> (Tree Nonterminal) -> [Rule]
buildSubType category (Node n1 subTrees1) (Node n2 subTrees2) = do
  let rule = Rule category n2 (F.LBool True) [n1]
  let rules = concat (zipWith (buildSubType category) subTrees2 subTrees1)
  rule:rules 

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the value of the expression.
valueOf :: HORT -> F.Expr
valueOf hort1 = do
 let (Node nonterminal _) = getHORT hort1
 let (Nonterminal _ vars) = nonterminal
 F.V (last vars)


-- | Whether or not this type is primitive.
isPrim :: HORT -> Bool
isPrim hort1 = case (getBasicType hort1) of
  TInt ->  True
  TBool -> True
  TArr _ _ -> False
  _ -> error "this type should not in HORT"

-- | Given a list of free variables and a basic type, construct
-- a higher order refinement type.
fresh :: MonadState Int m => Map.Map Var Type -> Type -> m HORT
fresh freeVarMaps exprType = do
  let primitiveVars = filter (\(_,basicType) -> isPrimitiveType basicType) (Map.toList freeVarMaps)
  tree <- buildTreeNode primitiveVars exprType
  return (HORT tree exprType)

buildTreeNode :: MonadState Int m => [(Var,Type)] -> Type ->m (Tree Nonterminal)
buildTreeNode freeVarMaps exprType = do
  let (highOrderTypes,basicTypes) = getCollectType ([],[]) exprType
  rootNonterminal <- freePredicate freeVarMaps basicTypes
  subTrees <- mapM (buildTreeNode freeVarMaps) highOrderTypes
  return (Node rootNonterminal subTrees)
-- | Given a pair of list of types, the first list is the list of high order types,
-- the second list is current primitive type
getCollectType :: ([Type],[Type]) -> Type -> ([Type],[Type])
getCollectType (currentHighOrderTypes, basicTypes) currentType = case currentType of
  TInt -> (currentHighOrderTypes,TInt:basicTypes)
  TBool -> (currentHighOrderTypes,TBool:basicTypes)
  TArr t1 t2 -> case t1 of
                TInt -> getCollectType (currentHighOrderTypes,TInt:basicTypes) t2
                TBool -> getCollectType (currentHighOrderTypes,TBool:basicTypes) t2
                TArr _ _ -> getCollectType (t1:currentHighOrderTypes,basicTypes) t2
                _ -> error "this type should not in getCollectType 2"
  _ -> error "this type should not in getCollectType 1"

freePredicate :: MonadState Int m =>[(Var,Type)] -> [Type] -> m Nonterminal
freePredicate freeVarsWithType types = do
  idNumber <- get
  let varList =  map (buildFVar idNumber) (zip types [1 ..])
  let freeVarList = map buildFreeVar freeVarsWithType
  let nonterminal = Nonterminal idNumber (freeVarList ++ varList)
  put (idNumber+1)
  return nonterminal

buildFreeVar :: (Var,Type) -> F.Var
buildFreeVar ((Var name),basicType) = case basicType of
  TInt -> F.Var name F.Int
  TBool -> F.Var name F.Bool
  _ -> error "it is not an primitive type  free vars (buildFreeVar in HORT)"

buildFVar :: Int -> (Type,Int) -> F.Var
buildFVar predicateId (types,index) = case types of
  TInt -> F.Var ("arg" ++ (show index)++"#"++(show predicateId)) F.Int
  TBool -> F.Var ("arg" ++ (show index)++"#"++(show predicateId)) F.Bool
  _ -> error "this is not an valid type in buildFVar"
-- | Split a refinement type at the arrow position.
split :: HORT -> Maybe (HORT, HORT)
split = undefined

-- | Generate a set of rules which constrain the higher order refinement types
-- by the given formula.
constrain :: HORT -> [HORT] -> F.Expr -> [Rule]
constrain head body constraint = undefined
  -- TODO constrain the shared free variables
  -- TODO construct grammar rule(s?)

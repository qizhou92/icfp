{-# LANGUAGE QuasiQuotes #-}
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
  -- the type list is the list of flat basic type
  { getHORT :: Tree (Nonterminal,[Type])
  , getBasicType :: Type
  } deriving (Show, Read, Eq, Data)

-- | Given a pair of higher order refinement types, generate the grammar rules
-- which constrain the types.
subtype ::HORT -> HORT -> [Rule]
subtype hort1 hort2 = buildSubType (getHORT hort1) (getHORT hort2)

buildSubType :: Tree (Nonterminal,[Type]) -> Tree (Nonterminal,[Type]) -> [Rule]
buildSubType (Node (n1,types1) subTrees1) (Node (n2,types2) subTrees2) =
  let (Nonterminal _ vars1) = n1
      (Nonterminal _ vars2) = n2
      dropLength1 = length vars1 - length types1
      dropLength2 = length vars2 - length types2
      expr =F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|]) (drop dropLength1 vars1) (drop dropLength2 vars2))
      rule = Rule L n2 expr [n1]
      rules = concat (zipWith buildSubType subTrees2 subTrees1)
  in rule : rules

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the value of the expression.
valueOf :: HORT -> F.Expr
valueOf hort1 = do
 let (Node (nonterminal,_) _) = getHORT hort1
 let (Nonterminal _ vars) = nonterminal
 F.V (last vars)

-- | Given a higher order refinement type, fetch the formula (variable) which
-- represents the first argument of the expression and its type is primitive type.
argumentOf :: HORT -> F.Expr
argumentOf hort = 
  let (Node (Nonterminal predicateId _, _) _) = getHORT hort
  in case getBasicType hort of
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
  let fvs = map (\v -> (v, freeVarMaps M.! v)) freeVars
  let primitiveVars = filter (\(_, basicType) -> isPrimitiveType basicType) fvs
  tree <- buildTreeNode primitiveVars exprType
  return (HORT tree exprType)

buildTreeNode :: MonadState Int m => [(Var, Type)] -> Type ->m (Tree (Nonterminal, [Type]))
buildTreeNode freeVarMaps exprType = do
  let (highOrderTypes, basicTypes) = getCollectType ([], []) exprType
  rootNonterminal <- freeRootPredicate freeVarMaps basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node (rootNonterminal , basicTypes) subTrees)

buildHighOrderTreeNode :: MonadState Int m => Type ->m (Tree (Nonterminal, [Type]))
buildHighOrderTreeNode exprType = do
  let (highOrderTypes, basicTypes) = getCollectType ([], []) exprType
  rootNonterminal <- freePredicate basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node (rootNonterminal , basicTypes) subTrees)

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
  let varList =  map (buildFVar idNumber) (zip (init types) [1 ..])
  let outputVar = buildOutput idNumber (last types)
  let nonterminal = Nonterminal idNumber (varList++[outputVar])
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

buildOutput :: Int -> Type -> F.Var
buildOutput predicateId types = case types of 
  TInt -> F.Var ("output" ++ "#" ++ show predicateId) F.Int
  TBool -> F.Var ("output" ++ "#" ++ show predicateId) F.Bool
  _ -> error "this is not a valid type in buildFVar"

buildFVar :: Int -> (Type,Int) -> F.Var
buildFVar predicateId (types,index) = case types of
  TInt -> F.Var ("arg" ++ show index ++ "#" ++ show predicateId) F.Int
  TBool -> F.Var ("arg" ++ show index ++ "#" ++ show predicateId) F.Bool
  _ -> error "this is not a valid type in buildFVar"
-- | Split a refinement type at the arrow position.
split :: HORT -> Maybe (HORT, HORT)
split hort = case getBasicType hort of
  TInt -> Nothing
  TBool -> Nothing
  TArr t1 t2 -> let (Node root subTrees) = getHORT hort
                in Just (HORT (head subTrees) t1, HORT (Node root (tail subTrees)) t2)
  _ -> error "it is not a support type (split in HORT)"

-- Generate a set of rules which constrains that all higher order refinement types
-- are primitive

constrainForPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constrainForPrimitive headHort body constraint =
  let (Node (h,_) _) = getHORT headHort
      bodys = map ((\(Node (root,_) _) -> root) . getHORT) body
  in [Rule L h constraint bodys]

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an app expression and the argument is primitve
constrainForAppPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constrainForAppPrimitive headHort body constraint = 
  let (Node (root,types1)  subTrees) = getHORT headHort
      (Node (abst,types2) subTrees2) = getHORT (head body)
      (Node (arg,_)  _) = getHORT (last body)
      (Nonterminal _ vars1) = root
      (Nonterminal _ vars2) = abst
      dropLength1 = length vars1 - length types1
      dropLength2 = length vars2 - length types2 + 1
      expr = F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|]) (drop dropLength1 vars1) (drop dropLength2 vars2))
      rule = Rule L root (F.mkAnd constraint expr) [abst,arg]
      rules = concat (zipWith buildSubType subTrees subTrees2)
  in rule:rules

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an lam expression and the variable is primitve
constraintForLamPrimitive :: HORT -> [HORT] -> F.Expr -> [Rule]
constraintForLamPrimitive headHort body constraint =
  let (Node (root,types1) subTrees) = getHORT headHort
      (Node (insideExpr,types2) subTrees2) = getHORT (head body)
      (Nonterminal _ vars1) = root
      (Nonterminal _ vars2) = insideExpr
      dropLength1 = length vars1 - length types1 + 1
      dropLength2 = length vars2 - length types2
      allOutuptEqual = F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|]) (drop dropLength1 vars1) (drop dropLength2 vars2))
      rule = Rule L root (F.mkAnd constraint allOutuptEqual) [insideExpr]
      rules = concat (zipWith buildSubType subTrees subTrees2)
  in rule:rules

-- Generate a set of rules which constrains that all higher order refinement types
-- when it is an if expression
constraintForIf :: HORT -> [HORT]  -> [Rule]
constraintForIf headHort body = 
  let (Node (root,types) subTrees) = getHORT headHort
      (Node (condition,_) _ )  = getHORT (head body)
      (Node (true,_) subTrees2) = getHORT (body !! 1)
      (Node (false,_) subTrees3) = getHORT (body !! 2)
      sv = valueOf (head body)
      (Nonterminal _ vars1) = root
      (Nonterminal _ vars2) = true
      (Nonterminal _ vars3) = false
      dropLength1 = length vars1 - length types
      dropLength2 = length vars2 - length types
      dropLength3 = length vars3 - length types
      expr1 = F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|]) (drop dropLength1 vars1) (drop dropLength2 vars2))
      expr2 = F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|]) (drop dropLength1 vars1) (drop dropLength3 vars3))
      constraintT = [F.expr|$sv && $expr1|]
      constraintF = [F.expr|not ($sv && $expr2)|]
      ruleT = Rule L root constraintT [condition,true]
      ruleF = Rule L root constraintF [condition,false]
      rules1 = concat (zipWith buildSubType subTrees subTrees2)
      rules2 = concat (zipWith buildSubType subTrees subTrees3)
  in ruleT:ruleF:(rules1++rules2)

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
  { getHORT :: Tree (Nonterminal, [Type])
  , getBasicType :: Type
  } deriving (Show, Read, Eq, Data)

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
  let (Node (Nonterminal pid _, _) _) = getHORT hort
  in case getBasicType hort of
     TArr t _ -> F.V $ mkArg pid (t, 1)
     _ -> error "this type is not supported (argumentOf in HORT)"

-- | Whether or not this type is primitive.
isPrim :: HORT -> Bool
isPrim hort1 = case getBasicType hort1 of
  TInt ->  True
  TBool -> True
  TArr _ _ -> False
  _ -> error "this type should not be in HORT"

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
  let (highOrderTypes, basicTypes) = collectTypes ([], []) exprType
  rootNonterminal <- mkPredicate freeVarMaps basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node (rootNonterminal , basicTypes) subTrees)

buildHighOrderTreeNode :: MonadState Int m => Type ->m (Tree (Nonterminal, [Type]))
buildHighOrderTreeNode exprType = do
  let (highOrderTypes, basicTypes) = collectTypes ([], []) exprType
  rootNonterminal <- mkHOPredicate basicTypes
  subTrees <- mapM buildHighOrderTreeNode highOrderTypes
  return (Node (rootNonterminal , basicTypes) subTrees)

-- | Given a pair of list of types, the first list is the list of high order types,
-- the second list is current primitive type
collectTypes :: ([Type], [Type]) -> Type -> ([Type], [Type])
collectTypes (currentHighOrderTypes, basicTypes) currentType = case currentType of
  TInt -> (currentHighOrderTypes,basicTypes++[TInt])
  TBool -> (currentHighOrderTypes,basicTypes++[TBool])
  TArr t1 t2 ->
    case t1 of
      TInt -> collectTypes (currentHighOrderTypes, basicTypes++[TInt]) t2
      TBool -> collectTypes (currentHighOrderTypes, basicTypes++[TBool]) t2
      TArr _ _ -> collectTypes (currentHighOrderTypes++[t1], basicTypes) t2
      _ -> error "this type should not be in collectTypes 2"
  _ -> error "this type should not be in collectTypes 1"

mkHOPredicate :: MonadState Int m => [Type] -> m Nonterminal
mkHOPredicate = mkPredicate []

mkPredicate :: MonadState Int m => [(Var,Type)] -> [Type] -> m Nonterminal
mkPredicate freeVarsWithType types = do
  idNumber <- get
  let varList = map (mkArg idNumber) (zip (init types) [1 ..])
  let outputVar = mkOut idNumber (last types)
  let freeVarList = map mkFreeVar freeVarsWithType
  let nonterminal = Nonterminal idNumber (freeVarList ++ varList ++ [outputVar])
  put (idNumber+1)
  return nonterminal

mkFreeVar :: (Var, Type) -> F.Var
mkFreeVar (Var name, t) = case t of
  TInt -> F.Var name F.Int
  TBool -> F.Var name F.Bool
  _ -> error "it is not an primitive type  free vars (mkFreeVar in HORT)"

mkOut :: Int -> Type -> F.Var
mkOut pid t = mkFreeVar (Var ("out#" ++ show pid), t)

mkArg :: Int -> (Type,Int) -> F.Var
mkArg pid (t, idx) = mkFreeVar (Var ("arg" ++ show idx ++ "#" ++ show pid), t)

-- | Split a refinement type at the arrow position.
split :: HORT -> Maybe (HORT, HORT)
split hort = case getBasicType hort of
  TInt -> Nothing
  TBool -> Nothing
  TArr t1 t2 -> let (Node root subTrees) = getHORT hort
                in Just (HORT (head subTrees) t1, HORT (Node root (tail subTrees)) t2)
  _ -> error "not a supported type (split in HORT)"

-- | Apply a constraint to `t` where other types may witness the constraint.
-- are primitive
constrain :: F.Expr -> [HORT] -> HORT -> [Rule]
constrain constraint witnesses t =
  let h = topPredicate t
      ws = map topPredicate witnesses
  in [Rule L h constraint ws]

-- | Constrain t' to be a subtype of t where a constraint can occur between the types
-- and other types may witness the constraint.
subtype :: F.Expr -> [HORT] -> HORT -> HORT -> [Rule]
subtype constraint witnesses t' t =
  buildSubType constraint (map topPredicate witnesses) (getHORT t') (getHORT t)
  where
    buildSubType constraint context (Node (n1, types1) subTrees1) (Node (n2, types2) subTrees2) =
      let expr = carryBound (length types1) (length types2) n1 n2
          rule = Rule L n2 (constraint `F.mkAnd` expr) (n1:context)
          rules = subTreeRules subTrees2 subTrees1
      in rule : rules
    -- Construct constraints for the subtrees.
    subTreeRules st1 st2 = concat (zipWith (buildSubType (F.LBool True) []) st1 st2)
    -- Copy the bound variables from one type to the other.
    carryBound numBound1 numBound2 (Nonterminal _ vars1) (Nonterminal _ vars2) =
      let toTake = min numBound1 numBound2 in
      F.manyAnd (zipWith (\x y -> [F.expr|@x = @y|])
        (lastN toTake vars1)
        (lastN toTake vars2))

topPredicate :: HORT -> Nonterminal
topPredicate = (\(Node (c, _) _) -> c) . getHORT

lastN :: Int -> [a] -> [a]
lastN n xs = drop (length xs - n) xs

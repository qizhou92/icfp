{-# LANGUAGE QuasiQuotes #-}
module Language.HORT where

import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Data (Data)
import           Data.Tree
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition)

import           Language.Types
import           Grammar
import qualified Formula as F
import           Formula (MonadVocab, fetch, fresh)

import Debug.Trace

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
     TArr t _ -> F.V $ mkArg (primaryID pid) (t, 1)
     _ -> error "this type is not supported (argumentOf in HORT)"

-- | Whether or not this type is primitive.
isPrim :: HORT -> Bool
isPrim = isPrimitiveType . getBasicType

-- | Given a list of free variables and a basic type, construct
-- a higher order refinement type.
freshType :: MonadState Int m => Map Var Type -> [Var] -> Type -> m HORT
freshType varTypes freeVars exprType = do
  let fvs = map (\v -> (v, varTypes M.! v)) freeVars
  let primFvs = filter (\(_, basicType) -> isPrimitiveType basicType) fvs
  HORT <$> mkTree primFvs exprType <*> pure exprType
  where
    mkTree primFreeVars exprType = do
      let (prims, hots) = partition isPrimitiveType $ flattenType exprType
      pred <- mkPredicate primFreeVars prims
      subTrees <- mapM (mkTree []) hots
      return (Node (pred, prims) subTrees)

    mkPredicate freeVarsWithType types = do
      idNumber <- get
      let varList = map (mkArg idNumber) (zip (init types) [1 ..])
      let outputVar = mkOut idNumber (last types)
      let freeVarList = map mkFreeVar freeVarsWithType
      let nonterminal = Nonterminal (ConcreteID idNumber) (freeVarList ++ varList ++ [outputVar])
      put (idNumber+1)
      return nonterminal
    mkOut pid t = mkFreeVar (Var ("out/" ++ show pid), t)

convertToFix :: Set Var -> HORT -> HORT -> HORT
convertToFix bound ref (HORT (Node (Nonterminal iden vs, ts) sub) t)  =
  let tmp =
        HORT (Node (Nonterminal (PhantomID (primaryID iden)
                                           (nonterminalPrimary $ topPredicate ref)
                                           (map getVar (S.toList bound))) vs, ts) sub) t
  in traceShow tmp tmp

flattenType :: Type -> [Type]
flattenType = \case
  TInt -> [TInt]
  TBool -> [TBool]
  TArr s t -> s : flattenType t

mkFreeVar :: (Var, Type) -> F.Var
mkFreeVar (Var name, t) = case t of
  TInt -> F.Var name F.Int
  TBool -> F.Var name F.Bool
  _ -> error "it is not an primitive type  free vars (mkFreeVar in HORT)"

mkArg :: Int -> (Type,Int) -> F.Var
mkArg pid (t, idx) = mkFreeVar (Var ("arg" ++ show idx ++ "/" ++ show pid), t)

-- | Split a refinement type at the arrow position.
split :: HORT -> (HORT, HORT)
split hort = case getBasicType hort of
  TArr t1 t2 -> let (Node root subTrees) = getHORT hort
                in (HORT (head subTrees) t1, HORT (Node root (tail subTrees)) t2)
  _ -> error "not a supported type (split in HORT)"

-- | Apply a constraint to `t` where other types may witness the constraint.
constrain :: MonadWriter [Rule] m => F.Expr -> [HORT] -> HORT -> m ()
constrain constraint witnesses t =
  let h = topPredicate t
      ws = map topPredicate witnesses
  in tell [Rule L h constraint ws]

-- | Constrain t' to be a subtype of t where a constraint can occur between the types
-- and other types may witness the constraint.
subtype :: MonadWriter [Rule] m => F.Expr -> [HORT] -> HORT -> HORT -> m ()
subtype constraint witnesses t' t =
  tell $ subtype' constraint (map topPredicate witnesses) (getHORT t') (getHORT t)
  where
    subtype' constraint witnesses
      (Node (sub, ts1) subTrees1)
      (Node (super, ts2) subTrees2) =
      let expr = carryBound (length ts1) (length ts2) sub super
          rule = Rule L super (constraint `F.mkAnd` expr) (sub:witnesses)
          rules = subTreeRules subTrees2 subTrees1
      in rule : rules
    -- Construct constraints for the subtrees.
    subTreeRules st1 st2 = concat (zipWith (subtype' (F.LBool True) []) st1 st2)
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

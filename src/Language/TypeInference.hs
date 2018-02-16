{-# LANGUAGE TemplateHaskell #-}
module Language.TypeInference where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Attributes

import           Language.Types

data InferenceError
  = UnificationError Type Type
  | UnboundError Var
  deriving (Show, Read, Eq, Ord, Data)

data InferenceState = InferenceState
  { _varCount :: Int
  , _typeTable :: Map Var Type
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''InferenceState

type Ctxt = Map Var Type

type Infer a = StateT InferenceState (Either InferenceError) a

typeCheck :: CoreExpr -> Either InferenceError (Attr CoreExpr' (Ctxt, Type))
typeCheck e = evalStateT (contextualize e >>= infer >>= resolve)
  (InferenceState 0 M.empty)

-- | When two types are the same, ensure they are eventually the same. This involves
-- failing when two known types are not the same and adding additional constraints
-- to the type table when one or both types are unknown variables.
unify :: Type -> Type -> Infer ()
unify (TArr s s') (TArr t t') = unify s t >> unify s' t'
unify (TVar x) (TVar y) = do
  tab <- use typeTable
  case (M.lookup x tab, M.lookup y tab) of
    (Just s , Just t ) -> unify s t
    (Just s , Nothing) -> typeTable %= M.insert y s
    (Nothing, Just t ) -> typeTable %= M.insert x t
    (Nothing, Nothing) -> typeTable %= M.insert x (TVar y)
unify (TVar x) t = do
  tab <- use typeTable
  case M.lookup x tab of
    Just s -> unify s t
    Nothing -> typeTable %= M.insert x t
unify s (TVar y) = do
  tab <- use typeTable
  case M.lookup y tab of
    Just t -> unify s t
    Nothing -> typeTable %= M.insert y s
unify (TList s) (TList t) = unify s t
unify t1 t2
  | t1 == t2 = pure ()
  | otherwise = throwError (UnificationError t1 t2)

-- | Given an expression where each subexpression is annotated with its type,
-- use the type table to replace type variables by their equivalent type, when
-- possible.
resolve :: Attr CoreExpr' (Ctxt, Type) -> Infer (Attr CoreExpr' (Ctxt, Type))
resolve = fmap unAttrib . traverse resolve' . Attrib
  where
    resolve' x = do
      x' <- x & _1 . traverse %%~ res
      x' & _2 %%~ res
    res = \case
      TVar x -> res =<< M.findWithDefault (TVar x) x <$> use typeTable
      TArr s t -> TArr <$> res s <*> res t
      t -> pure t

-- | Create a new type variable.
fresh :: Infer Type
fresh = do
  s <- use varCount
  varCount += 1
  pure (TVar $ Var $ "__tv" ++ show s)

-- | Label each subexpression with the correct context, which is a mapping from
-- expression variables to type variables.
contextualize :: CoreExpr -> Infer (Attr CoreExpr' Ctxt)
contextualize = inheritM (\e ctxt -> case e of
  Fix (ELam x _) -> do
    s <- fresh
    pure (M.insert x s ctxt)
  _ -> pure ctxt
  ) M.empty

-- | Given an expression where each subexpression is annotated with its
-- context, reannotate the subexpressions with their type. The types may not
-- be fully resolved, and may instead refer to type variables.
infer :: Attr CoreExpr' Ctxt -> Infer (Attr CoreExpr' (Ctxt, Type))
infer = fmap annZip .
  -- By using generics, each subexpression has been replaced by its type.
  synthetiseM (\(Ann ctxt e) -> case e of
  -- A => IntLit : Int
  EInt _ -> pure TInt

  -- A => BoolLit : Bool
  EBool _ -> pure TBool

  -- A => Nil : [a]
  ENil -> TList <$> fresh

  -- A + (x : t) => x : t
  EVar x -> case M.lookup x ctxt of
    Nothing -> throwError (UnboundError x)
    Just t  -> pure t

  -- A => o : r -> s -> t, A => e : r, A => e' : s
  -- ------------------------------------------
  -- A => o e e' : t
  EBin o r s -> do
    t <- fresh
    rst <- opType o
    unify (r `TArr` (s `TArr` t)) rst
    pure t

  -- A => c : Bool, A => e : t, A => e' : t
  -- -----------------------------------
  -- A => if c e e' : t
  EIf b t t' -> do
    unify b TBool
    unify t t'
    pure t

  -- A => e : s -> t, A => e' : s
  -- --------------------------
  -- A => e e' : t
  EApp st s -> do
    t <- fresh
    unify st (s `TArr` t)
    pure t

  -- A + (x : s) => e : t
  -- -------------------
  -- A => \x.e : s -> t
  ELam x t -> case M.lookup x ctxt of
    Nothing -> throwError (UnboundError x)
    Just s -> pure (s `TArr` t)

  -- A + (x : s) => e : t
  -- -------------------
  -- A => fix x.e : s -> t
  EFix x t -> case M.lookup x ctxt of
    Nothing -> throwError (UnboundError x)
    Just s -> pure (s `TArr` t))

test = ebin Plus (eapp (elam (Var "x") (evar (Var "x"))) (eint 3))
                 $ eapp (elam (Var "x") (evar (Var "x"))) (eint 3)

opType :: Binop -> Infer Type
opType b
  | b `elem` [Plus, Minus, Mul, Div] = pure (TInt `TArr` (TInt `TArr` TInt))
  | b `elem` [Eq, Ne] = do
    t <- fresh
    pure (t `TArr` (t `TArr` TBool))
  | b `elem` [Lt, Le] = pure (TInt `TArr` (TInt `TArr` TBool))
  | b `elem` [And, Or] = pure (TBool `TArr` (TBool `TArr` TBool))
  -- | b == Cons = let a = TVar "a" in Forall [a] (a `TArr` (TList a `TArr` TList a))
  | otherwise = error ("unknown binop " ++ show b)

-- binScheme :: Type -> Type -> Type -> Scheme
-- binScheme t1 t2 t3 = Forall [] (TArr t1 (TArr t2 t3))

-- resugarMatch :: CoreExpr -> CoreExpr
-- resugarMatch = rewrite (\case
--   EIf cond e1 e2 -> do
--     e <- isCheckNil cond
--     (x, y, ec) <- isConsMatch e e2
--     pure (EMatch e e1 x y ec)
--   _ -> Nothing)
--   where
--     isCheckNil = \case
--       EBin Eq ENil x -> Just x
--       EBin Eq x ENil -> Just x
--       _ -> Nothing

--     hd = EVar (Var "head")
--     tl = EVar (Var "tail")

--     isConsMatch xs (ELet x takeHead (ELet y takeTail e))
--       | takeHead == EApp hd xs , takeTail == EApp tl xs = Just (x, y, e)
--     isConsMatch xs (ELet y takeTail (ELet x takeHead e)) 
--       | takeHead == EApp hd xs , takeTail == EApp tl xs = Just (x, y, e)
--     isConsMatch _ _ = Nothing

listToFix :: Data a => a -> a
listToFix = types %~ rewrite (\case
  TList t -> Just $ TFix (Var "VList") (TPlus TNil (TProduct t (TVar (Var "VList"))))
  _ -> Nothing)

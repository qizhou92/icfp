{-# LANGUAGE TemplateHaskell #-}
module Language.TypeInference where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Monoid ((<>))

import           Language.Types

data InferenceError
  = UnificationError Type Type
  | OccurError Type Type
  | UnboundError Var

type Ctxt = Map Var Type

type Infer a = ExceptT InferenceError (StateT Int (Reader Ctxt)) a

unify :: Type -> Type -> Infer ()
unify = undefined

-- unify :: Type -> Type -> Infer Subst
-- unify (TArr t1 t2) (TArr t3 t4) = do
--   s1 <- unify t1 t3
--   s2 <- unify (apply s1 t2) (apply s1 t4)
--   pure (s2 <> s1)
-- unify (TVar a) t = varAsgn (TVar a) t
-- unify t (TVar a) = varAsgn (TVar a) t
-- unify (TList a) (TList b) = unify a b
-- unify TInt TInt = pure mempty
-- unify TBool TBool = pure mempty
-- unify t1 t2 = throwError (UnificationError t1 t2)

-- varAsgn :: Type -> Type -> Infer Subst
-- varAsgn a t
--   | t == a = pure mempty
--   | S.member a (freeTvars t) = throwError (OccurError a t)
--   | otherwise = pure (Subst $ M.singleton a t)

-- generalize :: TypeEnv -> Type -> Scheme
-- generalize env t = do
--   let as = S.toList (S.difference (freeTvars t) (freeTvars env))
--   Forall as t

fresh :: Infer Var
fresh = do
  s <- get
  put (s + 1)
  pure (Var $ "__tv" ++ show s)

infer :: CoreExpr -> Infer Type
infer expr = case expr of
  -- A => IntLit : Int
  EInt _ -> pure TInt

  -- A => BoolLit : Bool
  EBool _ -> pure TBool

  -- A => Nil : [a]
  ENil -> TList . TVar <$> fresh

  -- A + (x : t) => x : t
  EVar x -> M.lookup x <$> ask >>= \case
    Nothing -> throwError (UnboundError x)
    Just t  -> pure t

  -- A => o : r -> s -> t, A => e : r, A => e' : s
  -- ------------------------------------------
  -- A => o e e' : t
  EBin o e e' -> do
    t <- fresh
    r <- infer e
    s <- infer e'
    let rst = opType o
    unify (r `TArr` (s `TArr` TVar t)) rst
    resolve t

  -- A => c : Bool, A => e : t, A => e' : t
  -- -----------------------------------
  -- A => if c e e' : t
  EIf c e e' -> do
    b <- infer c
    t <- infer e
    t' <- infer e'
    unify b TBool
    unify t t'
    pure t

  -- ELet var1 expr1 expr2 -> do
  --   TypeResult s1 t1 m1 <- infer tEnv expr1
  --   let (TypeEnv env') = apply s1 tEnv
  --   let t'  = generalize (TypeEnv env') t1
  --   TypeResult s2 t2 m2 <- infer  (TypeEnv (M.insert (EVar var1) t' env')) expr2
  --   let m3 = M.union m1 m2
  --   let m4 = M.insert expr t2 m3
  --   pure (TypeResult (s1 <> s2) t2 m4)

  -- A => e : s -> t, A => e' : s
  -- --------------------------
  -- A => e e' : t
  EApp e e' -> do
    t <- fresh
    st <- infer e
    s <- infer e'
    unify st (s `TArr` TVar t)
    resolve t

  -- A + (x : s) => e : t
  -- -------------------
  -- A => \x.e : s -> t
  ELam x e -> bind x e

  -- A + (x : s) => e : t
  -- -------------------
  -- A => fix x.e : s -> t
  EFix x e -> bind x e

  -- EMatch e e1 x y e2 -> do 
  --   TypeResult s0 te me <- infer tEnv e
  --   tv <- freshTVar
  --   se <- unify te (TList tv)
  --   TypeResult s1 t1 m1 <- infer tEnv e1
  --   let env' = M.insert (EVar y) (generalize tEnv $ TList tv) $ M.insert (EVar x) (generalize tEnv tv) (getTypeEnv tEnv)
  --   TypeResult s2 t2 m2 <- infer (TypeEnv env') e2
  --   s12 <- unify (apply se t1) (apply se t2)
  --   let s = mconcat [s12, s2, s1, s2, s0]
  --   let texpr = apply s t1
  --   let m = M.insert expr texpr (mconcat [me, m1, m2])
  --   pure (TypeResult s texpr m)

  where
    bind x e = do
      s <- fresh
      t <- local (M.insert x (TVar s)) (infer e)
      s' <- resolve s
      pure (s' `TArr` t)

resolve :: Var -> Infer Type
resolve = undefined

-- for Eq and Ne, it is not accurate 
opType :: Binop -> Type
opType b = undefined
  -- | b `elem` [Plus, Minus, Mul, Div] = binScheme TInt TInt TInt
  -- | b `elem` [Eq, Ne] = let a = TVar "a" in Forall [a] (TArr a (TArr a TBool))
  -- | b `elem` [Lt, Le] = binScheme TInt TInt TBool
  -- | b `elem` [And, Or] = binScheme TBool TBool TBool
  -- | b == Cons = let a = TVar "a" in Forall [a] (a `TArr` (TList a `TArr` TList a))
  -- | otherwise = error ("unknown op scheme " ++ show b)

-- binScheme :: Type -> Type -> Type -> Scheme
-- binScheme t1 t2 t3 = Forall [] (TArr t1 (TArr t2 t3))

-- getPairFresh :: Infer (Type, Type)
-- getPairFresh = (,) <$> freshTVar <*> freshTVar

-- resugarMatch :: CoreExpr -> CoreExpr
-- resugarMatch = rewrite (\case
  -- EIf cond e1 e2 -> do
  --   e <- isCheckNil cond
  --   (x, y, ec) <- isConsMatch e e2
  --   pure (EMatch e e1 x y ec)
  -- _ -> Nothing)
  -- where
  --   isCheckNil = \case
  --     EBin Eq ENil x -> Just x
  --     EBin Eq x ENil -> Just x
  --     _ -> Nothing

  --   hd = EVar (Var "head")
  --   tl = EVar (Var "tail")

  --   isConsMatch xs (ELet x takeHead (ELet y takeTail e))
  --     | takeHead == EApp hd xs , takeTail == EApp tl xs = Just (x, y, e)
  --   isConsMatch xs (ELet y takeTail (ELet x takeHead e)) 
  --     | takeHead == EApp hd xs , takeTail == EApp tl xs = Just (x, y, e)
  --   isConsMatch _ _ = Nothing

listToFix :: Data a => a -> a
listToFix = types %~ rewrite (\case
  TList t -> Just $ TFix (Var "VList") (TPlus TNil (TProduct t (TVar (Var "VList"))))
  _ -> Nothing)

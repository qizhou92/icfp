module Language.TypeInference where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Monoid ((<>))

import           Language.Types
import           Language.Transformations

types :: Program -> Either InferenceError [(Var, Scheme)]
types prog =
  case evalState (runExceptT (act prog)) 0 of
    Left  err -> Left err
    Right env -> Right $ listToFix [(x,s) | (EVar x, s) <- M.toList $ getTypeEnv env]
   where
     act = foldM (\env (x,e) -> insertEnv env x <$> ti env (resugarMatch e)) initEnv

initEnv :: TypeEnv
initEnv = TypeEnv $ M.fromList
  [ (EVar $ Var "head", Forall [a] (TList a `TArr` a))
  , (EVar $ Var "tail", Forall [a] (TList a `TArr` TList a)) 
  ]
  where
    a = TVar "a"

insertEnv :: TypeEnv -> Var -> TypeResult -> TypeEnv
insertEnv env x (TypeResult _ t _)
  = TypeEnv (M.insert (EVar x) (generalize env t) (getTypeEnv env))

newtype TypeEnv = TypeEnv { getTypeEnv :: Map CoreExpr Scheme}

instance Monoid TypeEnv where
  mempty = TypeEnv mempty
  mappend (TypeEnv m1) (TypeEnv m2) = TypeEnv (mappend m1 m2)

newtype Subst = Subst { getSubst :: Map Type Type }
  deriving (Show)

instance Monoid Subst where
  mempty = Subst mempty
  mappend s1@(Subst m1) (Subst m2) = Subst $ M.union (M.map (apply s1) m2) m1

class Substitutable a where
  apply  :: Subst -> a -> a
  freeTvars :: a -> Set Type

instance Substitutable Type where
  -- | Apply a substitution table to the type by transitively applying to all
  -- type subexpressions. Type variables are looked up in the table while fix
  -- expressions remove their variable from the table (due to binding).
  apply (Subst s) x = runReader (sub x) s
    where sub = \case
            t@TVar{} -> M.findWithDefault t t <$> ask
            TFix t1 t2 -> TFix t1 <$> local (M.delete (TVar t1)) (sub t2)
            t -> t & plate %%~ sub

  -- | To compute the free variables, combine the sets from all subexpressions.
  -- Variables add a free variable whereas fix expressions bind one.
  freeTvars = para (\t ts ->
    let ts' = mconcat ts in case t of
      TVar a -> S.insert (TVar a) ts'
      TFix x _ -> S.delete (TVar x) ts'
      _ -> ts')

instance Substitutable Scheme where
  apply subSet (Forall boundVars t) = Forall boundVars (apply newSubSet t)
    where newSubSet = Subst $ foldr M.delete (getSubst subSet) boundVars
  freeTvars (Forall boundVars t) = S.difference (freeTvars t) (S.fromList boundVars)

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  freeTvars = foldMap freeTvars

instance Substitutable TypeEnv where
  apply s (TypeEnv typeEnv) = TypeEnv (M.map (apply s) typeEnv)
  freeTvars (TypeEnv typeEnv) = freeTvars (M.elems typeEnv)

data InferenceError
  = UnificationError Type Type
  | OccurError Type Type
  | UnboundError Var

type Infer a = ExceptT InferenceError (State Int) a

unify :: Type -> Type -> Infer Subst
unify (TArr t1 t2) (TArr t3 t4) = do
  s1 <- unify t1 t3
  s2 <- unify (apply s1 t2) (apply s1 t4)
  pure (s2 <> s1)
unify (TVar a) t = varAsgn (TVar a) t
unify t (TVar a) = varAsgn (TVar a) t
unify (TList a) (TList b) = unify a b
unify TInt TInt = pure mempty
unify TBool TBool = pure mempty
unify t1 t2 = throwError (UnificationError t1 t2)

varAsgn :: Type -> Type -> Infer Subst
varAsgn a t
  | t == a = pure mempty
  | S.member a (freeTvars t) = throwError (OccurError a t)
  | otherwise = pure (Subst $ M.singleton a t)

generalize :: TypeEnv -> Type -> Scheme

generalize env t = do 
  let as = S.toList (S.difference (freeTvars t) (freeTvars env))
  Forall as t 

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const freshTVar) as
  let s = M.fromList (zip as as')
  pure (apply (Subst s) t)

freshTVar :: Infer Type
freshTVar = do
  s <- get
  put (s+1)
  pure (TVar ("__tv" ++ show s))

data TypeResult = TypeResult Subst Type (Map CoreExpr Type)
  deriving(Show)

ti :: TypeEnv -> CoreExpr -> Infer TypeResult
ti tEnv expr = case expr of
  EInt _ -> pure (TypeResult mempty TInt (M.singleton expr TInt))

  EBool _ -> pure (TypeResult mempty TBool (M.singleton expr TBool))

  ENil -> TypeResult mempty <$> (TList <$> freshTVar) <*> pure mempty

  EVar x -> case M.lookup (EVar x) (getTypeEnv tEnv) of
    Nothing -> throwError (UnboundError x)
    Just s  -> do
      t <- instantiate s
      pure (TypeResult mempty t (M.singleton expr t))

  EBin op expr1 expr2 -> do
    TypeResult s1 t1 m1 <- ti tEnv expr1
    TypeResult s2 t2 m2 <- ti tEnv expr2
    tv <- freshTVar
    opType <- instantiate $ opScheme op
    s3 <- unify (TArr t1 (TArr t2 tv)) opType
    let tnew = apply s3 tv
    let m3 = M.insert expr tnew (m1 <> m2)
    pure (TypeResult (mconcat [s1, s2, s3]) tnew m3)

  EIf expr1 expr2 expr3 -> do
    TypeResult s1 t1 m1 <- ti tEnv expr1
    TypeResult s2 t2 m2 <- ti tEnv expr2
    TypeResult s3 t3 m3 <- ti tEnv expr3
    s4 <- unify t1 TBool
    s5 <- unify t2 t3
    let tnew = apply s5 t2
    let m = M.insert expr tnew (m1 <> m2 <> m3)
    pure (TypeResult (mconcat [s5, s4, s3, s2, s1]) tnew m)

  ELet var1 expr1 expr2 -> do
    TypeResult s1 t1 m1 <- ti tEnv expr1
    let (TypeEnv env') = apply s1 tEnv
    let t'  = generalize (TypeEnv env') t1
    TypeResult s2 t2 m2 <- ti  (TypeEnv (M.insert (EVar var1) t' env')) expr2
    let m3 = M.union m1 m2
    let m4 = M.insert expr t2 m3
    pure (TypeResult (s1 <> s2) t2 m4)

  EApp expr1 expr2 -> do
    tv <- freshTVar
    TypeResult s1 t1 m1 <- ti tEnv expr1
    TypeResult s2 t2 m2 <- ti (apply s1 tEnv) expr2
    s3 <- unify (apply s2 t1) (TArr t2 tv)
    let m3 = M.union m1 m2
    let tnew = apply s3 tv
    let m4 = M.insert expr tnew m3
    pure (TypeResult (mconcat [s3, s2, s1]) tnew m4)

  ELam var1 expr1 -> do
    tv <- freshTVar
    let env' = M.insert (EVar var1) (Forall [] tv) (getTypeEnv tEnv)
    TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
    let tnew = apply s1 (TArr tv t1)
    let m2 = M.insert expr tnew m1
    pure (TypeResult s1 tnew m2)

  -- not sure the rule for fix is correct
  EFix var1 expr1 -> do
    tv <- freshTVar
    let env' = M.insert (EVar var1) (Forall [] tv) (getTypeEnv tEnv)
    TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
    s2 <- unify tv t1
    let tnew = apply s2 tv
    let m2 = M.insert expr tnew m1
    pure (TypeResult (s1 <> s2) tnew m2)

  EMatch e e1 x y e2 -> do 
    TypeResult s0 te me <- ti tEnv e
    tv <- freshTVar
    se <- unify te (TList tv)
    TypeResult s1 t1 m1 <- ti tEnv e1
    let env' = M.insert (EVar y) (generalize tEnv $ TList tv) $ M.insert (EVar x) (generalize tEnv tv) (getTypeEnv tEnv)
    TypeResult s2 t2 m2 <- ti (TypeEnv env') e2
    s12 <- unify (apply se t1) (apply se t2)
    let s = mconcat [s12, s2, s1, s2, s0]
    let texpr = apply s t1
    let m = M.insert expr texpr (mconcat [me, m1, m2])
    pure (TypeResult s texpr m)

-- for Eq and Ne, it is not accurate 
opScheme :: Binop -> Scheme
opScheme b
  | b `elem` [Plus, Minus, Mul, Div] = binScheme TInt TInt TInt
  | b `elem` [Eq, Ne] = let a = TVar "a" in Forall [a] (TArr a (TArr a TBool))
  | b `elem` [Lt, Le] = binScheme TInt TInt TBool
  | b `elem` [And, Or] = binScheme TBool TBool TBool
  | b == Cons = let a = TVar "a" in Forall [a] (a `TArr` (TList a `TArr` TList a))
  | otherwise = error ("unknown op scheme " ++ show b)

binScheme :: Type -> Type -> Type -> Scheme
binScheme t1 t2 t3 = Forall [] (TArr t1 (TArr t2 t3))

getPairFresh :: Infer (Type, Type)
getPairFresh = (,) <$> freshTVar <*> freshTVar

inferType :: CoreExpr -> Either InferenceError (Map CoreExpr Type)
inferType expr = do
  TypeResult subset _ mapResult <- evalState (runExceptT (ti (TypeEnv M.empty) (resugarMatch expr))) 0
  pure $ listToFix (M.map (apply subset) mapResult)

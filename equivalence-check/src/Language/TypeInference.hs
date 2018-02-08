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

types :: Program -> Either String [(Var, Scheme)]
types prog =
  case evalState (runExceptT (act prog)) 0 of
    Left  err -> Left err
    Right env -> Right $ listToFix [(x,s) | (EVar x, s) <- M.toList $ tyEnv env]
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
  = TypeEnv (M.insert (EVar x) (generalize env t) (tyEnv env))

newtype TypeEnv = TypeEnv {tyEnv :: Map CoreExpr Scheme}

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
  apply (Subst s) x = runReader (rewriteM sub x) s
    where sub = \case
            t@TVar{} -> M.lookup t <$> ask
            TFix t1 t2 -> fmap (TFix t1) <$> local (M.delete (TVar t1)) (sub t2)
            _ -> pure Nothing

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

type HM a = ExceptT String (State Int) a

unify :: Type -> Type -> HM Subst
unify (TArr t1 t2) (TArr t3 t4) = do
  s1 <- unify t1 t3
  s2 <- unify (apply s1 t2) (apply s1 t4)
  pure (s2 <> s1)
unify (TVar a) t = varAsgn (TVar a) t
unify t (TVar a) = varAsgn (TVar a) t 
unify TInt TInt = pure mempty
unify TBool TBool = pure mempty
unify (TList a) (TList b) = unify a b 
unify t1 t2 = throwError ("types do not unify: " ++ show t1 ++ " vs ." ++ show t2 ++"\n")

varAsgn :: Type -> Type -> HM Subst
varAsgn a t
  | t == a         = pure mempty
  | S.member a (freeTvars t) = throwError ("occur check fails: " ++ show a ++ " in " ++ show t)
  | otherwise      = pure (Subst $ M.singleton a t)

generalize :: TypeEnv -> Type -> Scheme

generalize env t = do 
  let as = S.toList (S.difference (freeTvars t) (freeTvars env))
  Forall as t 

instantiate :: Scheme -> HM Type
instantiate (Forall as t) = do
  as' <- mapM (const freshTVar) as
  let s = M.fromList (zip as as')
  pure (apply (Subst s) t)

freshTVar :: HM Type
freshTVar = do
  s <- get
  put (s+1)
  pure (TVar ("newTypeVariable" ++ show s))

data TypeResult = TypeResult Subst Type (Map CoreExpr Type)
  deriving(Show)

ti :: TypeEnv -> CoreExpr -> HM TypeResult
ti _ expr@(EInt  _) = pure (TypeResult mempty TInt (M.singleton expr TInt))
ti _ expr@(EBool _) = pure (TypeResult mempty TBool (M.singleton expr TBool))
ti _ ENil = do
  a <- freshTVar
  pure $ TypeResult mempty (TList a) mempty
ti (TypeEnv env) expr@(EVar x) = 
  case M.lookup (EVar x) env of
     Nothing -> throwError ("Unbound Variable: " ++ show x)
     Just s  -> do
       t <- instantiate s
       pure (TypeResult mempty t (M.singleton expr t))

ti tEnv expr@(EBin op expr1 expr2) = do
  TypeResult s1 t1 m1 <- ti tEnv expr1
  TypeResult s2 t2 m2 <- ti tEnv expr2
  tv <- freshTVar
  opType <- instantiate $ getOp op
  s3 <- unify (TArr t1 (TArr t2 tv)) opType
  let tnew = apply s3 tv
  let m3 = M.insert expr tnew (m1 <> m2)
  pure (TypeResult (mconcat [s1, s2, s3]) tnew m3)

ti tEnv expr@(EIf expr1 expr2 expr3) = do
  TypeResult s1 t1 m1 <- ti tEnv expr1
  TypeResult s2 t2 m2 <- ti tEnv expr2
  TypeResult s3 t3 m3 <- ti tEnv expr3
  s4 <- unify t1 TBool
  s5 <- unify t2 t3
  let tnew = apply s5 t2
  let m5 = M.insert expr tnew (m1 <> m2 <> m3)
  let newSubSet = mconcat [s5, s4, s3, s2, s1]
  pure (TypeResult newSubSet tnew m5)

ti (TypeEnv env) expr@(ELet var1 expr1 expr2) = do
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  let (TypeEnv env') = apply s1 (TypeEnv env)
  let t'  = generalize (TypeEnv env') t1
  TypeResult s2 t2 m2 <- ti  (TypeEnv (M.insert (EVar var1) t' env')) expr2
  let m3 = M.union m1 m2
  let m4 = M.insert expr t2 m3
  pure (TypeResult (s1 <> s2) t2 m4) 

ti (TypeEnv env) expr@(EApp expr1 expr2) = do
  tv <- freshTVar
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  TypeResult s2 t2 m2 <- ti (apply s1 (TypeEnv env)) expr2
  s3 <- unify (apply s2 t1) (TArr t2 tv)
  let m3 = M.union m1 m2
  let tnew = apply s3 tv
  let m4 = M.insert expr tnew m3
  pure (TypeResult (mconcat [s3, s2, s1]) tnew m4)

ti (TypeEnv env) expr@(ELam var1 expr1) = do
  tv <- freshTVar
  let env' = M.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  let tnew = apply s1 (TArr tv t1)
  let m2 = M.insert expr tnew m1
  pure (TypeResult s1 tnew m2)

-- not sure the rule for fix is correct
ti (TypeEnv env) expr@(EFix var1 expr1) = do 
  tv <- freshTVar
  let env' = M.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  s2 <- unify tv t1
  let tnew = apply s2 tv
  let m2 = M.insert expr tnew m1
  pure (TypeResult (s1 <> s2) tnew m2)

ti γ@(TypeEnv env) expr@(EMatch e e1 x y e2) = do 
  TypeResult s0 te me <- ti γ e
  tv <- freshTVar 
  se <- unify te (TList tv)
  TypeResult s1 t1 m1 <- ti γ e1
  let env' = M.insert (EVar y) (generalize γ $ TList tv) $ M.insert (EVar x) (generalize γ tv) env
  TypeResult s2 t2 m2 <- ti (TypeEnv env') e2
  s12 <- unify (apply se t1) (apply se t2)
  let s = mconcat [s12, s2, s1, s2, s0]
  let texpr = apply s t1
  let m = M.insert expr texpr (mconcat [me, m1, m2])
  pure (TypeResult s texpr m)

-- for Eq and Ne, it is not accurate 
getOp :: Binop -> Scheme
getOp = \case
  Plus  -> binType TInt TInt TInt
  Minus -> binType TInt TInt TInt
  Mul   -> binType TInt TInt TInt
  Div   -> binType TInt TInt TInt
  Eq    -> Forall [a] (TArr a (TArr a TBool)) where a = TVar "a"
  Ne    -> Forall [a] (TArr a (TArr a TBool)) where a = TVar "a"
  Lt    -> binType TInt TInt TBool
  Le    -> binType TInt TInt TBool
  And   -> binType TBool TBool TBool
  Or    -> binType TBool TBool TBool
  Cons  -> Forall [a] (a `TArr` (TList a `TArr` TList a)) where a = TVar "a"

binType :: Type -> Type -> Type -> Scheme
binType t1 t2 t3 = Forall [] (TArr t1 (TArr t2 t3))

getPairFresh :: HM (Type, Type)
getPairFresh = (,) <$> freshTVar <*> freshTVar

inferType :: CoreExpr -> Either String (Map CoreExpr Type)
inferType expr = do
  TypeResult subset _ mapResult <- evalState (runExceptT (ti (TypeEnv M.empty) (resugarMatch expr))) 0
  pure $ listToFix (M.map (apply subset) mapResult)

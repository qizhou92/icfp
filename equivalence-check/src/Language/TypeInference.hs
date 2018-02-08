module Language.TypeInference where

import           Control.Monad.Except
import           Control.Monad.State

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
  apply _ TInt              = TInt
  apply _ TBool             = TBool
  apply _ TNil              = TNil
  apply su (TList t)        = TList $ apply su t
  apply su t@(TVar _)       = M.findWithDefault t t (getSubst su)
  apply su (TArr t1 t2)     = TArr (apply su t1) (apply su t2)
  apply su (TPlus t1 t2)    = TPlus (apply su t1) (apply su t2)
  apply su (TProduct t1 t2) = TProduct (apply su t1) (apply su t2)
  apply su (TFix t1 t2)     = TFix t1 (apply (Subst (M.delete (TVar t1) (getSubst su))) t2)

  freeTvars TInt             = S.empty
  freeTvars TNil             = S.empty
  freeTvars TBool            = S.empty
  freeTvars (TList t)        = freeTvars t 
  freeTvars (TVar a)         = S.singleton (TVar a)
  freeTvars (TArr t1 t2)     = S.union (freeTvars t1) (freeTvars t2)
  freeTvars (TProduct t1 t2) = S.union (freeTvars t1) (freeTvars t2)
  freeTvars (TPlus t1 t2)    = S.union (freeTvars t1) (freeTvars t2)
  freeTvars (TFix x t)       = S.delete (TVar x) (freeTvars t) 

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

mgu :: Type -> Type -> HM Subst

mgu (TArr t1 t2) (TArr t3 t4) = do s1 <- mgu t1 t3
                                   s2 <- mgu (apply s1 t2) (apply s1 t4)
                                   return (s2 <> s1)

mgu (TVar a) t = varAsgn (TVar a) t
mgu t (TVar a) = varAsgn (TVar a) t 
mgu TInt TInt = return mempty
mgu TBool TBool = return mempty
mgu (TList a) (TList b) = mgu a b 
mgu t1 t2 = throwError ("types do not unify: " ++ show t1 ++ " vs ." ++ show t2 ++"\n")

varAsgn :: Type -> Type -> HM Subst
varAsgn a t
  | t == a         = return mempty
  | S.member a (freeTvars t) = throwError ("occur check fails: " ++ show a ++ " in " ++ show t)
  | otherwise      = return (Subst $ M.singleton a t)

generalize :: TypeEnv -> Type -> Scheme

generalize env t = do 
  let as = S.toList (S.difference (freeTvars t) (freeTvars env))
  Forall as t 

instantiate :: Scheme -> HM Type
instantiate (Forall as t) = do
  as' <- mapM (const freshTVar) as
  let s = M.fromList (zip as as')
  return (apply (Subst s) t)

freshTVar :: HM Type
freshTVar = do
  s <- get
  put (s+1)
  return (TVar ("newTypeVariable" ++ show s))

data TypeResult = TypeResult Subst Type (Map CoreExpr Type)
  deriving(Show)

ti :: TypeEnv -> CoreExpr -> HM TypeResult
ti _ expr@(EInt  _) = return (TypeResult mempty TInt (M.singleton expr TInt))
ti _ expr@(EBool _) = return (TypeResult mempty TBool (M.singleton expr TBool))
ti _ ENil = do
  a <- freshTVar
  return $ TypeResult mempty (TList a) mempty
ti (TypeEnv env) expr@(EVar x) = 
  case M.lookup (EVar x) env of
     Nothing -> throwError ("Unbound Variable: " ++ show x)
     Just s  -> do
       t <- instantiate s
       return (TypeResult mempty t (M.singleton expr t))

ti tEnv expr@(EBin op expr1 expr2) = do
  TypeResult s1 t1 m1 <- ti tEnv expr1
  TypeResult s2 t2 m2 <- ti tEnv expr2
  tv <- freshTVar
  opType <- instantiate $ getOp op
  s3 <- mgu (TArr t1 (TArr t2 tv)) opType
  let tnew = apply s3 tv
  let m3 = M.insert expr tnew (m1 <> m2)
  return (TypeResult (mconcat [s1, s2, s3]) tnew m3)

ti tEnv expr@(EIf expr1 expr2 expr3) = do
  TypeResult s1 t1 m1 <- ti tEnv expr1
  TypeResult s2 t2 m2 <- ti tEnv expr2
  TypeResult s3 t3 m3 <- ti tEnv expr3
  s4 <- mgu t1 TBool
  s5 <- mgu t2 t3
  let tnew = apply s5 t2
  let m5 = M.insert expr tnew (m1 <> m2 <> m3)
  let newSubSet = mconcat [s5, s4, s3, s2, s1]
  return (TypeResult newSubSet tnew m5)

ti (TypeEnv env) expr@(ELet var1 expr1 expr2) = do
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  let (TypeEnv env') = apply s1 (TypeEnv env)
  let t'  = generalize (TypeEnv env') t1
  TypeResult s2 t2 m2 <- ti  (TypeEnv (M.insert (EVar var1) t' env')) expr2
  let m3 = M.union m1 m2
  let m4 = M.insert expr t2 m3
  return (TypeResult (s1 <> s2) t2 m4) 

ti (TypeEnv env) expr@(EApp expr1 expr2) = do
  tv <- freshTVar
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  TypeResult s2 t2 m2 <- ti (apply s1 (TypeEnv env)) expr2
  s3 <- mgu (apply s2 t1) (TArr t2 tv)
  let m3 = M.union m1 m2
  let tnew = apply s3 tv
  let m4 = M.insert expr tnew m3
  return (TypeResult (mconcat [s3, s2, s1]) tnew m4)

ti (TypeEnv env) expr@(ELam var1 expr1) = do
  tv <- freshTVar
  let env' = M.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  let tnew = apply s1 (TArr tv t1)
  let m2 = M.insert expr tnew m1
  return (TypeResult s1 tnew m2)

-- not sure the rule for fix is correct
ti (TypeEnv env) expr@(EFix var1 expr1) = do 
  tv <- freshTVar
  let env' = M.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  s2 <- mgu tv t1
  let tnew = apply s2 tv
  let m2 = M.insert expr tnew m1
  return (TypeResult (s1 <> s2) tnew m2)
ti γ@(TypeEnv env) expr@(EMatch e e1 x y e2) = do 
  TypeResult s0 te me <- ti γ e
  tv <- freshTVar 
  se <- mgu te (TList tv)
  TypeResult s1 t1 m1 <- ti γ e1
  let env' = M.insert (EVar y) (generalize γ $ TList tv) $ M.insert (EVar x) (generalize γ tv) env
  TypeResult s2 t2 m2 <- ti (TypeEnv env') e2
  s12 <- mgu (apply se t1) (apply se t2)
  let s = mconcat [s12, s2, s1, s2, s0]
  let texpr = apply s t1
  let m = M.insert expr texpr (mconcat [me, m1, m2])
  return (TypeResult s texpr m)

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

getPairFresh :: HM (Type,Type)
getPairFresh = do
  t1 <- freshTVar
  t2 <- freshTVar
  return (t1,t2)

inferType :: CoreExpr -> Either String (Map CoreExpr Type)
inferType expr = do
  TypeResult subset _ mapResult <- evalState (runExceptT (ti (TypeEnv M.empty) (resugarMatch expr))) 0
  pure $ listToFix (M.map (apply subset) mapResult)

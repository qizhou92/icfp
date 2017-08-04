module Language.Equivalence.TypeInference where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.Types

type TV = String
data Type = TVar TV
           | TInt
           | TBool
           | TArr Type Type
  deriving (Eq, Ord,Show)

data Scheme = Forall [Type] Type

newtype TypeEnv = TypeEnv (Map.Map CoreExpr Scheme)

type Subst = Map.Map Type Type

class Substitutable a where
  apply  :: Subst -> a -> a
  freeTvars :: a -> Set.Set Type

instance Substitutable Type where
  apply _ TInt = TInt
  apply _ TBool = TBool
  apply subSet t@(TVar a) = Map.findWithDefault t t subSet
  apply subSet t@(TArr t1 t2) = (TArr (apply subSet t1) (apply subSet t2))

  freeTvars TInt = Set.empty
  freeTvars TBool = Set.empty
  freeTvars (TVar a) = Set.singleton (TVar a)
  freeTvars (TArr t1 t2) = (Set.union (freeTvars t1) (freeTvars t2) )

instance Substitutable Scheme where
  apply subSet (Forall boundVars t) = Forall boundVars (apply newSubSet t) 
                                      where newSubSet = foldr Map.delete subSet boundVars
  freeTvars (Forall boundVars t) = Set.difference (freeTvars t) (Set.fromList boundVars)

instance Substitutable a => Substitutable [a] where
  apply = map . apply
  freeTvars = foldr Set.union Set.empty . map freeTvars

instance  Substitutable TypeEnv where
  apply s (TypeEnv typeEnv) = TypeEnv  (Map.map (apply s) typeEnv)
  freeTvars (TypeEnv typeEnv) = freeTvars (Map.elems typeEnv)

andSubSet :: Subst -> Subst -> Subst
andSubSet s1 s2 = (Map.union) (Map.map (apply s1) s2) s1 

type HM a = ExceptT String (State Int) a

mgu :: Type -> Type -> HM Subst

mgu (TArr t1 t2) (TArr t3 t4) = do s1 <- mgu t1 t3
                                   s2 <- mgu t2 t4
                                   return (andSubSet s1 s2)

mgu (TVar a) t = varAsgn (TVar a) t
mgu t (TVar a) = varAsgn (TVar a) t 
mgu TInt TInt = return Map.empty
mgu TBool TBool = return Map.empty
mgu t1 t2 = throwError ("types do not unify: " ++ (show t1) ++ " vs ." ++ (show t2) ++"\n")

varAsgn :: Type -> Type -> HM Subst
varAsgn a t
  | t == a         = return Map.empty
  | (Set.member a (freeTvars t)) = throwError ("occur check fails: " ++ (show a) ++ " in " ++ (show t))
  | otherwise      = return (Map.singleton a t)

generalize :: TypeEnv -> Type -> Scheme

generalize env t = do 
  let as = Set.toList (Set.difference (freeTvars t) (freeTvars env))
  Forall as t  

instantiate :: Scheme -> HM Type

instantiate (Forall as t) = do
  as' <- mapM (\_ -> freshTVar) as
  let s = Map.fromList (zip as as')
  return (apply s t)

freshTVar :: HM Type
freshTVar = do
  s <- get
  put (s+1)
  return (TVar ("newTypeVariable" ++ (show s)))

ti :: TypeEnv -> CoreExpr -> HM (Subst, Type)
ti _ (EInt  _) = return (Map.empty , TInt)
ti _ (EBool _) = return (Map.empty , TInt)
ti _ (ENil ) = throwError "Cannot analysis ENil type"
ti (TypeEnv env) (EVar x) = 
  case (Map.lookup (EVar x) env) of
     Nothing -> throwError ("Unbounded Varaiablie: " ++ (show x))
     Just s  -> do
       t <- instantiate s
       return (Map.empty, t) 

ti tEnv (EBin op expr1 expr2) = do
  (s1,t1) <- (ti tEnv expr1)
  (s2,t2) <- (ti tEnv expr2)
  tv <- freshTVar
  opType <- (getOp op)
  s3 <- mgu (TArr t1 (TArr t2 tv)) opType
  return ((andSubSet (andSubSet s1 s2) s3),(apply s3 tv))

ti tEnv (EIf expr1 expr2 expr3) = do
  (s1,t1) <- (ti tEnv expr1)
  (s2,t2) <- (ti tEnv expr2)
  (s3,t3) <- (ti tEnv expr3)
  s4 <- mgu t1 TBool
  s5 <- mgu t2 t3
  return (andSubSet s5 (andSubSet s4 (andSubSet s3 (andSubSet s2 s1))), (apply s5 t2)) 

ti (TypeEnv env) (ELet var1 expr1 expr2) = do
  (s1 ,t1) <- ti (TypeEnv env) expr1
  let (TypeEnv env') = apply s1 (TypeEnv env)
  let t'  = generalize (TypeEnv env') t1
  (s2, t2) <- ti  (TypeEnv (Map.insert (EVar var1) t' env')) expr2
  return (andSubSet s1 s2, t2)

ti (TypeEnv env) (EApp expr1 expr2) = do
  tv <- freshTVar
  (s1,t1) <- ti (TypeEnv env) expr1
  (s2,t2) <- ti (apply s1 (TypeEnv env)) expr2
  s3 <- mgu (apply s2 t1) (TArr t2 tv)
  return (andSubSet s3 (andSubSet s2 s1), apply s3 tv)

ti (TypeEnv env) (ELam var1 expr1) = do
  tv <- freshTVar
  let env' = Map.insert (EVar var1) (Forall [] tv) env
  (s1,t1) <- ti (TypeEnv env') expr1
  return (s1, apply s1 (TArr tv t1))

-- not sure the rule for fix is correct
ti (TypeEnv env) (EFix var1 expr1) = do 
  tv <- freshTVar
  let env' = Map.insert (EVar var1) (Forall [] tv) env
  (s1,t1) <- ti (TypeEnv env') expr1
  s2 <- mgu tv t1
  return (andSubSet s1 s2, apply s2 tv)


 
-- for Eq and Ne, it is not accurate 
getOp :: Binop -> HM Type
getOp Plus = return (TArr TInt (TArr TInt TInt))
getOp Minus =return (TArr TInt (TArr TInt TInt))
getOp Mul  = return(TArr TInt (TArr TInt TInt))
getOp Div  = return (TArr TInt (TArr TInt TInt))
getOp Eq = return (TArr TInt (TArr TInt TBool))
getOp Ne =return (TArr TInt (TArr TInt TBool))
getOp Lt =return (TArr TInt (TArr TInt TBool))
getOp Le =return (TArr TInt (TArr TInt TBool))
getOp And =return (TArr TInt (TArr TInt TBool))
getOp Or =return (TArr TInt (TArr TInt TBool))
getOp Cons = throwError "cannot anlaysis Cons"

getPairFresh :: HM (Type,Type)
getPairFresh = do
  t1 <- freshTVar
  t2 <- freshTVar
  return (t1,t2)

main = do 
  let r =(evalState (runExceptT getPairFresh) 0)
  case r of
    Left err -> print err
    Right res -> print res
inferType :: CoreExpr -> Type
inferType = undefined


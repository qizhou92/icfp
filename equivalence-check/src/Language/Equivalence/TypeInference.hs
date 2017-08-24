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

data TypeResult = TypeResult Subst Type (Map.Map CoreExpr Type)
  deriving(Show)

ti :: TypeEnv -> CoreExpr -> HM TypeResult
ti _ expr@(EInt  _) = return (TypeResult (Map.empty) TInt (Map.insert expr TInt Map.empty))
ti _ expr@(EBool _) = return (TypeResult (Map.empty) TBool (Map.insert expr TBool Map.empty))
ti _ (ENil ) = throwError "Cannot analysis ENil type"
ti (TypeEnv env) expr@(EVar x) = 
  case (Map.lookup (EVar x) env) of
     Nothing -> throwError ("Unbounded Varaiablie: " ++ (show x))
     Just s  -> do
       t <- instantiate s
       return (TypeResult (Map.empty) t (Map.insert expr t Map.empty))

ti tEnv expr@(EBin op expr1 expr2) = do
  TypeResult s1 t1 m1 <- (ti tEnv expr1)
  TypeResult s2 t2 m2 <- (ti tEnv expr2)
  tv <- freshTVar
  opType <- (getOp op)
  s3 <- mgu (TArr t1 (TArr t2 tv)) opType
  let m3 = Map.union m1 m2
  let tnew = apply s3 tv
  let m4 = Map.insert expr tnew m3
  return (TypeResult (andSubSet (andSubSet s1 s2) s3) tnew m4)

ti tEnv expr@(EIf expr1 expr2 expr3) = do
  TypeResult s1 t1 m1 <- (ti tEnv expr1)
  TypeResult s2 t2 m2 <- (ti tEnv expr2)
  TypeResult s3 t3 m3 <- (ti tEnv expr3)
  s4 <- mgu t1 TBool
  s5 <- mgu t2 t3
  let m4 = (Map.union m1 (Map.union m2 m3))
  let tnew = apply s5 t2
  let m5 = Map.insert expr tnew m4
  let newSubSet = (andSubSet (andSubSet (andSubSet (andSubSet s5 s4) s3) s2) s1)
  return (TypeResult newSubSet tnew m5)

ti (TypeEnv env) expr@(ELet var1 expr1 expr2) = do
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  let (TypeEnv env') = apply s1 (TypeEnv env)
  let t'  = generalize (TypeEnv env') t1
  TypeResult s2 t2 m2 <- ti  (TypeEnv (Map.insert (EVar var1) t' env')) expr2
  let m3 = Map.union m1 m2
  let m4 = Map.insert expr t2 m3
  return (TypeResult (andSubSet s1 s2) t2 m4) 

ti (TypeEnv env) expr@(EApp expr1 expr2) = do
  tv <- freshTVar
  TypeResult s1 t1 m1 <- ti (TypeEnv env) expr1
  TypeResult s2 t2 m2 <- ti (apply s1 (TypeEnv env)) expr2
  s3 <- mgu (apply s2 t1) (TArr t2 tv)
  let m3 = Map.union m1 m2
  let tnew = apply s3 tv
  let m4 = Map.insert expr tnew m3
  return (TypeResult (andSubSet (andSubSet s3 s2) s1) tnew m4)

ti (TypeEnv env) expr@(ELam var1 expr1) = do
  tv <- freshTVar
  let env' = Map.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  let tnew = apply s1 (TArr tv t1)
  let m2 = Map.insert expr tnew m1
  return (TypeResult s1 tnew m2)

-- not sure the rule for fix is correct
ti (TypeEnv env) expr@(EFix var1 expr1) = do 
  tv <- freshTVar
  let env' = Map.insert (EVar var1) (Forall [] tv) env
  TypeResult s1 t1 m1 <- ti (TypeEnv env') expr1
  s2 <- mgu tv t1
  let tnew = apply s2 tv
  let m2 = Map.insert expr tnew m1
  return (TypeResult (andSubSet s1 s2) tnew m2)


 
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

infereType :: CoreExpr -> Either String (Map.Map CoreExpr Type)
infereType expr = do
  let r = (evalState (runExceptT (ti (TypeEnv Map.empty) expr)) 0)
  case r of
    Left err -> Left err
    Right (TypeResult subset t mapResult) -> Right (Map.map (apply subset) mapResult)

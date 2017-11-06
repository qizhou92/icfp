module Language.Equivalence.TypeInference (types, Type (..)) where
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.Types
import Language.Equivalence.Transformations


types :: Program -> Either String [(Var, Scheme)]
types prog =
  case (evalState (runExceptT (act prog)) 0) of
    Left  err -> Left err
    Right env -> Right $ listToFix [(x,s) | (EVar x, s) <- Map.toList $ tyEnv env]
   where
     act = foldM (\env (x,e) -> (insertEnv env x) <$> ti env (desugarMatch e)) initEnv 

initEnv :: TypeEnv
initEnv = TypeEnv $ Map.fromList
  [ (EVar $ Var "head", Forall [a] (TList a `TArr` a))
  , (EVar $ Var "tail", Forall [a] (TList a `TArr` TList a)) 
  ]
  where
    a = TVar "a"

insertEnv :: TypeEnv -> Var -> TypeResult -> TypeEnv
insertEnv env x (TypeResult _ t _) 
  = TypeEnv (Map.insert (EVar x) (generalize env t) (tyEnv env))

-- data TypeResult = TypeResult Subst Type (Map.Map CoreExpr Type)
-- ti :: TypeEnv -> CoreExpr -> HM TypeResult
-- infereType :: CoreExpr -> Either String (Map.Map CoreExpr Type)





-- NV: TypeEnv should map Variables to Scheme, not CoreExpr
newtype TypeEnv = TypeEnv {tyEnv :: Map.Map CoreExpr Scheme}

instance Monoid TypeEnv where
  mempty = TypeEnv mempty
  mappend (TypeEnv m1) (TypeEnv m2) = TypeEnv (mappend m1 m2)

type Subst = Map.Map Type Type

class Substitutable a where
  apply  :: Subst -> a -> a
  freeTvars :: a -> Set.Set Type

instance Substitutable Type where
  apply _ TInt              = TInt
  apply _ TBool             = TBool
  apply _ TNil              = TNil
  apply su (TList t)        = TList $ apply su t 
  apply su t@(TVar _)       = Map.findWithDefault t t su
  apply su (TArr t1 t2)     = TArr (apply su t1) (apply su t2)
  apply su (TPlus t1 t2)    = TPlus (apply su t1) (apply su t2)
  apply su (TProduct t1 t2) = TProduct (apply su t1) (apply su t2)
  apply su (TFix t1 t2)     = TFix t1 (apply (Map.delete (TVar t1) su) t2)

  freeTvars TInt             = Set.empty
  freeTvars TNil             = Set.empty
  freeTvars TBool            = Set.empty
  freeTvars (TList t)        = freeTvars t 
  freeTvars (TVar a)         = Set.singleton (TVar a)
  freeTvars (TArr t1 t2)     = (Set.union (freeTvars t1) (freeTvars t2) )
  freeTvars (TProduct t1 t2) = Set.union (freeTvars t1) (freeTvars t2)
  freeTvars (TPlus t1 t2)    = Set.union (freeTvars t1) (freeTvars t2)
  freeTvars (TFix x t)       = Set.delete (TVar x) (freeTvars t) 

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
                                   s2 <- mgu (apply s1 t2) (apply s1 t4)
                                   return (andSubSet s2 s1)

mgu (TVar a) t = varAsgn (TVar a) t
mgu t (TVar a) = varAsgn (TVar a) t 
mgu TInt TInt = return Map.empty
mgu TBool TBool = return Map.empty
mgu (TList a) (TList b) = mgu a b 
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
ti _ ENil = do
  a <- freshTVar
  return $ TypeResult mempty (TList a) mempty
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
  opType <- instantiate $ getOp op
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
ti γ@(TypeEnv env) expr@(EMatch e e1 x y e2) = do 
  TypeResult s0 te me <- ti γ e
  tv <- freshTVar 
  se <- mgu te (TList tv)
  TypeResult s1 t1 m1 <- ti γ e1
  let env' = Map.insert (EVar y) (generalize γ $ TList tv) $ Map.insert (EVar x) (generalize γ $ tv) env
  TypeResult s2 t2 m2 <- ti (TypeEnv env') e2
  s12 <- mgu (apply se t1) (apply se t2)
  let s = andSubSet s12 (andSubSet s2 (andSubSet s1 (andSubSet s2 s0)))
  let texpr = apply s t1
  let m = Map.insert expr texpr (mconcat [me, m1, m2])
  return (TypeResult s texpr m)


 
-- for Eq and Ne, it is not accurate 
getOp :: Binop -> Scheme
getOp Plus  = Forall [] (TArr TInt (TArr TInt TInt))
getOp Minus = Forall [] (TArr TInt (TArr TInt TInt))
getOp Mul   = Forall [] (TArr TInt (TArr TInt TInt))
getOp Div   = Forall [] (TArr TInt (TArr TInt TInt))
getOp Eq    = Forall [a] (TArr a (TArr a TBool)) where a = TVar "a"
getOp Ne    = Forall [a] (TArr a (TArr a TBool)) where a = TVar "a"
getOp Lt    = Forall [] (TArr TInt (TArr TInt TBool))
getOp Le    = Forall [] (TArr TInt (TArr TInt TBool))
getOp And   = Forall [] (TArr TInt (TArr TInt TBool))
getOp Or    = Forall [] (TArr TInt (TArr TInt TBool))
getOp Cons  = Forall [a] (a `TArr` (TList a `TArr` TList a)) where a = TVar "a"


getPairFresh :: HM (Type,Type)
getPairFresh = do
  t1 <- freshTVar
  t2 <- freshTVar
  return (t1,t2)

infereType :: CoreExpr -> Either String (Map.Map CoreExpr Type)
infereType expr = do
  let r = (evalState (runExceptT (ti (TypeEnv Map.empty) (desugarMatch expr))) 0)
  case r of
    Left err -> Left err
    Right (TypeResult subset _ mapResult) -> Right $ listToFix (Map.map (apply subset) mapResult)

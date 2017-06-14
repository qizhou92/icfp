module Language.Equivalence.Derivations where

import Language.Equivalence.Types

import qualified Data.List as L 


-------------------------------------------------------------------------------
------- | Derivations with History of choices ---------------------------------
-------------------------------------------------------------------------------

data Derivations 
  = DS { def       :: Der   -- | Default Derivation 
       , dscurrent :: [Der] -- | Current Derivations not yet returned 
       , dsold     :: [Der] -- | Old derivations not yet unwinded 
       }

unwind :: Derivations -> (Derivations, Der)
unwind (DS dd (d:ds) old) = (DS dd ds (old++[d]), d)
unwind (DS dd [] (o:os))  = unwind (DS dd (unwindDer o) os)
unwind (DS dd [] [])      = (DS dd [] [], dd)

initDerivations :: CoreExpr -> Derivations
initDerivations e = DS dd ds [] 
  where 
    ds = makeDerivations [] e
    dd = if null ds then Der RAAssume [] e e [] else head ds 


-------------------------------------------------------------------------------
------- | Derivations ---------------------------------------------------------
-------------------------------------------------------------------------------

data Der     = Der {drulename :: RuleName, 
                    denv      :: DEnv, 
                    dinExpr   :: CoreExpr, 
                    doutExpr  :: CoreExpr, 
                    dpremises :: [Der]} 

type DEnv    = [(Var, CoreExpr)]

data RuleName = RNConst | RNVar | RNOp | RNIteTrue | RNIteFalse | RNAbs 
              | RNFix | RNAppLam | RNAppFix | RASymbolic | RAAssume 
     deriving (Show, Eq)


-- Unwind picks a symbolic choice and evaluates it 
unwindDer :: Der -> [Der]
unwindDer der 
  | drulename der == RASymbolic
  = makeDerivations (denv der) (dinExpr der)
  | otherwise
  = do dds <- mapM unwindDer (dpremises der)
       return $ der {dpremises = dds}

makeDerivations :: DEnv -> CoreExpr -> [Der]
makeDerivations denv e@(EInt _)  
  = return $ Der RNConst denv e e []
makeDerivations denv e@(EBool _) 
  = return $ Der RNConst denv e e [] 
makeDerivations denv e@(EVar x) 
  | Just ex <- L.lookup x denv  
  = return $ Der RNVar denv e ex []
  | otherwise 
  = error ("makeDerivations failed on EVar: "  ++ show x)
makeDerivations denv e@(EBin bop e1 e2) 
  = do d1 <- makeDerivations denv e1
       d2 <- makeDerivations denv e2 
       return $ Der RNOp denv e (eBin bop (doutExpr d1) (doutExpr d2)) [d1,d2] 
makeDerivations denv e@(EIf b e1 e2) 
  = do dcondition <- makeDerivations denv b 
       d1 <- makeDerivations denv e1 
       d2 <- makeDerivations denv e2 
       -- d1 <- makeDerivations (i-1) denv e1
       -- d2 <- makeDerivations (i-1) denv e2 
       [Der RNIteTrue denv e (doutExpr d1) [dcondition,d1],
        Der RNIteFalse denv e (doutExpr d2) [dcondition,d2]]  
makeDerivations denv e@(ELam _ _)
  = return $ Der RNAbs denv e e [] 
makeDerivations denv e@(EFix _ _)
  = return $ Der RNFix denv e e [] 
makeDerivations denv e@(EApp e1 e2)
  = do d1 <- makeDerivations denv e1 
       makeAppDerivations denv e d1 (doutExpr d1) e1 e2 
makeDerivations denv e@(ELet x ex e') 
  | isFix e 
  = makeDerivations denv (subst (x, EFix x ex) e')
makeDerivations denv (ELet x ex e) 
  = makeDerivations denv (subst (x,ex) e) 
makeDerivations _ e@ENil 
  = error ("makeDerivations: undefined on " ++ show e)


makeAppDerivations :: DEnv -> CoreExpr -> Der -> CoreExpr -> CoreExpr -> CoreExpr -> [Der]
makeAppDerivations denv e d1 (EFix x e1') _ e2 
  = do d2 <- makeDerivations ((x,EFix x e1'):denv) (EApp e1' e2)
       return $ Der RNAppFix denv e (doutExpr d2) [d1, d2]
makeAppDerivations denv e d1 (ELam x e1') _ e2 
  = do d2 <- makeDerivations denv e2
       d3 <- makeDerivations ((x, doutExpr d2):denv) e1'
       return $ Der RNAppLam denv e (doutExpr d3) [d1, d2, d3]
makeAppDerivations _ _ _ e _ e2 
  = error ("makeAppDerivations without Lam: " ++ exprString e ++ "\nTO\n" ++ exprString e2)



eBin :: Binop -> CoreExpr -> CoreExpr -> CoreExpr
eBin Plus  (EInt n)  (EInt m)  = EInt (n + m)
eBin Minus (EInt n)  (EInt m)  = EInt (n - m)
eBin Mul   (EInt n)  (EInt m)  = EInt (n * m)
eBin Div   (EInt n)  (EInt m)  = EInt (n `div` m)
eBin Eq    (EInt n)  (EInt m)  = EBool (n == m)
eBin Ne    (EInt n)  (EInt m)  = EBool (n /= m)
eBin Eq    (EBool n) (EBool m) = EBool (n == m)
eBin Ne    (EBool n) (EBool m) = EBool (n /= m)
eBin Lt    (EInt n)  (EInt m)  = EBool (n <  m)
eBin Le    (EInt n)  (EInt m)  = EBool (n <= m)
eBin And   (EBool n) (EBool m) = EBool (n && m)
eBin Or    (EBool n) (EBool m) = EBool (n || m)
eBin bop   e1        e2        = EBin bop e1 e2 



instance Show Der where
  show  = showDerShort 

showDerShort der =  
    unwords (show <$> dpremises der) ++ "\n" 
    ++ "-------"
    ++ show (drulename der) 
    -- ++ show (denv der) ++ " |- " ++ exprString (dinExpr der) ++ " ~> " ++ exprString (doutExpr der) ++ "\n"  



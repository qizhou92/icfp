module Language.Equivalence.Derivations where

import Language.Equivalence.Types



predecessors :: CoreExpr -> [CoreExpr]
predecessors (EInt _) = []
predecessors (EBool _) = []
predecessors ENil = []
predecessors (EVar _) = []
predecessors (EBin _ e1 e2) = [e1, e2]
predecessors (EIf e1 e2 e3) = [e1, e2, e3]
predecessors (ELam _ _) = []
predecessors (EFix _ _) = []
predecessors (EApp e1 e2) = predecessorsApp e1 e2 
predecessors e@(ELet x ex e')
  | isFix e 
  = predecessors (subst (x, EFix x ex) e')
  | otherwise 
  = predecessors (subst (x,ex) e)

-- NV This does not make sense: should I evaluate it?
predecessorsApp :: CoreExpr -> CoreExpr -> [CoreExpr]
predecessorsApp e1 e2 = [e1, e2]




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
    ds = makeDerivations [] e e
    dd = if null ds then Der RAAssume [] e e e[] else head ds 


-------------------------------------------------------------------------------
------- | Derivations ---------------------------------------------------------
-------------------------------------------------------------------------------

data Der     = Der {drulename :: RuleName, 
                    denv      :: DEnv, 
                    dinExpr   :: CoreExpr, 
                    doutExpr  :: CoreExpr,
                    annotedExpr :: CoreExpr,
                    dpremises :: [Der]} 

type DEnv    = [(Var, CoreExpr)]

data RuleName = RNConst | RNVar | RNOp | RNIteTrue | RNIteFalse | RNAbs 
              | RNFix | RNAppLam | RNAppFix | RASymbolic | RAAssume 
     deriving (Show, Eq)


-- Unwind picks a symbolic choice and evaluates it 
unwindDer :: Der -> [Der]
unwindDer der 
  | drulename der == RASymbolic
  = makeDerivations (denv der) (dinExpr der) (annotedExpr der)
  | otherwise
  = do dds <- mapM unwindDer (dpremises der)
       return $ der {dpremises = dds}

makeDerivations :: DEnv -> CoreExpr->CoreExpr-> [Der]
makeDerivations denv e@(EInt _) e1
  = return $ Der RNConst denv e e e1 []
makeDerivations denv e@(EBool _) e1
  = return $ Der RNConst denv e e e1[] 
makeDerivations denv e@(EVar _) e1
  = return $ Der RNVar denv e e e1 []
makeDerivations denv e@(EBin bop e1 e2) e3@(EBin _ e4 e5)
  = do d1 <- makeDerivations denv e1 e4
       d2 <- makeDerivations denv e2 e5
       return $ Der RNOp denv e (eBin bop (doutExpr d1) (doutExpr d2)) e3 [d1,d2]
makeDerivations denv e@(EBin bop e1 e2) e3
  = do d1 <- makeDerivations denv e1 e1
       d2 <- makeDerivations denv e2 e2
       return $ Der RNOp denv e (eBin bop (doutExpr d1) (doutExpr d2)) e3 [d1,d2] 
makeDerivations denv e@(EIf b e1 e2) e3@(EIf b2 e4 e5)
  = do dcondition <- makeDerivations denv b b2
       d1 <- makeDerivations denv e1 e4
       d2 <- makeDerivations denv e2 e5
       -- d1 <- makeDerivations (i-1) denv e1
       -- d2 <- makeDerivations (i-1) denv e2 
       [Der RNIteTrue denv e (doutExpr d1) e3 [dcondition,d1],
        Der RNIteFalse denv e (doutExpr d2) e3 [dcondition,d2]]
makeDerivations denv e@(EIf b e1 e2) e3
  = do dcondition <- makeDerivations denv b b
       d1 <- makeDerivations denv e1 e1
       d2 <- makeDerivations denv e2 e2
       -- d1 <- makeDerivations (i-1) denv e1
       -- d2 <- makeDerivations (i-1) denv e2 
       [Der RNIteTrue denv e (doutExpr d1) e3 [dcondition,d1],
        Der RNIteFalse denv e (doutExpr d2) e3 [dcondition,d2]]   
makeDerivations denv e@(ELam _ _) e1
  = return $ Der RNAbs denv e e e1 [] 
makeDerivations denv e@(EFix var e1) e2@(EFix var2 e3)
  = do d1 <-makeDerivations denv (substituteCoreExpr (var,(EFix var e1)) e1) (substituteCoreExpr (var2,(EFix var2 e3)) e3)
       return $ Der RNFix denv e (doutExpr d1) e2 [d1]
makeDerivations denv e@(EFix var e1) e2
  = do d1 <-makeDerivations denv (substituteCoreExpr (var,(EFix var e1)) e1) (substituteCoreExpr (var,(EFix var e1)) e1)
       return $ Der RNFix denv e (doutExpr d1) e2 [d1]
makeDerivations denv e@(EApp e1 e2) e3@(EApp e4 _)
  = do d1 <- makeDerivations denv e1 e4
       makeAppDerivations denv e d1 (doutExpr d1) e1 e2 e3
makeDerivations denv e@(EApp e1 e2) e3
  = do d1 <- makeDerivations denv e1 e1
       makeAppDerivations denv e d1 (doutExpr d1) e1 e2 e3
makeDerivations denv e@(ELet x ex e') e3
  | isFix e 
  = makeDerivations denv (subst (x, EFix x ex) e') e3
makeDerivations denv (ELet x ex e) e3
  = makeDerivations denv (subst (x,ex) e) e3
makeDerivations _ e@ENil _
  = error ("makeDerivations: undefined on " ++ show e)


makeAppDerivations :: DEnv -> CoreExpr -> Der -> CoreExpr -> CoreExpr -> CoreExpr ->CoreExpr ->[Der]
makeAppDerivations denv e d1 (ELam x e1') _ e2 e3
  = do d2 <- makeDerivations denv e2 (EVar x)
       d3 <- makeDerivations denv (substituteCoreExpr (x, (doutExpr d2)) e1') e1'
       return $ Der RNAppLam denv e (doutExpr d3) e3 [d1, d2, d3]
makeAppDerivations _ _ _ e _ e2 _
  = error ("makeAppDerivations without Lam: " ++ exprString e ++ "\nTO\n" ++ exprString e2)


substituteCoreExpr :: (Var,CoreExpr) -> CoreExpr -> CoreExpr
substituteCoreExpr (variable,value) originalCoreExpr = case originalCoreExpr of
  EVar var-> if var == variable then value else (EVar var)
  EBin op c1 c2 -> EBin op (substituteCoreExpr (variable,value) c1) (substituteCoreExpr (variable,value) c2)
  EIf c1 c2 c3 -> EIf (substituteCoreExpr (variable,value) c1) (substituteCoreExpr (variable,value) c2) (substituteCoreExpr (variable,value) c3)
  EApp c1 c2 -> EApp (substituteCoreExpr (variable,value) c1) (substituteCoreExpr (variable,value) c2)
  ELam v1 c1 -> if v1 == variable then ELam v1 c1 else ELam v1 (substituteCoreExpr (variable,value) c1)
  ELet v1 c1 c2 -> ELet v1 (substituteCoreExpr (variable,value) c1) (substituteCoreExpr (variable,value) c2)
  _ ->originalCoreExpr

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
eBin Lt    (EBool n) (EBool m) = EBool (n < m)
eBin Le    (EBool n) (EBool m) = EBool (n <= m)
eBin And   (EBool n) (EBool m) = EBool (n && m)
eBin Or    (EBool n) (EBool m) = EBool (n || m)
eBin bop   e1        e2        = EBin bop e1 e2 



instance Show Der where
  show  = showDerShort 

showDerShort der =  
    unwords (show <$> dpremises der) ++ "\n" 
    ++ "-------"
    ++ show (drulename der)
    ++ "|- " ++ exprString (dinExpr der) ++ " ~> " ++ exprString (doutExpr der) ++ "annoted:" ++ exprString (annotedExpr der) ++ "\n"  

    -- ++ show (denv der) ++ " |- " ++ exprString (dinExpr der) ++ " ~> " ++ exprString (doutExpr der) ++ "\n"  



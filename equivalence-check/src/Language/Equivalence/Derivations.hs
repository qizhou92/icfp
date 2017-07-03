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
    ds = makeDerivations e
    dd = if null ds then Der RAAssume e [] else head ds 


-------------------------------------------------------------------------------
------- | Derivations ---------------------------------------------------------
-------------------------------------------------------------------------------

data Der     = Der {drulename :: RuleName, 
                    coreExpr  :: CoreExpr,
                    dpremises :: [Der]} 

type DEnv    = [(Var, CoreExpr)]

data RuleName = RNConst | RNVar | RNOp | RNIteTrue | RNIteFalse | RNFix | RNApp| RASymbolic | RAAssume 
     deriving (Show, Eq)


-- Unwind picks a symbolic choice and evaluates it 
unwindDer :: Der -> [Der]
unwindDer der 
  | drulename der == RASymbolic
  = makeDerivations (coreExpr der)
  | otherwise
  = do dds <- mapM unwindDer (dpremises der)
       return $ der {dpremises = dds}

makeDerivations ::CoreExpr-> [Der]
makeDerivations e@(EInt _)
  = return $ Der RNConst e []
makeDerivations e@(EBool _)
  = return $ Der RNConst e [] 
makeDerivations e@(EVar _)
  = return $ Der RNVar e []
makeDerivations e@(EBin _ e1 e2)
  = do d1 <- makeDerivations e1 
       d2 <- makeDerivations e2
       return $ Der RNOp e [d1,d2] 
makeDerivations e@(EIf b e1 e2)
  = do dcondition <- makeDerivations b
       d1 <- makeDerivations e1
       d2 <- makeDerivations e2
       [Der RNIteTrue e [dcondition,d1],
        Der RNIteFalse e [dcondition,d2]] 
makeDerivations (ELam _ e1)
  = makeDerivations e1
makeDerivations e@(EFix var e1)
  = do d1 <-makeDerivations (substituteCoreExpr (var,(EFix var e1)) e1)
       return $ Der RNFix e [d1]
makeDerivations e@(EApp e1 e2)
  = do d1 <- makeDerivations e1
       d2 <- makeDerivations e2
       return $ Der RNApp e [d1,d2] 
makeDerivations e@(ELet x ex e')
  | isFix e 
  = makeDerivations (subst (x, EFix x ex) e')
makeDerivations (ELet x ex e)
  = makeDerivations (subst (x,ex) e)
makeDerivations e@ENil
  = error ("makeDerivations: undefined on " ++ show e)


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
    ++ "|- " ++ exprString (coreExpr der)  ++ "\n"  

    -- ++ show (denv der) ++ " |- " ++ exprString (dinExpr der) ++ " ~> " ++ exprString (doutExpr der) ++ "\n"  



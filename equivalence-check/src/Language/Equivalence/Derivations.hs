module Language.Equivalence.Derivations where

import Language.Equivalence.Types
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State




-------------------------------------------------------------------------------
------- | Derivations with History of choices ---------------------------------
-------------------------------------------------------------------------------

data Derivations 
  = DS { def       :: Der   -- | Default Derivation 
       , dscurrent :: [Der] -- | Current Derivations not yet returned 
       , dsold     :: [Der] -- | Old derivations not yet unwinded 
       }


-------------------------------------------------------------------------------
------- | Derivations ---------------------------------------------------------
-------------------------------------------------------------------------------

data Der     = Der {drulename :: RuleName, 
                    coreExpr  :: CoreExpr,
                    originalCoreExpr :: CoreExpr,
                    dpremises :: [Der],
                    idNumber :: Int
                    } 
      deriving(Eq,Ord)

type DEnv    = [(Var, CoreExpr)]

data RuleName = RNConst | RNVar | RNOp | RNIte | RNFix | RNApp| RNLam | RASym
     deriving (Show, Eq,Ord)

data UnwindResult = UnwindResult (Set.Set CoreExpr) Int
     deriving (Eq, Show,Ord)


type UnwindState a = (State UnwindResult) a
-- Unwind picks a symbolic choice and evaluates it

getNewId :: UnwindState Int
getNewId = do
  (UnwindResult fixExprs newId) <- get
  put (UnwindResult fixExprs (newId+1))
  return newId

unwindDer :: Der -> UnwindState Der
unwindDer der@(Der RASym expr1 expr2 _ idNumber) = do
  theDer <- makeDerivations expr1 expr2
  return theDer
unwindDer der@(Der rule expr1 expr2 list idNumber) = do
  list1 <- mapM unwindDer list
  return (Der rule expr1 expr2 list1 idNumber)

makeDerivations :: CoreExpr -> CoreExpr->UnwindState Der
makeDerivations e@(EInt _) e2 = do
  idNumber <- getNewId
  return (Der RNConst e e2 [] idNumber)
makeDerivations e@(EBool _) e2 = do
  idNumber <- getNewId
  return (Der RNConst e e2 [] idNumber)
makeDerivations e@(EVar _) e2 = do
  idNumber <- getNewId
  return (Der RNVar e e2 [] idNumber)
makeDerivations e@(EBin _ e1 e2) e3@(EBin _ e4 e5)= do
  idNumber <- getNewId
  d1 <- makeDerivations e1 e4
  d2 <- makeDerivations e2 e5
  return (Der RNOp e e3 [d1,d2] idNumber) 
makeDerivations e@(EIf b e1 e2) e3@(EIf b2 e4 e5) = do
  idNumber <- getNewId
  condition <- makeDerivations b b2
  d1 <- makeDerivations e1 e4
  d2 <- makeDerivations e2 e5
  return (Der RNIte e e3 [condition,d1,d2] idNumber)
makeDerivations e@(ELam _ e1) e2@(ELam _ e3)= do
  idNumber <- getNewId
  d1 <- makeDerivations e1 e3
  return (Der RNLam e e2 [d1] idNumber)
makeDerivations e@(EFix var e1) e2@(EFix _ e3)= do
  idNumber <- getNewId
  (UnwindResult fixExprs newId) <- get
  if (Set.member e fixExprs) then (return (Der RASym e e2 [] idNumber))
    else do
           put (UnwindResult (Set.insert e fixExprs) newId)
           d1 <- makeDerivations (substituteCoreExpr (var,e) e1) e3
           return (Der RNFix e e2 [d1] idNumber)
makeDerivations e@(EFix var e1) e2 = do
  idNumber <- getNewId
  (UnwindResult fixExprs newId) <- get
  if (Set.member e fixExprs) then (return (Der RASym e e2 [] idNumber))
    else do
           put (UnwindResult (Set.insert e fixExprs) newId)
           d1 <- makeDerivations (substituteCoreExpr (var,e) e1) e1
           return (Der RNFix e e [d1] idNumber)
makeDerivations e@(EApp e1 e2) e3@(EApp e4 e5)= do
  idNumber <- getNewId
  d1 <- makeDerivations e1 e4
  d2 <- makeDerivations e2 e5
  return (Der RNApp e e3 [d1,d2] idNumber) 
makeDerivations e@(ELet _ _ _) _
  = error ("makeDerivations: undefined on " ++ show e)
makeDerivations e@ENil _
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
    ++ "|- " ++ exprString (coreExpr der)  ++ "id:" ++ show(idNumber der) ++ "\n"  

    -- ++ show (denv der) ++ " |- " ++ exprString (dinExpr der) ++ " ~> " ++ exprString (doutExpr der) ++ "\n"  

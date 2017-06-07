module Language.Equivalence.Verify (

   verify

) where


import Data.Monoid
import Data.List ((\\))
import Data.Maybe (fromMaybe)
import Language.Equivalence.Types
import Language.Equivalence.CHC (checkEntail)
import Language.Equivalence.Derivations 
import Language.Equivalence.Expr hiding (Var)
import qualified Data.Map   as M

import System.Exit

-------------------------------------------------------------------------------
-- | verify -------------------------------------------------------------------
-------------------------------------------------------------------------------

verify :: Bind -> Bind -> IO Result
verify (x1, p0) (x2, p1) = do 
  putStrLn ("DERIVATIONS FOR P0 = " ++ show x1 ++ " = ")
  putStrLn (show $  makeDerivations [] p0)
  putStrLn ("DERIVATIONS FOR P1 = " ++ show x2 ++ " = ")
  putStrLn (show $ makeDerivations [] p1)
  putStrLn ("DERIVATIONS FOR P1 APPLIED = " ++ show x1 ++ " = ")
  putStrLn (show $ makeDerivations [] (EApp p0 (EInt 0)) )
  Result (x1, x2) <$> vAux (initDerivations p0) (initDerivations p1) mempty
  where
    vAux :: Derivations -> Derivations -> DersInvs -> IO Bool
    vAux ders1 ders2 i = do
      ires <- checkInd p0 p1 i
      case ires of
        IsInd -> return True
        NonInd -> do let (ders1', d1) = unwind ders1 
                     let (ders2', d2) = unwind ders2
                     vders <- verifyDers d1 d2
                     case vders of
                      Nothing -> return False
                      Just i' -> vAux ders1' ders2' (i <> i')

-------------------------------------------------------------------------------
-- | checkInd -----------------------------------------------------------------
-------------------------------------------------------------------------------
-- NV Question: Why do I need p0 and p1 here?
checkInd :: CoreExpr -> CoreExpr -> DersInvs -> IO IndRes
checkInd _p0 _p1 iγ  = cAux mempty mempty (const mempty)
  where
    cAux :: DerCtxs -> DerCtxs -> ((CoreExpr, CoreExpr) -> Invariant) -> IO IndRes 
    cAux γ0 γ1 _ 
      | not ((γ0, γ1) `elem` dersInvsKeys iγ)
      = chooseDer e
      where
        e = (hd γ0, hd γ1)
    cAux γ0 γ1 ie = do 
      r <- φe `checkEntail` φγ
      if r 
        then return IsInd
        else do 
          let ie' x = if x == e then (φe <> φγ) else ie x  
          i0  <- or <$> mapM (\(γ0', γ0'') -> bothIsInd <$> cAux γ0' γ1 ie' <*> cAux γ0'' γ1 ie') (tiles γ0) 
          i1  <- or <$> mapM (\(γ1', γ1'') -> bothIsInd <$> cAux γ0 γ1' ie' <*> cAux γ0 γ1'' ie') (tiles γ1) 
          if i0 || i1  
            then return IsInd
            else return NonInd -- NV CHECK chooseRes <$> unwind p0 γ0 γ1 ie' <*> unwind p1 γ0 γ1 ie'
      where
        e  = (hd γ0, hd γ1)
        φe = ie e  
        φγ = dersInvsLookup (γ0,γ1) iγ

bothIsInd :: IndRes -> IndRes -> Bool
bothIsInd IsInd IsInd = True 
bothIsInd _ _         = False 

-- NV CHECL 
_chooseRes :: IndRes -> IndRes -> IndRes
_chooseRes IsInd _ = IsInd
_chooseRes _ IsInd = IsInd
_chooseRes x _     = x 

chooseDer :: (CoreExpr, CoreExpr) -> IO IndRes
chooseDer (e0, e1) 
  = putStrLn ("chooseDer on " ++ show (e0,e1))
     >> exitWith (ExitFailure 0)


-------------------------------------------------------------------------------
-- | unwind -------------------------------------------------------------------
-------------------------------------------------------------------------------
-- NV CHECK 
-- unwind :: CoreExpr -> DerCtxs -> DerCtxs -> a -> IO IndRes
-- unwind = error "TODO: unwind"


-------------------------------------------------------------------------------
-- | verifyDers ---------------------------------------------------------------
-------------------------------------------------------------------------------
verifyDers :: Der -> Der -> IO (Maybe DersInvs)
verifyDers _ _ = error "TODO: qizhou"



-------------------------------------------------------------------------------
-- | Data Structures ----------------------------------------------------------
-------------------------------------------------------------------------------

data IndRes  = IsInd | NonInd -- NV CHECK IndDers {_indRes0 :: Der, _indRes1 :: Der}

data DerCtxs = DerCtxs [CoreExpr]
  deriving (Eq, Ord, Show)

tiles :: DerCtxs -> [(DerCtxs, DerCtxs)]
-- Ordering is not important in splitting 
tiles (DerCtxs xs) = [(DerCtxs ys, DerCtxs (xs\\ys)) | ys <- powerset xs]
  where
   powerset = foldr (\x acc -> acc ++ (map ((:) x) acc)) [[]]

-- Ordering is not important in splitting 
-- tiles (DerCtxs xs) = [(DerCtxs xs1, DerCtxs xs2) | (xs1, xs2) <- (`splitAt` xs) <$> [0..length xs]]

hd :: DerCtxs -> CoreExpr
hd (DerCtxs (x:_)) = x
hd _               = error "hd.DerCtxs on empty list"


type Invariant = Expr
data DersInvs  = DersInvs (M.Map (DerCtxs, DerCtxs) Invariant)

dersInvsKeys :: DersInvs -> [(DerCtxs, DerCtxs)]
dersInvsKeys (DersInvs m) = M.keys m  

dersInvsLookup :: (DerCtxs, DerCtxs) -> DersInvs -> Invariant
dersInvsLookup k (DersInvs m) = fromMaybe mempty (M.lookup k m)

instance Monoid DerCtxs where
  mempty = DerCtxs mempty
  mappend (DerCtxs m1) (DerCtxs m2) = DerCtxs (m1 `mappend` m2) 

instance Monoid DersInvs where
  mempty  = DersInvs $ M.singleton (mempty,mempty) mempty
  mappend (DersInvs m1) (DersInvs m2) = DersInvs $ M.unionWith mappend m1 m2

instance Monoid Expr where
  mempty  = ExprConstant (ConstantBool True)
  mappend x y= MkAnd [x,y]

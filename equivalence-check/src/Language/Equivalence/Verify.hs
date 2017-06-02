module Language.Equivalence.Verify (

   verify
   , RuleName(..)
  
) where


import Data.Monoid
import Data.List ((\\))
import Data.Maybe (fromMaybe)
import Language.Equivalence.Types
import Language.Equivalence.Expr hiding (Var)
import qualified Data.Map   as M

import System.Exit

-------------------------------------------------------------------------------
-- | verify -------------------------------------------------------------------
-------------------------------------------------------------------------------

verify :: Bind -> Bind -> IO Result
verify (x1, p0) (x2, p1) = Result (x1, x2) <$> vAux mempty
  where
    vAux :: DersInvs -> IO Bool
    vAux i = do
      ires <- checkInd p0 p1 i
      case ires of
        IsInd -> return True
        IndDers d0 d1 -> do vders <- verifyDers d0 d1
                            case vders of
                              Nothing -> return False
                              Just i' -> vAux (i <> i')

-------------------------------------------------------------------------------
-- | checkInd -----------------------------------------------------------------
-------------------------------------------------------------------------------
checkInd :: CoreExpr -> CoreExpr -> DersInvs -> IO IndRes
checkInd p0 p1 iγ  = cAux mempty mempty (const mempty)
  where
    cAux :: DerCtxs -> DerCtxs -> ((CoreExpr, CoreExpr) -> Invariant) -> IO IndRes 
    cAux γ0 γ1 _ 
      | not ((γ0, γ1) `elem` dersInvsKeys iγ)
      = chooseDer e
      where
        e = (hd γ0, hd γ1)
    cAux γ0 γ1 ie = do 
      r <- φe `implies` φγ
      if r 
        then return IsInd
        else do 
          let ie' x = if x == e then (φe <> φγ) else ie x  
          i0  <- or <$> mapM (\(γ0', γ0'') -> bothIsInd <$> cAux γ0' γ1 ie' <*> cAux γ0'' γ1 ie') (tiles γ0) 
          i1  <- or <$> mapM (\(γ1', γ1'') -> bothIsInd <$> cAux γ0 γ1' ie' <*> cAux γ0 γ1'' ie') (tiles γ1) 
          if i0 || i1  
            then return IsInd
            else chooseRes <$> unwind p0 γ0 γ1 ie' <*> unwind p1 γ0 γ1 ie'
      where
        e  = (hd γ0, hd γ1)
        φe = ie e  
        φγ = dersInvsLookup (γ0,γ1) iγ

bothIsInd :: IndRes -> IndRes -> Bool
bothIsInd IsInd IsInd = True 
bothIsInd _ _         = False 

chooseRes :: IndRes -> IndRes -> IndRes
chooseRes IsInd _ = IsInd
chooseRes _ IsInd = IsInd
chooseRes x _     = x 

chooseDer :: (CoreExpr, CoreExpr) -> IO IndRes
chooseDer (e0, e1) 
  = putStrLn ("chooseDer on " ++ show (e0,e1))
     >> exitWith (ExitFailure 0)


implies :: Expr -> Expr -> IO Bool 
implies = error "Using checkEntail in CHC.hs"

-------------------------------------------------------------------------------
-- | unwind -------------------------------------------------------------------
-------------------------------------------------------------------------------
unwind :: CoreExpr -> DerCtxs -> DerCtxs -> a -> IO IndRes
unwind = error "TODO: unwind"


-------------------------------------------------------------------------------
-- | verifyDers ---------------------------------------------------------------
-------------------------------------------------------------------------------
verifyDers :: Der -> Der -> IO (Maybe DersInvs)
verifyDers (Der _ _ _ _) _ = error "TODO: qizhou"



-------------------------------------------------------------------------------
-- | Data Structures ----------------------------------------------------------
-------------------------------------------------------------------------------

data RuleName = RNConst | RNVar | RNOp | RNIteTrue | RNIteFalse | RNAbs 
              | RNFix | RNAppLam |RNAppFix

data IndRes  = IsInd | IndDers {_indRes0 :: Der, _indRes1 :: Der}

type DEnv    = [(Var, CoreExpr)]

data Der     = Der RuleName DEnv CoreExpr [Der] 

data DerCtxs = DerCtxs [CoreExpr]
  deriving (Eq, Ord)

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

instance Ord CoreExpr where 
  compare = error "todo"

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
  mempty  = mempty
  mappend (DersInvs m1) (DersInvs m2) = DersInvs $ M.unionWith mappend m1 m2

instance Monoid Expr where
  mempty  = ExprConstant (ConstantBool True)
  mappend x y= MkAnd [x,y]

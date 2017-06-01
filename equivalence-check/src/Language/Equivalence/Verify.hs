module Language.Equivalence.Verify (

   verify

) where


import Data.Monoid
import Language.Equivalence.Types
import Language.Equivalence.Expr hiding (Var)
import qualified Data.Map   as M

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
checkInd _ _ _ = error "TODO: checkInd"

-------------------------------------------------------------------------------
-- | verifyDers ---------------------------------------------------------------
-------------------------------------------------------------------------------
verifyDers :: Der -> Der -> IO (Maybe DersInvs)
verifyDers (Der _ _ _ _) _ = error "TODO: verifyDers"


-------------------------------------------------------------------------------
-- | unwind -------------------------------------------------------------------
-------------------------------------------------------------------------------
unwind :: DersInvs -> IO (Der, Der)
unwind (Der _ _ _ _) _ = error "TODO: unwind"


-------------------------------------------------------------------------------
-- | Data Structures ----------------------------------------------------------
-------------------------------------------------------------------------------

data RuleName  

data IndRes = IsInd | IndDers {_indRes0 :: Der, _indRes1 :: Der}

type DEnv   = [(Var, CoreExpr)]

data Der     = Der RuleName DEnv CoreExpr [Der] 

data DerCtxs = DerCtxs [CoreExpr]
  deriving (Eq, Ord)

instance Ord CoreExpr where 
  compare = error "todo"

type Invariant = Expr
data DersInvs  = DersInvs (M.Map (DerCtxs, DerCtxs) Invariant)

instance Monoid DersInvs where
  mempty  = mempty
  mappend (DersInvs m1) (DersInvs m2) = DersInvs $ M.unionWith mappend m1 m2

instance Monoid Expr where
  mempty  = ExprConstant (ConstantBool True)
  mappend x y= MkAnd [x,y]

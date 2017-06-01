module Language.Equivalence.Verify (

   verify

) where


import Data.Monoid
import Language.Equivalence.Types
import Language.Equivalence.Expr
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
verifyDers :: Ders -> Ders -> IO (Maybe DersInvs)
verifyDers _ _ = error "TODO: verifyDers"

-------------------------------------------------------------------------------
-- | Data Structures ----------------------------------------------------------
-------------------------------------------------------------------------------

data IndRes   = IsInd | IndDers {_indRes0 :: Ders, _indRes1 :: Ders}
data Ders
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

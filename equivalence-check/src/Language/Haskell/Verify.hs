module Language.Haskell.Verify (

   verify 

) where


import Language.Haskell.Types
import Data.Monoid
import Language.Haskell.Expr

-- NV This does not compile
-- import qualified Language.Haskell.Expr as Logic 

import qualified Data.Map   as M 

-------------------------------------------------------------------------------
-- | verify -------------------------------------------------------------------
-------------------------------------------------------------------------------

verify :: ProgramBind -> ProgramBind -> IO Result 
verify (x1,p0) (x2,p1) = Result (x1, x2) <$> vAux mempty 
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

checkInd :: Program -> Program -> DersInvs -> IO IndRes 
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
data DerCtxs = DerCtxs
  deriving (Eq, Ord)


type Invariant = Expr -- = Logic.Expr
data DersInvs = DersInvs (M.Map (DerCtxs, DerCtxs) Invariant)

instance Monoid DersInvs where
  mempty  = mempty
  mappend (DersInvs m1) (DersInvs m2) = DersInvs $ M.unionWith mappend m1 m2 


-- TODO replace this with Logic.Expr
instance Monoid Expr where 
  mempty  = ExprConstant (ConstantBool True)
  mappend x y= MkAnd [x,y]

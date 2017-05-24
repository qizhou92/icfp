module Language.Haskell.Verify (

   verify 

) where


import Language.Haskell.Types
import Data.Monoid 

import qualified Language.Haskell.Expr as Logic 
import qualified Data.HashMap.Strict   as M 

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

checkInd :: Program -> Program -> DersInvs -> IO IndRes 
checkInd _ _ _ = error "TODO: checkInd"

verifyDers :: Ders -> Ders -> IO (Maybe DersInvs)
verifyDers _ _ = error "TODO: verifyDers"

data IndRes   = IsInd | IndDers {_indRes0 :: Ders, _indRes1 :: Ders}
data Ders      
data DerCtxs
type Invariant = Logic.Expr
data DersInvs = DersInvs (M.HashMap (DerCtxs, DerCtxs) Invariant)

instance Monoid DersInvs where
  mempty  = DersInvs
  mappend = \_ _ -> DersInvs

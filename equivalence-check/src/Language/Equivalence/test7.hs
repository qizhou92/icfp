module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.Derivations
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.State
import Language.Equivalence.TypeInference
import Language.Equivalence.VerifyDerivation


main = do
  let zero = Types.EInt 0
  let one = Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let x = Types.Var "x"
  let f = Types.Var "f"
  let sum1 = Types.EBin Types.Plus (Types.EVar x) two
  let sum2 = Types.EBin Types.Plus (Types.EVar x) one
  let app1 = Types.EApp (Types.EVar f) zero
  let app2 = Types.EApp (Types.EVar f) one
  let lambada1 = Types.ELam x sum1
  let lambada2 = Types.ELam x sum2
  let lambadaF1 = Types.ELam f app1
  let lambadaF2 = Types.ELam f app2
  let coreExpr1 = Types.EApp lambadaF1 lambada1
  let coreExpr2 = Types.EApp lambadaF2 lambada2
  let (der1,state1) = runState (makeDerivations coreExpr1) (UnwindResult Set.empty 0)
  let (der2,state2) = runState (makeDerivations coreExpr2) state1
  verifyPairs der1 der2
  

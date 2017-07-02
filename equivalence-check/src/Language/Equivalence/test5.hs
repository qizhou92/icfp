module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Map as Map
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.VerifyDerivation
import Language.Equivalence.Derivations

main = do
  let t = (Types.Var "T")
  let x = (Types.Var "x")
  let y = (Types.Var "y")
  let a = (Types.Var "arg1")
  -- /y y+1
  let inside = Types.ELam y (Types.EBin Types.Plus (Types.EVar y) (Types.EInt 1))
  let inside2 = Types.ELam y (Types.EBin Types.Plus (Types.EVar y) (Types.EInt 2))
  -- apply T x
  let app1 = Types.EApp (Types.EVar t) (Types.EVar x)
  -- /x (apply T x) 
  let lambada1 = Types.ELam x app1
  -- /T /x (apply T x)
  let lambada2 = Types.ELam t lambada1
  -- apply (/T /x (apply T x)) (/y y+1)
  let app2 = Types.EApp lambada2 inside
  let app2_1 = Types.EApp lambada2 inside2
  let app3 = Types.EApp app2 (Types.EInt 2)
  let app3_1 = Types.EApp app2_1 (Types.EInt 2)
  let dEnv =[(a,(Types.ENil))]
  let d1 = (makeDerivations dEnv app3 app3) !! 0
  let d2 = (makeDerivations dEnv app3_1 app3_1) !! 0
  let (node1,number) = translateDT 0 d1
  print d1
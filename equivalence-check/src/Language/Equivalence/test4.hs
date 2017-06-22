module Language.Haskell.Test1 where
import Language.Equivalence.CHC
import Language.Equivalence.Expr
import qualified Data.Set as Set
import qualified Data.List as List
import Language.Equivalence.Verify
import qualified Language.Equivalence.Types as Types
import Language.Equivalence.VerifyDerivation
import Language.Equivalence.Derivations

main = do
  let x = Types.EVar (Types.Var "x")
  let y = Types.EVar (Types.Var "y")
  let one=Types.EInt 1
  let two=Types.EInt 2
  let three=Types.EInt 3
  let four=Types.EInt 4
  let coreExpr1 = Types.EBin Types.Plus y   one
  let coreExpr2 = Types.EBin Types.Plus y   two
  let lamExpr1 = Types.ELam (Types.Var "y") coreExpr1
  let lamExpr2 = Types.ELam (Types.Var "y") coreExpr2
  let xGtFour = Types.EBin Types.Lt x four
  let coreExpr3 = Types.EIf xGtFour lamExpr1 lamExpr2
  let apply1 = Types.EApp coreExpr3 x
  let dEnv= [((Types.Var "x"),Types.ENil)]
  let d1 = (makeDerivations dEnv apply1) !! 0
  let (node1,number) = translateDT 0 d1
  print node1
module Language.Haskell.Test where
import Language.Haskell.Expr
import Language.Haskell.CHC
import System.Process
import Text.ParserCombinators.Parsec

--- main is the function to write the CHC system to the file and call z3 on the file

--- main2 is the function to read the output file2 and parse the file

main = do
--- r1 is the predicate R1(Int) 
	let r1 = Function "R1" [IntegerSort]
-- x1 and x2 are the int variables
	let x1 = Var "x1" IntegerSort
	let x2 = Var "x2" IntegerSort
-- the following are the constant value
	let constantZero = (ExprConstant (ConstantInt 0))
	let constantTwo = (ExprConstant (ConstantInt 2))
	let constant41 = (ExprConstant (ConstantInt 41))
-- rule 1 is (x1 = 0) => R1(x1)
	let rule1 = Rule (MkEq  (ExprVar x1) constantZero) (ApplyFunction r1 [(ParameterVar x1)])	
	let sum1 = MkEq (ExprVar x2) (MkAdd [(ExprVar x1),constantTwo])
-- rule 2 is R1(x1) /\ (x2 = x1 +2) => R1(x2) 
	let rule2 = Rule (MkAnd [sum1,(ApplyFunction r1 [(ParameterVar x1)])]) (ApplyFunction r1 [(ParameterVar x2)])
	let equal41 = MkEq (ExprVar x1) constant41
-- query is R(x1) /\ (x1==41)
	let query = MkAnd [equal41, (ApplyFunction r1 [(ParameterVar x1)])]
-- build the CHC system, the first list is rules, the second list is predicates, the third
-- list is variables, and the last is query expression
	let theCHC = CHC [rule1,rule2] [r1] [x1,x2] query
	chc_write_file theCHC
	callCommand "z3 test.z3 > output1.txt"
main2 :: IO ()
main2 = do
	x <-readFile "./output1.txt"
	print (show (parse parseCHCResult "unknonw.txt" x))
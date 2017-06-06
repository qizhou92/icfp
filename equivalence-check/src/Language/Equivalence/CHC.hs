module Language.Equivalence.CHC where
import qualified Data.Map as Map
import Language.Equivalence.Expr
import System.Process
import System.Exit
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec

data Rule = Rule Expr Expr

rule_pretty_print :: Rule -> String

rule_pretty_print (Rule b h) = "(rule (=> " ++ (expr_pretty_print b) ++ "  "++ (expr_pretty_print h) ++ " ))"

rule_list_pretty_print :: [Rule] -> String
rule_list_pretty_print list = case list of 
    x:xs -> (rule_pretty_print x) ++ "\n" ++ (rule_list_pretty_print xs)
    [] -> "\n"

data CHC = CHC [Rule] [Function] [Var] Expr

add_rule :: Rule->CHC -> CHC

add_rule  newRule (CHC rules predicates variables query) = (CHC (newRule:rules) predicates variables query)

decl_var :: Var -> String
decl_var (Var name sort) = case sort of 
    BoolSort -> "(declare-const " ++ name ++ " Bool)"
    IntegerSort -> "(declare-const " ++ name ++ " Int)"
    RealSort -> "(declare-const " ++ name ++ " Real)"

checkEntail :: Expr -> Expr -> IO Bool
checkEntail expr1 expr2 = do
  let varList = (collectVar expr1) ++ (collectVar expr2)
  let list = Set.toList (Set.fromList varList)
  let string1 = unlines (map decl_var list)
  let expr3 = MkAnd [expr1, (MkNot expr2)]
  let string2 = "(assert " ++ (expr_pretty_print  expr3) ++ " )\n (check-sat)\n"
  writeFile "./test.z3" (string1++string2)
  callCommand "z3 test.z3 > output1.txt"
  x <-readFile "./output1.txt"
  if x == "unsat\n"
     then return True
     else return False

register_predicate :: Function -> CHC -> CHC

register_predicate newPredicates (CHC rules predicates variables query)
  | elem newPredicates predicates = (CHC rules predicates variables query)
  | otherwise = (CHC rules (newPredicates:predicates) variables query)

add_varaible :: Var -> CHC -> CHC

add_varaible newVar (CHC rules predicates variables query)
  | elem newVar variables = (CHC rules predicates variables query)
  | otherwise = (CHC rules predicates (newVar:variables) query)

decl_var_list_pretty_print :: [Var] -> String

decl_var_pretty_print :: Var -> String
decl_var_pretty_print (Var name sort) = case sort of 
    BoolSort -> "(declare-var " ++ name ++ " Bool)"
    IntegerSort -> "(declare-var " ++ name ++ " Int)"
    RealSort -> "(declare-var " ++ name ++ " Real)"

decl_var_list_pretty_print list = case list of
    x:xs -> (decl_var_pretty_print x) ++ "\n" ++ (decl_var_list_pretty_print xs)
    [] -> "" 

decl_predicate_pretty_print :: Function -> String
decl_predicate_pretty_print (Function functionName sortList) = "(declare-rel "++ functionName ++ "  (" ++ (sort_list_pretty_print sortList) ++ " ) )"

decl_predicate_list_pretty_print :: [Function] -> String
decl_predicate_list_pretty_print list = case list of
    x:xs -> (decl_predicate_pretty_print x) ++ "\n" ++ (decl_predicate_list_pretty_print xs)
    [] -> "(declare-rel Goal ()) \n"

query_pretty_print :: Expr -> String
query_pretty_print query= "(rule (=> " ++ (expr_pretty_print query) ++ " Goal))\n (query Goal :print-certificate true)"

chc_pretty_print :: CHC -> String
chc_pretty_print (CHC rules predicates variables query) = do
    "(set-option :fixedpoint.engine \"duality\")\n" ++ (decl_predicate_list_pretty_print predicates) ++ (decl_var_list_pretty_print variables) ++ (rule_list_pretty_print rules) ++ (query_pretty_print query)

chc_write_file :: CHC -> IO()
chc_write_file theCHC = writeFile "./test.z3" (chc_pretty_print theCHC)


chc_execute :: CHC -> IO (Bool, (Map.Map Function Expr))
chc_execute theCHC = do
  chc_write_file theCHC
  callCommand "z3 test.z3 > output1.txt"
  x <-readFile "./output1.txt"
  let result  = parse parseCHCResult "unknonw.txt" x
  case result of 
     Left e -> do
                print ("error in parse"++(show e)) 
                exitWith (ExitFailure 10)
     Right result -> return result


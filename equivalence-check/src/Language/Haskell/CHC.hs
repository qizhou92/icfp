module Language.Haskell.CHC where

import Language.Haskell.Expr
import Data.List

data Rule = Rule Expr Expr

rule_pretty_print :: Rule -> String

rule_pretty_print (Rule h b) = "(rule (=> " ++ (expr_pretty_print h) ++ "  "++ (expr_pretty_print b) ++ " ))"

rule_list_pretty_print :: [Rule] -> String
rule_list_pretty_print list = case list of 
    x:xs -> (rule_pretty_print x) ++ "\n" ++ (rule_list_pretty_print xs)
    otherwise -> "\n"

data CHC = CHC [Rule] [Function] [Var] Expr

add_rule :: Rule->CHC -> CHC

add_rule  newRule (CHC rules predicates variables query) = (CHC (newRule:rules) predicates variables query)



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
    BoolSort -> "(declare-var " ++ (show name) ++ " Bool)"
    IntegerSort -> "(declare-var " ++ (show name) ++ " Int)"
    RealSort -> "(declare-var " ++ (show name) ++ " Real)"

decl_var_list_pretty_print list = case list of
    x:xs -> (decl_var_pretty_print x) ++ "\n" ++ (decl_var_list_pretty_print xs)
    otherwise -> "" 

decl_predicate_pretty_print :: Function -> String
decl_predicate_pretty_print (Function functionName sortList) = "(declare-rel "++ functionName ++ "  (" ++ (sort_list_pretty_print sortList) ++ " ) )"

decl_predicate_list_pretty_print :: [Function] -> String
decl_predicate_list_pretty_print list = case list of
    x:xs -> (decl_predicate_pretty_print x) ++ "\n" ++ (decl_predicate_list_pretty_print xs)
    otherwise -> "(declare-rel Goal ()) \n"

query_pretty_print :: Expr -> String
query_pretty_print query= "(rule (=> " ++ (expr_pretty_print query) ++ " Goal))\n (query Goal : print-certificate true)"

chc_pretty_print :: CHC -> String
chc_pretty_print (CHC rules predicates variables query) = do
    (decl_predicate_list_pretty_print predicates) ++ (decl_var_list_pretty_print variables) 
    ++ (rule_list_pretty_print rules) ++ (query_pretty_print query)


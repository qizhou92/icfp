module Language.Haskell.CHC where

import Z3.Monad
import Language.Haskell.Expr
import Data.List

data Rule = Rule Expr Expr

rule_pretty_print :: Rule -> IO ()

rule_pretty_print (Rule h b) = do
	             print "(rule (=> "
	             expr_pretty_print h
	             expr_pretty_print b
	             print "))"

data CHC = CHC [Rule] [Function] [Var] Rule

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

decl_var_pretty_print :: [Var] -> IO ()
decl_var_pretty_print = undefined

decl_predicate_pretty_print :: [Function] -> IO ()
decl_predicate_pretty_print = undefined

query_pretty_print :: Rule -> IO ()
query_pretty_print = undefined

chc_pretty_print :: CHC -> IO()
chc_pretty_print = undefined


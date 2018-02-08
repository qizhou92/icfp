module Grammar.Chc where

import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M

import           Formula
import qualified Formula.Z3 as Z3

import           Grammar.Grammar

runSystem :: (Symbol sym, Ord sym) => [Chc] -> IO (Either Model (Map sym Expr))
runSystem clauses = runExceptT (interpretModel <$> Z3.solveChc clauses)
  where
    interpretModel m =
      M.mapKeys (interpret . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

clause :: Symbol sym => Production sym -> Chc
clause (Production _ lhs f rhs) = Rule (map app rhs) f (app lhs)

app :: Symbol sym => Nonterminal sym -> App
app (Nonterminal sym vs) = mkApp ("R" ++ generate sym) vs

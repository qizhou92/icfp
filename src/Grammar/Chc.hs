module Grammar.Chc where

import           Control.Monad.Except

import           Data.Map (Map)
import qualified Data.Map as M

import           Formula hiding (Rule)
import qualified Formula as F
import qualified Formula.Z3 as Z3

import           Grammar.Grammar

runSystem :: [Chc] -> IO (Either Model (Map Symbol Expr))
runSystem clauses = runExceptT (interpretModel <$> Z3.solveChc clauses)
  where
    interpretModel m =
      M.mapKeys (read . tail)
      $ M.filterWithKey (\k _ -> head k == 'R')
      $ M.mapKeys _varName m

clause :: Rule -> Chc
clause (Rule _ lhs f rhs) = F.Rule (map app rhs) f (app lhs)

app :: Nonterminal -> App
app (Nonterminal sym vs) = mkApp ("R" ++ show (primaryID sym)) vs

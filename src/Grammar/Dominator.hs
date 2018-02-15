module Grammar.Dominator where

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Grammar.Grammar

type DomTable = Map Symbol (Set Symbol)

search :: DomTable -> Symbol -> Set Symbol
search m sym = M.findWithDefault S.empty sym m

dominators :: DomTable
           -> (DomTable -> [Rule] -> [Set Symbol])
           -> (Symbol -> [Rule] -> [Rule])
           -> Grammar
           -> DomTable
dominators initial rSyms rSel (Grammar _ rs) = loop initial
  where
    loop m = let m' = iter m in if m == m' then m' else loop m'
    iter m = foldr step m (symbols rs)
    inters ss = case ss of
      [] -> S.empty
      _ -> foldr1 S.intersection ss
    step sym m =
      let rs' = rSel sym rs -- select the rules involving the current symbol
          ps = rSyms m rs'  -- select the dominators from the appropriate symbols in the rule
          new = S.insert sym (inters ps) -- update the dominators
      in M.insert sym new m

predominators :: Grammar -> DomTable
predominators g@(Grammar _ rs) = dominators initial rSyms rulesFor g
  where
    syms = symbols rs
    initial = M.fromList (zip (S.toList syms) (repeat syms))
    rSyms m = map (\r -> S.unions $ map (search m) (S.toList $ rhsSymbols r))

postdominators :: Grammar -> DomTable
postdominators g@(Grammar start rs) = dominators initial rSyms rulesWith g
  where
    syms = symbols rs
    initial = M.insert start (S.singleton start) $
      M.fromList (zip (S.toList syms) (repeat syms))
    rSyms m = map (search m . lhsSymbol)

backRules :: Grammar -> [Rule]
backRules g@(Grammar _ rs) = filter isBack rs
  where
    predominates x y = x `elem` search (predominators g) y
    postdominates x y = x `elem` search (postdominators g) y
    isBack r = any (\sym -> (lhsSymbol r `predominates` sym)
                         || (sym `postdominates` lhsSymbol r)) (rhsSymbols r)

nonrecursive :: Grammar -> Grammar
nonrecursive g@(Grammar start rs) = Grammar start (filter (`notElem` backRules g) rs)

module Grammar.Dominator where

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Grammar.Grammar

type DomTable sym = Map sym (Set sym)

search :: Ord sym => DomTable sym -> sym -> Set sym
search m sym = M.findWithDefault S.empty sym m

dominators :: (Data sym, Ord sym)
           => DomTable sym
           -> (DomTable sym -> [Production sym] -> [Set sym])
           -> (sym -> [Production sym] -> [Production sym])
           -> Grammar sym
           -> DomTable sym
dominators initial rSyms rSel (Grammar _ rs) = loop initial
  where
    loop m = let m' = iter m in if m == m' then m' else loop m'
    iter m = foldr step m (symbols rs)
    inters ss = case ss of
      [] -> S.empty
      _ -> foldr1 S.intersection ss
    step sym m =
      let rs' = rSel sym rs -- select the productions involving the current symbol
          ps = rSyms m rs'  -- select the dominators from the appropriate symbols in the production
          new = S.insert sym (inters ps) -- update the dominators
      in M.insert sym new m

predominators :: (Data sym, Ord sym) => Grammar sym -> DomTable sym
predominators g@(Grammar _ rs) = dominators initial rSyms productionsFor g
  where
    syms = symbols rs
    initial = M.fromList (zip (S.toList syms) (repeat syms))
    rSyms m = map (\r -> S.unions $ map (search m) (S.toList $ rhsSymbols r))

postdominators :: (Data sym, Ord sym) => Grammar sym -> DomTable sym
postdominators g@(Grammar start rs) = dominators initial rSyms productionsWith g
  where
    syms = symbols rs
    initial = M.insert start (S.singleton start) $
      M.fromList (zip (S.toList syms) (repeat syms))
    rSyms m = map (search m . lhsSymbol)

backProductions :: (Data sym, Ord sym) => Grammar sym -> [Production sym]
backProductions g@(Grammar _ rs) = filter isBack rs
  where
    predominates x y = x `elem` search (predominators g) y
    postdominates x y = x `elem` search (postdominators g) y
    isBack r = any (\sym -> (lhsSymbol r `predominates` sym)
                         || (sym `postdominates` lhsSymbol r)) (rhsSymbols r)

nonrecursive :: (Data sym, Ord sym) => Grammar sym -> Grammar sym
nonrecursive g@(Grammar start rs) = Grammar start (filter (`notElem` backProductions g) rs)

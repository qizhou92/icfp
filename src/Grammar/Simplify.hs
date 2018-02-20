module Grammar.Simplify where

import           Control.Lens

import           Data.Foldable
import qualified Data.Set as S
import qualified Data.Map as M

import           Formula hiding (Rule)

import           Grammar.Grammar

-- | There are two rules for logical grammar simplification:
-- If there is a nonterminal with cardinality one (that is non-recursive), inline the body
-- at all occurrences, deleting the rule for the nonterminal (the start symbol cannot be inlined).
-- If there is a nonterminal with multiple rules that share the same nonterminals in the body,
-- disjoin them into a single rule.
-- Repeat the rules into no more reductions are possible.
simplify :: Grammar -> Grammar
simplify = over grammarRules (map cleanUp) . loop
  where
    loop g =
      let g' = disjoin $ inline g
      in if g' == g then g' else loop g'

    cleanUp (Rule cats lhs f ps) =
      Rule cats lhs (varElim (varSet lhs `S.union` varSet ps) f) ps

inline :: Grammar -> Grammar
inline g@(Grammar start rs) =
  let preserve = S.insert start $ foldMap (\(s, tar, _) -> S.fromList [s, tar]) (phantoms g)
      toInline = S.filter (\inst -> inst `notElem` preserve && cardinality inst rs == 1) (instances rs)
      rs' = foldr (\inst rs' -> inlineRule (head $ rulesFor inst rs') rs') rs toInline
  in Grammar start rs'

-- | Substitute occurrences of the rule left hand side instance with the body of the rule.
inlineRule :: Rule -> [Rule] -> [Rule]
inlineRule (Rule _ lhs body rhs) g =
  delete sym $ map
    (\(Rule cats lhs' f rhs') ->
      if sym `elem` foldMap (S.singleton . nonterminalPrimary) rhs'
      then uncurry (Rule cats lhs') $ repRHS (f, rhs')
      else Rule cats lhs' f rhs') g
  where
    sym = nonterminalPrimary lhs
    repRHS (f, ps) = repRHS' ([], f, ps)
    repRHS' (acc, f, p:ps) =
      if nonterminalPrimary p == sym
      then repRHS' (rhs ++ acc, mkAnd f body, ps)
      else repRHS' (p : acc, f, ps)
    repRHS' (acc, f, []) = (f, acc)

disjoin :: Grammar -> Grammar
disjoin (Grammar start rs)  = Grammar start $ foldr disjoinCandidate rs candidates
  where
    disjoinCandidate rs' g' = disjoinRules rs' : filter (`notElem` rs') g'
    candidates = M.elems (M.filter (\rs' -> length rs' > 1) instMap)
    -- a map from all instances in a rule to corresponding rules
    instMap = foldr addInstEntry M.empty rs
    addInstEntry r@(Rule ct lhs _ rhs) =
      M.insertWith (++) (ct, map (view nonterminalID) (lhs : rhs)) [r]

disjoinRules :: [Rule] -> Rule
disjoinRules rules =
  let rs = map rename rules in
  first & ruleBody .~ manyOr (map _ruleBody rs)
  where
    prodVars r = concatMap _nonterminalVars (_ruleLHS r : _ruleRHS r)
    first = head rules
    rename r =
      let m = M.fromList (zip (prodVars r) (prodVars first))
      in subst m r

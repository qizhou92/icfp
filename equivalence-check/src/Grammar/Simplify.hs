module Grammar.Simplify where

import           Control.Lens

import           Data.Foldable
import qualified Data.Set as S
import qualified Data.Map as M

import           Formula

import           Grammar.Grammar

-- | There are two ruels for logical grammar simplification:
-- If there is a nonterminal with cardinality one (that is non-recursive), inline the body
-- at all occurrences, deleting the production for the nonterminal (the start symbol cannot be inlined).
-- If there is a nonterminal with multiple productions that share the same nonterminals in the body,
-- disjoin them into a single production.
-- Repeat the productions into no more reductions are possible.
simplify :: MonadVocab m => Grammar Int -> m (Grammar Int)
simplify = fmap (over grammarProductions (map cleanUp)) . loop
  where
    loop g = do
      g' <- disjoin <$> inline g
      if g' == g then pure g' else loop g'

    cleanUp (Production cats lhs f ps) =
      Production cats lhs (varElim (varSet lhs `S.union` varSet ps) f) ps

inline :: MonadVocab m => Grammar Int -> m (Grammar Int)
inline (Grammar start rs) = do
  let toInline = S.filter (\inst -> inst /= start && cardinality inst rs == 1) (instances rs)
  rs' <- foldrM (\inst rs' -> inlineProduction (head $ productionsFor inst rs') rs') rs toInline
  pure (Grammar start rs')

-- | Substitute occurrences of the production left hand side instance with the body of the production.
inlineProduction :: MonadVocab m => Production Int -> [Production Int] -> m [Production Int]
inlineProduction (Production _ lhs body rhs) g =
  delete sym <$> mapM (\(Production cats lhs' f rhs') -> uncurry (Production cats lhs') <$> repRHS (f, rhs')) g
  where
    sym = lhs ^. nonterminalSymbol
    repRHS (f, ps) = repRHS' ([], f, ps)
    repRHS' (acc, f, p:ps) =
      if (p ^. nonterminalSymbol) == sym
      then do
        (f', ps') <- freshen (M.fromList $ zip (lhs ^. nonterminalVars ) (p ^. nonterminalVars)) (body, rhs)
        repRHS' (ps' ++ acc, mkAnd f f', ps)
      else repRHS' (p : acc, f, ps)
    repRHS' (acc, f, []) = pure (f, acc)

disjoin :: Grammar Int -> Grammar Int
disjoin (Grammar start rs)  = Grammar start $ foldr disjoinCandidate rs candidates
  where
    disjoinCandidate rs' g' = disjoinProductions rs' : filter (`notElem` rs') g'
    candidates = M.elems (M.filter (\rs' -> length rs' > 1) instMap)
    -- a map from all instances in a production to corresponding productions
    instMap = foldr addInstEntry M.empty rs
    addInstEntry r@(Production ct lhs _ rhs) =
      M.insertWith (++) (ct, map (view nonterminalSymbol) (lhs : rhs)) [r]

disjoinProductions :: [Production Int] -> Production Int
disjoinProductions productions =
  let rs = map rename productions in
  first & productionBody .~ manyOr (map _productionBody rs)
  where
    prodVars r = concatMap _nonterminalVars (_productionLHS r : _productionRHS r)
    first = head productions
    rename r =
      let m = M.fromList (zip (prodVars r) (prodVars first))
      in subst m r

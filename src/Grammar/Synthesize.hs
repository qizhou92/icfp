module Grammar.Synthesize where

import           Control.Lens
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Formula hiding (Rule)
import qualified Formula.Z3 as Z3
import           Grammar.Grammar

synthesizeInvariants :: Set Symbol -> Clones -> Grammar -> Map Symbol Expr -> Map Symbol (Expr, Expr)
synthesizeInvariants ind cs (Grammar start rs') m = evalState (rec L start) S.empty
  where
    rs = filter (all (`elem` ind) . ruleSymbols) rs'
    rec dir = visit M.empty (\sym ->
      if sym `notElem` ind
      then pure M.empty
      else let f = M.findWithDefault (LBool True) sym m
               m' = if hasUniqueDirection sym
                    then single (original sym) f f
                    else case dir of
                           L -> single (original sym) f (LBool True)
                           R -> single (original sym) (LBool True) f
           in do ms <- mapM (\(Rule ct _ _ rhs) ->
                   merges <$> mapM (rec ct . nonterminalPrimary) rhs) (rulesFor sym rs)
                 pure $ merges (m':ms))

    single sym l r = M.singleton sym (l, r)
    original sym = S.findMin (cloneFor sym cs)
    hasUniqueDirection sym = length (S.fromList $ map (view ruleCategory) (rulesWith sym rs)) < 2
    merge = M.unionWith (\(a, b) (c, d) -> (mkOr a c, mkOr b d))
    merges = foldr merge M.empty

-- Construct the populated CHC for each rule and check it is valid (including the query)
validate :: Grammar -> Expr -> Map Symbol (Expr, Expr) -> IO Bool
validate (Grammar start rs) q m = do
  rs' <- mapM runVRule rs
  q' <- Z3.forallIsSat (mkImpl (fst (exprsFor start)) q)
  pure (and (q':rs'))
  where
    runVRule r =
      Z3.forallIsSat (vRule r)

    vRule (Rule dir lhs f rhs) = mkImpl (manyAnd (f : map (insProd dir) rhs)) (insProd dir lhs)

    insProd dir (Nonterminal sym vs) =
      let fs = exprsFor (primaryID sym)
      in case dir of
        L -> instantiate vs (fst fs)
        R -> instantiate vs (snd fs)

    exprsFor sym = M.findWithDefault (LBool True, LBool True) sym m

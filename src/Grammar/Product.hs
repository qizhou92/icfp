module Grammar.Product where

import           Control.Lens

import qualified Data.Map as M
import qualified Data.Set as S

import           Grammar.Grammar
import           Formula hiding (Rule)

product :: Grammar -> Grammar -> Grammar
product g1' g2' = Grammar start (initial : rs1' ++ rs2')
  where
    initial = Rule L (Nonterminal 0 [Var "TMP" Int]) (LBool True) []

    ss1 = (-1) : S.toList (symbols g1)
    ss2 = (-1) : S.toList (symbols g2)

    g1 = g1' & vars . varName %~ ("l/" ++)
    g2 = g2' & vars . varName %~ ("r/" ++)

    tab = symbolTable ss1 ss2
    start = tab (g1 ^. grammarStart) (g2 ^. grammarStart)

    rs1 = map removeEmpty (g1 ^. grammarRules)
    rs2 = map removeEmpty (g2 ^. grammarRules)

    rs1' = [ r1 & nonterminals %~ rightJoin s2 (symbolVars g2 s2)
                & ruleCategory .~ L
           | r1 <- rs1, s2 <- ss2]
    rs2' = [ r2 & nonterminals %~  leftJoin s1 (symbolVars g1 s1)
                & ruleCategory .~ R
           | r2 <- rs2, s1 <- ss1]

    rightJoin s vs p = p & nonterminalVars %~ (++ vs) & allSymbols %~ (`tab` s)
    leftJoin  s vs p = p & nonterminalVars %~ (vs ++) & allSymbols %~ (s `tab`)

removeEmpty :: Rule -> Rule
removeEmpty r =
  if null (r ^. ruleRHS)
  then r & ruleRHS .~ [Nonterminal (-1) []]
  else r

symbolTable :: [Symbol] -> [Symbol] -> Symbol -> Symbol -> Symbol
symbolTable ss1 ss2 s s' =
  let pairs = [(s1, s2) | s1 <- ss1, s2 <- ss2]
      m = M.fromList $ zip pairs [0..]
  in M.findWithDefault 0 (s, s') m

symbolVars :: Grammar -> Symbol -> [Var]
symbolVars g s = case rulesFor s (g ^. grammarRules) of
  (r:_) -> view (ruleLHS . nonterminalVars) r
  [] -> []

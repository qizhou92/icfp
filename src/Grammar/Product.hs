module Grammar.Product where

import           Control.Lens
import           Data.Data.Lens
import           Data.List (nub)

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import           Grammar.Grammar
import           Formula hiding (Rule)

product :: Grammar -> Grammar -> Grammar
product g1 g2 = snd (fullProduct g1 g2)

fullProduct :: Grammar -> Grammar -> (Map (Symbol, Symbol) Symbol, Grammar)
fullProduct g1' g2' = (symTab, Grammar start (initial : rs1' ++ rs2'))
  where
    initial = Rule L (Nonterminal (ConcreteID 0) [Var "TMP" Int]) (LBool True) []

    cs1 = nub $ (-1) : (g1 ^.. biplate . _ConcreteID)
    cs2 = nub $ (-1) : (g1 ^.. biplate . _ConcreteID)
    ss1 = (-1) : S.toList (allSymbols g1)
    ss2 = (-1) : S.toList (allSymbols g2)

    g1 = g1' & vars . varName %~ ("l/" ++)
             & biplate . _PhantomID . _3 . traverse %~ ("l/" ++)
    g2 = g2' & vars . varName %~ ("r/" ++)
             & biplate . _PhantomID . _3 . traverse %~ ("r/" ++)

    symTab = symbolTable ss1 ss2
    tab s s' = M.findWithDefault 0 (s, s') symTab
    start = tab (g1 ^. grammarStart) (g2 ^. grammarStart)

    rs1 = map removeEmpty (g1 ^. grammarRules)
    rs2 = map removeEmpty (g2 ^. grammarRules)

    rs1' = [ r1 & nonterminals %~ rightJoin s2 (symbolVars g2 s2)
                & ruleCategory .~ L
           | r1 <- rs1, s2 <- cs2]
    rs2' = [ r2 & nonterminals %~  leftJoin s1 (symbolVars g1 s1)
                & ruleCategory .~ R
           | r2 <- rs2, s1 <- cs1]

    rightJoin s vs p = p & nonterminalVars %~ (++ vs) & biplate %~ (`tab` s)
    leftJoin  s vs p = p & nonterminalVars %~ (vs ++) & biplate %~ (s `tab`)

removeEmpty :: Rule -> Rule
removeEmpty r =
  if null (r ^. ruleRHS)
  then r & ruleRHS .~ [Nonterminal (ConcreteID $ -1) []]
  else r

symbolTable :: [Symbol] -> [Symbol] -> Map (Symbol, Symbol) Symbol
symbolTable ss1 ss2 =
  let pairs = [(s1, s2) | s1 <- ss1, s2 <- ss2]
  in M.fromList $ zip pairs [0..]

symbolVars :: Grammar -> Symbol -> [Var]
symbolVars g s = case rulesFor s (g ^. grammarRules) of
  (r:_) -> view (ruleLHS . nonterminalVars) r
  [] -> []

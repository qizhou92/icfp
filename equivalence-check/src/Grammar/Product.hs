module Grammar.Product where

import           Control.Lens

import qualified Data.Map as M
import qualified Data.Set as S

import           Grammar.Grammar
import           Formula hiding (Production)

product :: Grammar Int -> Grammar Int -> Grammar Int
product g1' g2' = Grammar start (initial : rs1' ++ rs2')
  where
    initial = Production L (Nonterminal 0 []) (LBool True) []

    ss1 = (-1) : S.toList (symbols g1)
    ss2 = (-1) : S.toList (symbols g2)

    g1 = g1' & vars . varName %~ ("l/" ++)
    g2 = g2' & vars . varName %~ ("r/" ++)

    tab = symbolTable ss1 ss2
    start = tab (g1 ^. grammarStart) (g2 ^. grammarStart)

    rs1 = map removeEmpty (g1 ^. grammarProductions)
    rs2 = map removeEmpty (g2 ^. grammarProductions)

    rs1' = [ r1 & nonterminals %~ rightJoin s2 (symbolVars g2 s2)
                & productionCategory .~ L
           | r1 <- rs1, s2 <- ss2] :: [Production Int]
    rs2' = [ r2 & nonterminals %~ leftJoin s1 (symbolVars g1 s1)
                & productionCategory .~ R
           | r2 <- rs2, s1 <- ss1]

    rightJoin, leftJoin :: Int -> [Var] -> Nonterminal Int -> Nonterminal Int
    rightJoin s vs p = p & nonterminalVars %~ (++ vs) & allSymbols %~ (`tab` s)
    leftJoin  s vs p = p & nonterminalVars %~ (vs ++) & allSymbols %~ (s `tab`)

removeEmpty :: Production Int -> Production Int
removeEmpty r =
  if null (r ^. productionRHS)
  then r & productionRHS .~ [Nonterminal (-1) []]
  else r

symbolTable :: [Int] -> [Int] -> Int -> Int -> Int
symbolTable ss1 ss2 s s' =
  let pairs = [(s1, s2) | s1 <- ss1, s2 <- ss2]
      m = M.fromList $ zip pairs [0..]
  in M.findWithDefault 0 (s, s') m

symbolVars :: Grammar Int -> Int -> [Var]
symbolVars g s = case productionsFor s (g ^. grammarProductions) of
  (r:_) -> view (productionLHS . nonterminalVars) r
  [] -> []

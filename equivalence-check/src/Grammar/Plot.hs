{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Grammar.Plot where

import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Monoid ((<>))
import           Data.List (intercalate)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc hiding ((<>), dot)

import qualified Turtle
import           System.Info

import           Formula hiding (Production, symbol, annot)
import           Grammar.Grammar

plot :: (Ord sym, Data sym, Pretty sym, MonadIO m) => FilePath -> Grammar sym -> m ()
plot fn g = do
  let txt = dot g
      cmdopen = case System.Info.os of
        "mingw32" -> "start"
        "linux"   -> "xdg-open"
        _         -> "open"
  liftIO $ writeFile (fn ++ ".dot") txt
  let fn' = Turtle.fromString (fn ++ ".dot")
  _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
  _ <- Turtle.shell (cmdopen <> " " <> fn' <> ".pdf") Turtle.empty
  return ()

dot :: forall sym. (Ord sym, Data sym, Pretty sym) => Grammar sym -> String
dot g =
  let vs = map symbol (S.toList (symbols g))
      es = concatMap production (g ^. grammarProductions)
      globalAtts = [ "node[fontsize=6];"
                   , "edge[fontsize=6, arrowsize=0.6];"]
  in "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    symbol i =
      let vs = view (productionLHS . nonterminalVars) $ head $ productionsFor i (g ^. grammarProductions)
          vs' = unwords (map unaliasedVarName vs)
      in show (pretty i) ++ " [label=\"" ++ show (pretty i) ++ "\n" ++ vs' ++ "\"];"
    production (Production ct lhs f rhs) =
      let annot = " [label=\"" ++ show (pretty ct) ++ ": " ++ show (pretty f) ++ "\"];"
          inc = rhs ^.. allSymbols :: [sym]
          tar = lhs ^. nonterminalSymbol
      in case inc of
        [i] -> [show (pretty i) ++ " -> " ++ show (pretty tar) ++ annot]
        _ ->
          let mid = "m" ++ intercalate "_" (map (show . pretty) (inc ++ [tar])) in
          [ mid ++ " [shape=point, width=0.00001, height=0.00001];" ]
          ++ map (\i -> show (pretty i) ++ " -> " ++ mid ++ " [dir=none];") inc
          ++ [ mid ++ " -> " ++ show (pretty tar) ++ annot ]

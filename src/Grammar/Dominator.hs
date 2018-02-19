module Grammar.Dominator where

import           Control.Lens

import           Grammar.Grammar

backRules :: Grammar -> [Rule]
backRules = filter (view ruleBackwards) . view grammarRules

nonrecursive :: Grammar -> Grammar
nonrecursive g@(Grammar start rs) = Grammar start (filter (`notElem` backRules g) rs)

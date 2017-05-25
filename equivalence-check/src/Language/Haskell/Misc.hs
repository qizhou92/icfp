module Language.Haskell.Misc where

-- import Outputable hiding (showPpr)
import Debug.Trace (trace)

import Text.PrettyPrint.HughesPJ

class PPrint a where
  ppr :: a -> Doc

instance (PPrint a, PPrint b) => PPrint (a, b) where
  ppr (x, y) = parens (ppr x <> comma <+> ppr y)

showPpr :: PPrint a => a -> String
showPpr = render . ppr

traceShow :: (Show a) => String -> a -> a
traceShow str x = trace (str ++ show x) x

module Language.Haskell.Misc where 

import Outputable hiding (showPpr)

import Debug.Trace (trace)


showPpr :: Outputable a => a -> String
showPpr = showSDocUnsafe . ppr

traceShow :: (Show a) => String -> a -> a 
traceShow str x = trace (str ++ show x) x 
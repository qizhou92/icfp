module Language.Haskell.Verify (

   verify 

) where


import Language.Haskell.Types

verify :: Program -> Program -> IO Result 
verify (x1,_) (x2,_) = return $ Result (x1, x2) False

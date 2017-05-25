module Main where

import Language.Haskell.Types
import Language.Haskell.Verify

import System.Environment
import System.Exit

main :: IO ExitCode
main = equivalenceCheck =<< makeConfig =<< getArgs

equivalenceCheck :: Config -> IO ExitCode
equivalenceCheck cfg = do
    eqEnv <- makeEqEnv cfg 
    res   <- mapM (uncurry verify) (goalsToPrograms (eqProgram eqEnv) <$> eqGoals eqEnv)
    putStrLn (unlines (show <$> res))
    exitWith ExitSuccess

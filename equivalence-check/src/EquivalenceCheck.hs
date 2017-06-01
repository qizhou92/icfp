module Main where

import Language.Equivalence.Types
import Language.Equivalence.Verify
import Language.Equivalence.Parser

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

makeEqEnv :: Config -> IO EqEnv
makeEqEnv cfg = do
  prog <-  parseProg <$> readFile (cfgFile cfg)
  return $ EqEnv prog (cfgQueries cfg)

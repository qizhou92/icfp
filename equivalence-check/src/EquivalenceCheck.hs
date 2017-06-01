module Main where

import Language.Equivalence.Types
import Language.Equivalence.Verify
import Language.Equivalence.Parser
import System.Environment
import System.Exit
import Data.Maybe (mapMaybe)
import Data.List  (isPrefixOf)

main :: IO ExitCode
main = equivalenceCheck =<< makeConfig =<< getArgs

equivalenceCheck :: Config -> IO ExitCode
equivalenceCheck cfg = do
  eqEnv <- makeEqEnv cfg
  putStrLn ("************** GOALS ************** \n" ++ show eqEnv)
  res   <- mapM (uncurry verify) (goalsToPrograms (eqProgram eqEnv) <$> eqGoals eqEnv)
  putStrLn (unlines (show <$> res))
  exitWith ExitSuccess

makeEqEnv :: Config -> IO EqEnv
makeEqEnv cfg = do
  str  <- readFile (cfgFile cfg)
  return $ EqEnv (parseProg str) (queries str ++ cfgQueries cfg)

queries :: String -> [(Var, Var)]
queries = mapMaybe stringQuery . lines

stringQuery :: String -> Maybe (Var, Var)
stringQuery l
  | isPrefixOf "--" l   = case words (drop 2 l) of
                            ["@checkEq", v1, v2] -> Just (Var v1, Var v2)
                            _                    -> Nothing
  | otherwise           = Nothing

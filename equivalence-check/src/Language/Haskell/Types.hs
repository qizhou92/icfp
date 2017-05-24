module Language.Haskell.Types where

import Var 
import CoreSyn

import System.Exit

import Language.Haskell.Misc
import Language.Haskell.GHC.Misc


type ProgramBind = (Var, CoreExpr) 
type Program     = CoreExpr

goalsToPrograms :: CoreProgram -> (Var, Var) -> (ProgramBind, ProgramBind)
goalsToPrograms cbs (x1, x2) = ((x1, findBind cbs x1), (x2, findBind cbs x2))


data Result = Result {resGoal :: (Var, Var), resResult :: Bool}

instance Show Result where
  show (Result (x1, x2) b) 
    = "\nPrograms " ++ showPpr x1 ++ " and " ++ showPpr x2 ++ showVerb b ++ "equivalent."
    where
      showVerb b = if b then " are " else " are not "

data EqEnv 
  = EqEnv { eqProgram :: CoreProgram
          , eqGoals   :: [(Var, Var)]
          }

instance Show EqEnv where
   show (EqEnv _ x) = "EqEnv {" ++ "eqGoals = " ++ unlines (showPpr <$> x) ++ " }"



data Config = Config {target :: String}

instance Show Config where
   show (Config {target = tg}) = "Config {" ++ "target =" ++ tg ++ " }" 

makeConfig :: [String] -> IO Config
makeConfig (i:_) = return $ Config i 
makeConfig _     = do 
   putStrLn "No input file specified"
   exitWith $ ExitFailure 0    
import Data.List (splitOn)
import System.Environment (getArgs)

import Debug.Trace

data Equation = Equation Int [Int]
  deriving (Show, Eq)

parseEquation :: String -> Equation
parseEquation raw = Equation lhs rhs
  where [rawLhs, rawRhs] = splitOn ": " raw
        lhs = read rawLhs
        rhs = read <$> splitOn " " rawRhs

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile path
      let input = (parseEquation <$>) . lines $!! raw
      mapM_ print input
    _ -> putStrLn "Usage: day07 <path to input>"

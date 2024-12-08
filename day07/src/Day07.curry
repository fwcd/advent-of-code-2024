{-# OPTIONS_FRONTEND -Wno-overlapping -Wno-incomplete-patterns #-}

import Control.Search.SetFunctions (set1, notEmpty)
import Data.List (splitOn, sum)
import System.Environment (getArgs)

data Equation = Equation { lhs :: Int, rhs :: [Int] }
  deriving (Show, Eq)

parseEquation :: String -> Equation
parseEquation raw = Equation lhs rhs
  where [rawLhs, rawRhs] = splitOn ": " raw
        lhs = read rawLhs
        rhs = read <$> splitOn " " rawRhs

isSolvable :: Equation -> Bool
isSolvable = notEmpty . set1 isSolvable'
  where eval [v]    = v
        eval (v:vs) = v + eval vs ? v * eval vs
        isSolvable' (Equation l r) | l =:= eval (reverse r) = True

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile path
      let equations = (parseEquation <$>) . lines $!! raw
          part1 = sum $ lhs <$> filter isSolvable equations
      putStrLn $ "Part 1: " ++ show part1
    _ -> putStrLn "Usage: day07 <path to input>"

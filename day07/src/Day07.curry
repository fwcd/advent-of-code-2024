{-# OPTIONS_FRONTEND -Wno-incomplete-patterns #-}

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

isSolvable :: [Int -> Int -> Int] -> Equation -> Bool
isSolvable ops = notEmpty . set1 isSolvable'
  where
    isSolvable' (Equation l (r:rs)) | l =:= evalAcc r rs = True
      where
        evalAcc acc vals = case vals of
            -- Prune branches that already overshoot the target
            _ | acc > l -> failed
            []          -> acc
            (v:vs)      -> anyOf $ (\op -> evalAcc (op acc v) vs) <$> ops

totalResult :: [Int -> Int -> Int] -> [Equation] -> Int
totalResult ops eqns = sum $ lhs <$> filter (isSolvable ops) eqns

(||.) :: Int -> Int -> Int
x ||. y = x * (10 ^ floor (1 + if y == 0 then 0 else logBase 10 (toFloat y))) + y

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile path
      let eqns = (parseEquation <$>) . lines $!! raw
          part1 = totalResult [(+), (*)] eqns
          part2 = totalResult [(+), (*), (||.)] eqns
      putStrLn $ "Part 1: " ++ show part1
      putStrLn $ "Part 2: " ++ show part2
    _ -> putStrLn "Usage: day07 <path to input>"

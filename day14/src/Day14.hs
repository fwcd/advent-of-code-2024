{-# LANGUAGE DeriveFunctor, NoFieldSelectors, OverloadedRecordDot #-}

import System.Environment (getArgs)
import System.IO (readFile')
import Data.List (sort)
import qualified Data.Set as S
import Control.Monad (join)

-- | Splits on the given value.
split :: Eq a => a -> [a] -> [[a]]
split x (y:ys) | x == y    = [] : split x ys
               | otherwise = let (y':ys') = split x ys
                             in (y : y') : ys'
split _ []                 = [[]]

-- | Finds the period of the given function.
period :: Ord a => (a -> a) -> a -> [a]
period f = period' S.empty
  where period' acc x | x `S.member` acc = []
                      | otherwise        = x : period' (S.insert x acc) (f x)

-- | The cartesian product with itself.
cartesianSquare :: [a] -> [(a, a)]
cartesianSquare xs = [(x, x') | x <- xs, x' <- xs]

-- | Finds the nth element of the list (modulo the list's length) .
(!!%) :: [a] -> Int -> a
xs !!% n = xs !! (n `mod` length xs)

data Vec2 a = Vec2 { x :: a, y :: a }
  deriving (Show, Eq, Ord, Functor)

data Robot = Robot { pos :: Vec2 Int, vel :: Vec2 Int }
  deriving (Show, Eq, Ord)

zipVec2With :: (a -> b -> c) -> Vec2 a -> Vec2 b -> Vec2 c
zipVec2With f v w = Vec2 (f v.x w.x) (f v.y w.y)

(.+.) :: Num a => Vec2 a -> Vec2 a -> Vec2 a
(.+.) = zipVec2With (+)

(.-.) :: Num a => Vec2 a -> Vec2 a -> Vec2 a
(.-.) = zipVec2With (-)

(.%.) :: Integral a => Vec2 a -> Vec2 a -> Vec2 a
(.%.) = zipVec2With mod

(./) :: Integral a => Vec2 a -> a -> Vec2 a
v ./ x = (`div` x) <$> v

parseVec2 :: Read a => String -> Vec2 a
parseVec2 raw = Vec2 x y
  where [x, y] = read <$> split ',' raw

parseRobot :: String -> Robot
parseRobot raw = Robot pos vel
  where [pos, vel] = parseVec2 . drop 2 <$> split ' ' raw

boardSize :: Vec2 Int
boardSize = Vec2 101 103

step :: Robot -> Robot
step r = Robot ((r.pos .+. r.vel) .%. boardSize) r.vel

stepN :: Int -> Robot -> Robot
stepN n = (!!% n) . period step

safetyFactor :: [Robot] -> Int
safetyFactor rs = foldr1 (*) [length $ filter (\p -> p.x `xop` center.x && p.y `yop` center.y) ps | (xop, yop) <- cartesianSquare [(<), (>)]]
  where center = boardSize ./ 2
        inQuadrant v = v.x /= center.x || v.y /= center.y
        ps = filter inQuadrant $ (.pos) <$> rs

pretty :: [Robot] -> String
pretty rs = unlines $ (\y -> join $ (\x -> showCount . length . filter (== Vec2 x y) $ (.pos) <$> rs) <$> [0..boardSize.x]) <$> [0..boardSize.y]
  where showCount n | n == 0    = "."
                    | otherwise = show n

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile' path
      let robots = parseRobot <$> lines raw
          robots1 = stepN 100 <$> robots
      putStrLn $ "Part 1: " ++ show (safetyFactor robots1)
    _ -> putStrLn "Usage: day14 <path to input>"

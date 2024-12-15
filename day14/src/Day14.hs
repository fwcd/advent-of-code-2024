{-# LANGUAGE DeriveFunctor, NoFieldSelectors, OverloadedRecordDot #-}

import System.Environment (getArgs)
import System.IO (readFile')
import Data.List (findIndex)
import qualified Data.Set as S
import Control.Monad (join)
import Data.Maybe (fromJust)

-- | Splits on the given value.
split :: Eq a => a -> [a] -> [[a]]
split x (y:ys) | x == y    = [] : split x ys
               | otherwise = let (y':ys') = split x ys
                             in (y : y') : ys'
split _ []                 = [[]]

-- | The cartesian product with itself.
cartesianSquare :: [a] -> [(a, a)]
cartesianSquare xs = [(x, x') | x <- xs, x' <- xs]

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
stepN n = (!! n) . iterate step

stepsUntil :: ([Robot] -> Bool) -> [Robot] -> Int
stepsUntil p = fromJust . findIndex p . iterate (step <$>)

-- Simple heuristic to check if all positions are unique.
-- Not sure why this even works since the tree isn't the full input.
isChristmasTree :: [Robot] -> Bool
isChristmasTree rs = S.size (S.fromList ps) == length rs
  where ps = (.pos) <$> rs

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
          part1 = safetyFactor robots1
          part2 = stepsUntil isChristmasTree robots
          robots1 = stepN 100 <$> robots
          robots2 = stepN part2 <$> robots
      putStrLn $ "Part 1: " ++ show part1
      putStrLn $ "Part 2: " ++ show part2
      putStrLn $ pretty robots2
    _ -> putStrLn "Usage: day14 <path to input>"

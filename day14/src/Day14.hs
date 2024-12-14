{-# LANGUAGE OverloadedRecordDot #-}

import System.Environment (getArgs)
import System.IO (readFile')

-- | Splits on the given value.
split :: Eq a => a -> [a] -> [[a]]
split x (y:ys) | x == y    = [] : split x ys
               | otherwise = let (y':ys') = split x ys
                             in (y : y') : ys'
split _ []                 = [[]]

data Vec2 = Vec2 { x :: Int, y :: Int }
  deriving (Show, Eq, Ord)

data Robot = Robot { pos :: Vec2, vel :: Vec2 }
  deriving (Show, Eq, Ord)

parseVec2 :: String -> Vec2
parseVec2 raw = Vec2 x y
  where [x, y] = read <$> split ',' raw

parseRobot :: String -> Robot
parseRobot raw = Robot pos vel
  where [pos, vel] = parseVec2 . drop 2 <$> split ' ' raw

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile' path
      let robots = parseRobot <$> lines raw
      mapM_ print robots
    _ -> putStrLn "Usage: day14 <path to input>"

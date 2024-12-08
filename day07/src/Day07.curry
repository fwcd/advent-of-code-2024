import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      raw <- readFile path
      let input = lines $!! raw
      print input
    _ -> putStrLn "Usage: day07 <path to input>"

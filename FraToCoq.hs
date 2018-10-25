module Tests where

import MS
import Bank
import Data.Foldable

handleProblem :: Int -> Effect -> IO ()
handleProblem n e = do
  let ps = allInterpretations e
  forM_ ps $ \p -> do
    putStrLn ("Definition Problem" ++ show n ++ ":= " ++ show p ++ ".")
    -- putStrLn $ "Abort All."
    putStrLn $ ""


main :: IO ()
main = do
  putStrLn "Load MS."
  suite handleProblem


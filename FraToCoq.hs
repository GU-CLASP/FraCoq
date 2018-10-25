module Tests where

import MS
import Bank
import Data.Foldable

handleProblem :: Int -> Effect -> IO ()
handleProblem n e = do
  let ps = allInterpretations e
  forM_ ps $ \p ->
    putStrLn $ "Theorem FraCaS" ++ show n ++ ": " ++ show p ++ ".\n"


main :: IO ()
main = do
  suite handleProblem


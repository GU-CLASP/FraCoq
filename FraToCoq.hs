module Tests where

import MS
import Bank
import Data.Foldable


handleProblem :: Int -> Effect -> IO ()
handleProblem n e = do
  let ps = allInterpretations e
  forM_ pnTable $ \(x,(gs,n)) -> do
    forM_ gs $ \g -> do
    -- putStrLn ("Variable " ++ show x ++ "_" ++ show g ": " ++ map toLower (show gender) ++ show p ++ ".")
    putStrLn $ ""
  forM_ ps $ \p -> do
    putStrLn ("Definition Problem" ++ show n ++ ":= " ++ show p ++ ".")
    -- putStrLn $ "Abort All."
    putStrLn $ ""


main :: IO ()
main = do
  putStrLn "Load MS."
  suite handleProblem


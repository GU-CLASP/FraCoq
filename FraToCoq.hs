import Data.Char
import MS
import Bank
import Data.Foldable
import LogicB


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
  forM_ pnTable $ \(x,(gs,_number)) -> do
    forM_ gs $ \g -> do
    putStrLn ("Variable " ++ x ++ "_" ++ show g ++ ": " ++ map toLower (show g) ++ "_A (PN2object "++ x ++ ").")
    putStrLn $ ""

  suite handleProblem


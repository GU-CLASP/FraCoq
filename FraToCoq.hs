import Data.Char
import MS
import Bank
import Data.Foldable
import LogicB


handleProblem :: Int -> Effect -> IO ()
handleProblem n e = do
  let ps = allInterpretations e
  forM_ (zip ['a'..'z'] ps) $ \(v,p) -> do
    case extendAllScopes ((fromHOAS' p) :: Exp Zero) of
      ([],q) -> putStrLn ("Definition Problem" ++ show n ++ [v] ++ ":= " ++ show q ++ ".")
      _ -> putStrLn ("(* Problem" ++ show n ++ [v] ++ " can't be scope-extended fully *)")
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


import Data.Char
import MS
import Bank
import Data.Foldable
import LogicB
import Data.List

prepare :: Exp Zero -> Either String (Exp Zero)
prepare q = case extendAllScopes q of
      ([],p) -> Right p
      _ -> Left $ "(* Interpretation " ++ show q ++ " can't be scope-extended fully *)"

handleProblem :: Int -> Effect -> IO ()
handleProblem n e = do
  let ps = nub $ map fromHOAS' $ allInterpretations e :: [Exp Zero]
      qs = nub $ map prepare ps
  forM_ (zip ['a'..'z'] qs) $ \(v,p) -> do
    case p of
      Right q -> putStrLn ("Definition Problem" ++ show n ++ [v] ++ ":= " ++ show q ++ ".")
      Left err -> putStrLn err
    putStrLn $ ""


main :: IO ()
main = do
  putStrLn "Load MS."
  forM_ pnTable $ \(x,(gs,_number)) -> do
    forM_ gs $ \g -> do
    putStrLn ("Variable " ++ x ++ "_" ++ show g ++ ": " ++ map toLower (show g) ++ "_A (PN2object "++ x ++ ").")
    putStrLn $ ""

  suite handleProblem


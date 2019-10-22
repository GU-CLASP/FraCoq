import Data.Char
import Dynamic
import MS
import Bank
import Data.Foldable
import LogicB
import Data.List
import Text.Printf

prepare :: Exp Zero -> Either String (Exp Zero)
prepare q = case extendAllScopes q of
      ([],p) -> Right p
      _ -> Left $ "(* Interpretation " ++ show q ++ " can't be scope-extended fully *)"

handleProblem :: Int -> (Phr,Phr,[Bool]) -> IO ()
handleProblem n (premise,h,rs) = do
  putStrLn $ "(* Problem " ++ show n ++ " *)"
  forM_ rs $ \r -> do
    let e = case r of
              True -> phrToEff premise ==> phrToEff h
              False -> phrToEff premise ==> (pNeg <$> phrToEff h)
    let ps = nub $ map fromHOAS' $ evalDynamic e :: [Exp Zero]
        qs = nub $ map prepare ps
    forM_ (zip ['a'..'z'] qs) $ \(v,p) -> do
      putStrLn $ "(* Reading  "++ show v ++" *)"
      case p of
        Right q -> putStrLn ("Definition Problem" ++ printf "%03d" n ++ [v] ++ show r ++ ":= " ++ show q ++ ".")
        Left err -> putStrLn err
      putStrLn $ ""


main :: IO ()
main = do
  putStrLn "Load MS."
  forM_ pnTable $ \(x,(gs,_number)) -> do
    forM_ gs $ \g -> do
    putStrLn ("Parameter " ++ x ++ "_" ++ show g ++ ": (" ++ map toLower (show g) ++ "_A (PN2object "++ x ++ ")).")
    putStrLn $ ""

  suite handleProblem


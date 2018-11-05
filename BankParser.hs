{-# LANGUAGE ViewPatterns #-}

module BankParser where

-- import Text.ParserCombinators.Parsek
import Text.ParserCombinators.Parsek.Position
-- import Text.ParserCombinators.Class
import Data.Char
import Data.List
import Data.Function
import Data.List.Split

data SExpr = Atom String | SExpr [SExpr] | Variants deriving Show

keyword :: String -> Parser ()
keyword x = spaces >> string x >> return ()

identifier :: Parser String
identifier = spaces >> munch1 (\x -> isAlphaNum x || x `elem` "_")

parens :: Parser x -> Parser x
parens a = do
  keyword "("
  x <- a
  keyword ")"
  return x

expr :: Parser SExpr
expr = (Atom <$> identifier) <|> (SExpr <$> parens exprs) <|> (keyword "variants{}" >> pure Variants)

exprs :: Parser [SExpr]
exprs = sepBy1 expr space

def :: Parser (String, SExpr)
def = do
  keyword "lin"
  x <- identifier
  keyword "="
  val <- expr
  keyword ";"
  return (x,val)

bank :: Parser [(String, SExpr)]
bank = do
  _prelude <- munch (\x -> x /= '{')
  keyword "{"
  keyword "lincat FraCaSPhrase = SS;"
  defs <- many def
  keyword "}"
  return defs


processSuite :: [[(HypID,SExpr)]] -> [String]
processSuite pbs = "suite :: (Int -> (Phr,Phr,[Bool]) -> IO ()) -> IO ()" :
                   "suite handleProblem = do" :
                   concat
                     [["  handleProblem " ++ show pb ++ " " ++ pbName pb] | (((pb,_,_),_):_) <- pbs ]

parseBank :: IO (ParseResult SourcePos [(String, SExpr)])
parseBank = parseFromFile bank longestResult "FraCaS-treebank/src/FraCaSBankI.gf"

processProblem :: [(HypID,SExpr)] -> [String]
processProblem defs = concatMap processDef defs ++ problemDef (reverse (map fst defs))

pbName :: Int -> String
pbName pb = "p_" ++ show pb


problemDef :: [HypID] -> [String]
problemDef ((th@(pb,_,_):hs))
  = [pbName pb ++ " :: (Phr,Phr,[Bool])"
    ,pbName pb ++ " = (" ++ intercalate " ### " (map hypName hyps') ++ "," ++ hypName th ++ "," ++ show rs ++ ")"]
  where hyps' = [h | h@(_,_,[_]) <- reverse hs]
        rs = case lookup pb expectResults of
          Nothing -> [True]
          Just x -> x
problemDef [] = error "problem without hypothesis"

hypName :: HypID -> String
hypName (pb,h,t) = "s_" ++ show pb ++ "_" ++ show h ++ "_" ++ t

processDef :: (HypID, SExpr) -> [String]
processDef (h,e) = [x ++ " :: Phr"
                   ,x ++ "=" ++ e']
  where x = hypName h
        e' = case overrides h of
               Nothing -> processExp e
               Just v -> v
processExp :: SExpr -> String
processExp (SExpr xs) = "(" ++ intercalate " " (map processExp xs) ++ ")"
processExp (Atom []) = error "empty identifer"
processExp (Atom s@(x:xs)) = case reverse s of
                               ('A':'_':_) -> "lexemeA " ++ show s
                               ('N':'_':_) -> "lexemeN " ++ show s
                               ('N':'P':'_':_) -> "lexemePN " ++ show s
                               ('P':'R':'_':_) -> "lexemeRP " ++ show s
                               ('V':'_':_) -> "lexemeV " ++ show s
                               ('2':'V':'_':_) -> "lexemeV2 " ++ show s
                               ('S':'2':'V':'_':_) -> "lexemeV2S " ++ show s
                               ('S':'V':'_':_) -> "lexemeVS " ++ show s
                               ('V':'2':'V':'_':_) -> "lexemeV2V " ++ show s
                               ('3':'V':'_':_) -> "lexemeV3 " ++ show s
                               ('v':'d':'A':'_':_) -> "lexemeAdv " ++ show s
                               ('V':'d':'A':'_':_) -> "lexemeAdV " ++ show s
                               ('p':'e':'r':'P':'_':_) -> "lexemePrep " ++ show s
                               _ -> toLower x : xs
processExp Variants = "variants"

frst :: (t2, t1, t) -> t2
frst (x,_,_) = x

main :: IO ()
main = do
  Right inp <- parseBank
  let handled = [((pbNumber,hypNumber,hypTyp),e)
                | (x,e) <- inp,
                  let (pbNumber, hypNumber, hypTyp) = parseHName x,
                  pbNumber >= 114,
                  -- pbNumber <= 141, -- end of anaphora section
                  pbNumber <= 220, -- end of ellipsis section
                  hypTyp /= "q"]
      problems = filter (not . (`elem` disabledProblems) . frst . fst  . head) $
                 groupBy ((==) `on` (frst . fst)) handled
  putStrLn $ unlines $
    ("module Bank where" :
     "import MS" :
     concatMap processProblem problems ++
     processSuite problems)

parseHName :: [Char] -> HypID
parseHName x = case splitOn "_" x of
  ("s": pbNumber : hypNumber : rest) -> (read pbNumber, read hypNumber, intercalate "_" rest)
  _ -> error ("statement with unexpected format: " ++ x)

type HypID = (Int, Int, [Char])


expectResults :: [(Int, [Bool])]
expectResults = [(119,[False])
                ,(125,[True,False])
                ,(130,[True,False])
                ,(136,[True,False])
                ,(141,[True,False])
                ,(147,[False])
                ]

overrides :: HypID -> Maybe String
overrides (177,1,"p")= Just "s_177_1_p_NEW"
overrides (122,4,"h")= Just "s_122_4_h_ALT"
overrides _ = Nothing

disabledProblems :: [Int]
disabledProblems =
  [137,171,172,191,192,193,194,195
  ,276 -- degenerate problem
  ,305 -- degenerate problem
  ,216,217 -- syntax wrong: should be (john is (fatter politician than
           -- bill)) not ((john is fatter politician) than bill)
  ]

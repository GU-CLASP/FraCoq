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


processSuite :: [[((String,String,String),SExpr)]] -> [String]
processSuite pbs = "suite :: IO ()" :
                   "suite = do" :
                   concat
                     [["  putStrLn " ++ show pb,
                       "  evalDbg " ++ pbName pb] | (((pb,_,_),_):_) <- pbs ]

parseBank :: IO (ParseResult SourcePos [(String, SExpr)])
parseBank = parseFromFile bank longestResult "FraCaS-treebank/src/FraCaSBankI.gf"

processProblem :: [((String,String,String),SExpr)] -> [String]
processProblem defs = concatMap processDef defs ++ problemDef (reverse (map fst defs))

pbName :: String -> String
pbName pb = "p_" ++ pb

problemDef :: [(String,String,String)] -> [String]
problemDef (th@(pb,_,_):hs) = [pbName pb ++ " :: Effect"
                              ,pbName pb ++ " = (" ++ intercalate " ### " (map hypName (reverse hs)) ++ ") ==> " ++ hypName th]
problemDef [] = error "prooblem without hypothesis"

hypName :: (String,String,String) -> String
hypName (pb,h,t) = "s_" ++ pb ++ "_" ++ h ++ "_" ++ t

processDef :: ((String,String,String), SExpr) -> [String]
processDef (h,e) = [x ++ " :: Phr"
                   ,x ++ "=" ++ processExp e]
  where x = hypName h
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
                               ('j':'n':'o':'C':'P':'_':_) -> "lexemePConj " ++ show s
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
                  pbNumber >= "114",
                  pbNumber < "164",
                  hypTyp /= "q"]
      problems = groupBy ((==) `on` (frst . fst)) handled
  putStrLn $ unlines $
    ("module Bank where" :
     "import MS" :
     concatMap processProblem problems ++
     processSuite problems)

parseHName :: [Char] -> ([Char], [Char], [Char])
parseHName x = case splitOn "_" x of
  ("s": pbNumber : hypNumber : rest) -> (pbNumber, hypNumber, intercalate "_" rest)
  _ -> error ("statement with unexpected format: " ++ x)

-- >>> splitOn "_" "s_168_4_h"
-- ["s","168","4","h"]

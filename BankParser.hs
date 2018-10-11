module BankParser where

-- import Text.ParserCombinators.Parsek
import Text.ParserCombinators.Parsek.Position
-- import Text.ParserCombinators.Class
import Data.Char
import Data.List

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


parseBank :: IO (ParseResult SourcePos [(String, SExpr)])
parseBank = parseFromFile bank longestResult "FraCaS-treebank/src/FraCaSBankI.gf"



processDef :: ([Char], SExpr) -> [String]
processDef (x,e) = [x ++ " :: Phr"
                   ,x ++ "=" ++ processExp e]

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

main :: IO ()
main = do
  Right inp <- parseBank
  putStrLn $ unlines $
    ("module Bank where" :
     "import MS" :
     concatMap processDef [(x,e) | (x,e) <- inp, x >= "s_114_1_p", x < "s_133_1_p", not ("_q" `isSuffixOf` x)])

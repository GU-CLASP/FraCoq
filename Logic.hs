{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
module Logic where

import Data.Char (toLower)
import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Arrow (second)

type Var = String

data Next v = Here | There v deriving Eq

newtype Nat = Nat Integer deriving (Show,Eq,Num,Enum,Integral,Ord,Real)

data Amount = One | Few | Several | Exact Nat | AtLeast Nat -- amount for the *positive* polarity
  deriving (Eq,Show)

data Op = Fld String -- ^ field lookup
        | Custom String
        | App
        | Not
        | And
        | Or
        | Implies
        | ImpliesOften
        | LAST_OPERATOR
  deriving (Eq,Show)

data Pol = Pos | Neg | Both deriving (Eq,Ord,Show)

data Exp v where
  Op :: Op -> [Exp v] -> Exp v
  Con :: String -> Exp v
  Var :: v -> Exp v
  Lam :: Exp (Next v) -> Exp v
  Quant :: Amount -> Pol -> (Exp (Next v)) -> (Exp (Next v)) -> Exp v
  deriving Eq


{-

eqExp :: Int -> Exp -> Exp -> Bool
eqExp n (Op op1 exps1) (Op op2 exps2) = op1 == op2 && length exps1 == length exps2 && and (zipWith (eqExp n) (exps1) (exps2))
eqExp n (Quant a1 p1 v1 t1 b1) (Quant a2 p2 v2 t2 b2) = a1 == a2 && p1 == p2 && v1 == v2 && eqExp n t1 t2 && eqExp n b1 b2
eqExp n (Lam f1) (Lam f2) = eqExp (n+1) (f1 x) (f2 x)
  where x = Var $ "_V" ++ show n
eqExp _ (Var x) (Var x') = x == x'
eqExp _ (Con x) (Con x') = x == x'
eqExp _ _ _ = False

type Type = Exp


opPrc :: Op -> Int
opPrc = \case
  (Custom _) -> 1
  Fld _ -> 1
  App -> 2
  Not -> 3
  And -> 4
  Or -> 5
  ImpliesOften -> 6
  Implies -> 6
  LAST_OPERATOR -> 7


pattern TRUE :: Exp
pattern TRUE = Con "True"

pattern FALSE :: Exp
pattern FALSE = Con "False"

pattern APP :: Exp -> Exp -> Exp
pattern APP f x = BinOp App f x

pattern NOT :: Exp -> Exp
pattern NOT x = UnOp Not x

not' :: Exp -> Exp
not' = NOT

lam :: (Exp -> Exp) -> Exp
lam f = case f (Var eta) of
           APP b (Var "__ETA__") | not (eta `elem` freeVars b) -> b
           _ -> Lam f
  where eta = "__ETA__"


app :: Exp -> Exp -> Exp
app (Lam f) x = f x
app f x = APP f x

apps :: Exp -> [Exp] -> Exp
apps f args = foldl app f args

true :: Exp
true = TRUE

pattern Proj :: Exp -> String -> Exp
pattern Proj e f = Op (Fld f) [e]

pattern BinOp :: Op -> Exp -> Exp -> Exp
pattern BinOp op x y = Op op [(x),(y)]

pattern UnOp :: Op -> Exp -> Exp
pattern UnOp op x = Op op [(x)]

(-->),(~~>) :: Exp -> Exp -> Exp
x --> y = BinOp Implies x y
x ~~> y = BinOp ImpliesOften x y

pattern (:∧) :: Exp -> Exp -> Exp
pattern x :∧ y = BinOp And x y

(∧) :: Exp -> Exp -> Exp
TRUE ∧ y = y
y ∧ TRUE = y
(x :∧ y) ∧ z = x :∧ (y ∧ z)
x ∧ y = x :∧ y
(∨) :: Exp -> Exp -> Exp
x ∨ y = BinOp Or x y


substOp :: Subst -> Op -> Op
substOp _ op = op

subst :: Subst -> Exp -> Exp
subst f (Lam t) = Lam (\x -> subst f (t x))
subst f (Quant a p v t b) = Quant a p v (subst f t) (subst f b)
subst f (Var x) = f x
subst _ (Con x) = Con x
subst f (Op o xs) = Op (substOp f o) (map (subst f) xs)

dualize :: Pol -> Pol
dualize Pos = Neg
dualize Neg = Pos
dualize Both = Both

isAssoc :: Op -> Bool
isAssoc Implies = False
isAssoc ImpliesOften = False
isAssoc App = False
isAssoc _ = True

needsParens :: Op -> Op -> Bool
needsParens ctx op = opPrc ctx < opPrc op || (opPrc ctx == opPrc op && not (isAssoc op))

instance Show Exp where
  show = ppExp 1 Not


quoteTex :: String -> String
quoteTex = concatMap q
  where q x | x `elem` "_#\\%" = "\\" ++ [x]
            | otherwise = [x]

-- showTex :: Exp -> [Char]
-- showTex = texExp LAST_OPERATOR

ppOp :: Op -> [Char]
ppOp o = case o of
  Not -> "NOT"
  And -> "/\\"
  Or -> "\\/"
  Implies -> "->"
  ImpliesOften -> "~>"
  Custom n -> n
  App -> "@"
  _ -> error ("cannot print op:" ++ show o)


varName :: Int -> String
varName n = "x" ++ show n

ppExp :: Int -> Op -> Exp -> String
ppExp n ctx e0 =
  let prns op x = if needsParens ctx op then parens x else x
  in case e0 of
      (Lam f) -> parens ("fun " ++ varName n ++ " => " ++ ppExp (n+1) LAST_OPERATOR (f (Var (varName n))))
      (Con x) -> x
      (Var x) -> x
      (Proj e f) -> ppExp n (Fld "f") e ++ "." ++ f
      (Quant k p v dom body) -> parens (o ++ " " ++ ppFun dom ++ " " ++ ppFun body)
          where ppFun t = parens("fun " ++ v ++ "=>" ++ ppExp n LAST_OPERATOR t)
                o = case (k,p) of
                   (One,Neg) -> "FORALL"
                   (One,Pos) -> "EXISTS"
                   (Few,Pos) -> "FEW"
                   (Few,Neg) -> "MOST"
                   (Several,Pos) -> "SEVERAL"
                   (Exact n,Both) -> "EXACT (" ++ show (toInteger n) ++ ")"
                   (AtLeast n,Both) -> "ATLEAST (" ++ show (toInteger n) ++ ")"
                   _ -> show (k,p)
                c = case p of
                   Neg -> (-->)
                   _ -> (∧)
      (APP f arg) -> prns App $ ppExp n Not f ++ " " ++ ppExp n App arg
      (BinOp op x y) -> prns op $ ppExp n op x ++ " " ++ ppOp op ++ " " ++ ppExp n op y
      (Op op args) -> ppOp op ++ "(" ++ intercalate "," [ppExp n op a | (a) <- args] ++ ")"


parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

pattern The :: Exp -> Exp
pattern The body =  APP (Con "THE") body
pattern Forall :: Var -> Type -> Exp -> Exp
pattern Forall x dom body = Quant One Neg x dom body
pattern Exists :: Var -> Type -> Exp -> Exp
pattern Exists x dom body = Quant One Pos x dom body

-- pattern Sigma x dom body = Quant Pi Pos x dom body
pattern MOST :: Var -> Type -> Exp -> Exp
pattern MOST x dom body = Quant Few Neg x dom  body
pattern FEW :: Var -> Type -> Exp -> Exp
pattern FEW x dom body = Quant Few Pos x dom  body
pattern SEVERAL :: Var -> Type -> Exp -> Exp
pattern SEVERAL x dom body = Quant Several Pos x dom  body

normalize :: [Char] -> [Char]
normalize = map toLower

-- texRec :: Exp -> [(String,String)]
-- texRec (Quant _ Pos x dom body) = (x,showTex dom):texRec body
-- texRec body = [("p",showTex body)]

-- showRec :: Op -> Exp -> [Char]
-- showRec _ ex@(Quant _ Pos _ _ _) = "[" ++ intercalate ";\\;" ([x ++ " : " ++ t | (x,t) <- texRec ex]) ++ "]"
-- showRec op ex = texExp op ex

-- -- | Convert an expression to tex string. The 1st argument is the
-- -- operator of the context where the expression is to be printed.
-- texExp :: Op -> Exp -> [Char]
-- texExp _ (Var x) = "\\mathnormal{" ++ quoteTex (normalize x) ++ "}"
-- texExp _ (Con x) = "\\mathrm{" ++ quoteTex (normalize x) ++ "}"
-- texExp op (Proj e f) = texExp op e ++ "." ++ f
-- texExp _ (Op op@(Custom _) args) = texOp op ++ "(" ++ intercalate "," (map (texExp op) args) ++ ")"
-- texExp _ (Op THE args) = texOp THE ++ "(" ++ intercalate "," (map (texExp THE) args) ++ ")"
-- texExp ctx (Op op args) = prns $ case args of
--   [x,y] -> texExp op x ++ " " ++ texOp op ++ " " ++ texExp op y
--   [x] -> texOp op ++ " " ++ texExp op x
--   where prns x = if needsParens ctx op then "(" ++ x ++ ")" else x
-- texOp :: Op -> [Char]
-- texOp o = case o of
--   (Custom op) -> "\\mathrm{" ++ quoteTex (normalize op) ++ "}"
--   THE -> "\\mathbf{U}"
--   Not -> "¬"
--   And -> "∧"
--   Or -> "∨"
--   Implies -> "→"
--   ImpliesOften -> "↝"
--   -- Or -> "∨"
--   Qu k p v dom -> (++ ("(" ++ v ++ ":" ++ showRec LAST_OPERATOR dom {-(1)-} ++ ").\\;")) $ case (k,p) of
--     (All,Neg) -> "∀"
--     (All,Pos) -> "∃"
--     (Pi,Pos) -> "Σ"
--     (Pi,Neg) -> "Π"
--     (Most,Pos) -> "FEW "
--     (Most,Neg) -> "MOST "

freeVars :: Exp -> [Var]
freeVars (Con _x) = []
freeVars (Lam f) = freeVars (f (Con "__FREE__"))
freeVars (Var x) = [x]
freeVars (Quant _ _ x dom body) = (freeVars dom ++ nub (freeVars body)) \\ [x]
freeVars (Op _ xs) = (concatMap (freeVars) xs)

boundVars :: Exp -> [Var]
boundVars (Var _) = []
boundVars (Lam f) = boundVars (f (Con "__BOUND__")) 
boundVars (Con _) = []
boundVars (Quant _ _ x dom body) = x:boundVars dom++boundVars body
boundVars (Op _ xs) = concatMap (boundVars) xs

negativeContext :: (Num a, Eq a) => Op -> a -> Bool
negativeContext Implies 0 = True
negativeContext ImpliesOften 0 = True
negativeContext Not _ = True
negativeContext _ _ = False

-- FIMXE: rename
isQuant :: [Var] -> Exp -> Bool
isQuant x' (e) = case e of
  (Quant One _ x _ _) -> x `elem` x'
  _ -> False

type Arg = (Exp)
matchQuantArg :: Alternative m => Monad m => [Var] -> [Arg] -> m ([Arg],Arg,[Arg])
matchQuantArg _ [] = fail "not found"
matchQuantArg x' (a:as) = (guard (isQuant x' a) >> return ([],a,as)) <|> do
  (l,q,r) <- matchQuantArg x' as
  return (a:l,q,r)

negativePol :: Pol -> Bool
negativePol = \case
  Neg -> True
  _ -> False

liftQuantifiers :: (Alternative m, Monad m) => [Var] -> Exp -> m Exp
liftQuantifiers xs (Quant amount pol x dom inner@(Quant a' pol' x' dom' body))
  | isQuant xs inner = return (Quant a' (maybeDual pol') x' dom' (Quant amount pol x dom body))
    where maybeDual = if negativePol pol then dualize else id
liftQuantifiers xs (Op op args) = do
  (l,(Quant One pol x dom body),r) <- matchQuantArg xs args
  let pol' = if negativeContext op (length l) then dualize pol else pol
  return (Quant One pol' x dom (Op op (l++(body):r)))
liftQuantifiers _ e = return e

-- bottomUp :: (Monad m) => (Exp -> m Exp) -> (Exp -> m Exp)
-- bottomUp f (Var x) = f (Var x)
-- bottomUp f (Con x) = f (Con x)
-- bottomUp f (Op op args) = do
--   r <- Op op <$> mapM (bottomUp f) args
--   f r

-}

-- (Exp -> Exp) -> m (Exp -> Exp)
anywhere :: Alternative m => (Monad m) => (forall v. Exp v -> m (Exp v)) -> (Exp v -> m (Exp v))
anywhere f (Var x) = f (Var x)
anywhere f e@(Lam q) = f e <|> (Lam <$> f q )
anywhere f (Con x) = f (Con x)
anywhere f e@(Op op args) = f e <|> Op op <$> mapM (anywhere f) args

{-
-- liftQuantifiersAnyWhere :: (Monad m, Alternative m) => [Var] -> Exp -> m Exp
-- liftQuantifiersAnyWhere x = anywhere (liftQuantifiers x)


-- extendAllScopes :: Exp -> Exp
-- extendAllScopes e = case freeVars e `intersect` boundVars e of
--   [] -> e
--   xs -> case liftQuantifiersAnyWhere xs e of
--     Nothing -> error "freevars, but nothing to lift!"
--     -- Just e' -> if e == e' then e else extendAllScopes e'

type Subst = Var -> Exp

mkSubst :: [(Var,Exp)] -> Subst
mkSubst s x' = case lookup x' s of
  Nothing -> Var x'
  Just e -> e

after :: Subst -> Subst -> Subst
(s1 `after` s2) x = subst s1 (s2 x)

unsupported :: Exp
unsupported = Var "unsupported"

-}

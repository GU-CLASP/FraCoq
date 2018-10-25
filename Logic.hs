{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Logic where

import Data.Char (toLower)
import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Arrow (second)
import Data.Traversable

newtype AExp = AExp {fromAExp :: forall v. Exp v}

type Var = String

data Next v = Here | There v deriving (Eq, Functor)
data Zero

instance Applicative Next where
  pure = There
  Here <*> _ = Here
  _ <*> Here = Here
  There f <*> There a = There (f a)

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
  V :: v -> Exp v
  Var :: String -> Exp v 
  Lam :: Exp (Next v) -> Exp v
  Quant :: Amount -> Pol -> Var -> (Exp v) -> (Exp v) -> Exp v -- TODO: dom should not mention the variable
  deriving (Eq, Functor)


-- eqExp :: Int -> Exp v -> Exp v -> Bool
-- eqExp n (Op op1 exps1) (Op op2 exps2) = op1 == op2 && length exps1 == length exps2 && and (zipWith (eqExp n) (exps1) (exps2))
-- eqExp n (Quant a1 p1 v1 t1 b1) (Quant a2 p2 v2 t2 b2) = a1 == a2 && p1 == p2 && v1 == v2 && eqExp n t1 t2 && eqExp n b1 b2
-- eqExp n (Lam f1) (Lam f2) = eqExp (n+1) (f1) (f2)
-- eqExp _ (Var x) (Var x') = x == x'
-- eqExp _ (Con x) (Con x') = x == x'
-- eqExp _ _ _ = False

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


pattern TRUE :: Exp v
pattern TRUE = Con "True"

pattern FALSE :: Exp v
pattern FALSE = Con "False"

pattern APP :: Exp v -> Exp v -> Exp v
pattern APP f x = BinOp App f x

pattern NOT :: Exp v -> Exp v
pattern NOT x = UnOp Not x

not' :: Exp v -> Exp v
not' = NOT

lapp :: Exp (Next w) -> Exp w -> Exp w
lapp f a = f >>= \case
  Here -> a
  There v -> V v


lam' :: (Exp (Next w) -> Exp (Next w)) -> Exp w
lam' f = case f (V Here) of
           APP b (V Here) -> case sequenceA b of
             Here -> dflt
             There b' -> b'
           _ -> dflt
  where dflt = Lam (f (V Here))

lam :: (AExp -> AExp) -> AExp
lam f = AExp $ case f (AExp (V Here)) of
  AExp t -> _

instance Applicative Exp where
  (<*>) = ap
  pure = V
instance Monad Exp where
  (>>=) = flip subst

subst :: forall v w. (v -> Exp w) -> Exp v -> Exp w
subst f = \case
  (V x) -> f x
  (Op p args) -> Op p (map (subst f) args)
  (Con k) -> Con k
  (Var v) -> Var v
  (Quant a p v dom body) -> Quant a p v (dom >>= f) (body >>= f)
  (Lam t) -> Lam (subst f' t)
    where f' :: Next v -> Exp (Next w)
          f' Here = V Here
          f' (There x) = fmap There (f x)

instance Foldable Exp where
  foldMap = foldMapDefault

instance Traversable Exp where
  traverse f = \case
    (Op p args) -> Op p <$> traverse (traverse f) args
    (Con k) -> pure (Con k)
    (Var v) -> pure (Var v)
    (Quant a p v d b) -> Quant a p v <$> traverse f d <*> traverse f b
    V x -> V <$> f x
    Lam t -> Lam <$> (flip traverse t $ \case
                         Here -> pure Here
                         There x -> fmap There (f x))

app' :: Exp v -> Exp v -> Exp v
app' (Lam f) x = f >>= \case Here -> x;There v -> pure v 
app' f x = APP f x

app ::  AExp -> AExp -> AExp
app (AExp f) (AExp a) = AExp (app' f a)

apps :: AExp -> [AExp] -> AExp
apps f args = foldl app f args

con :: String -> AExp
con s = AExp (Con s)

true :: Exp v
true = TRUE

pattern Proj :: Exp v -> String -> Exp v
pattern Proj e f = Op (Fld f) [e]

pattern BinOp :: Op -> Exp v -> Exp v -> Exp v
pattern BinOp op x y = Op op [(x),(y)]

pattern UnOp :: Op -> Exp v -> Exp v
pattern UnOp op x = Op op [(x)]

(-->),(~~>) :: AExp -> AExp -> AExp
AExp x --> AExp y = AExp (BinOp Implies x y)
AExp x ~~> AExp y = AExp (BinOp ImpliesOften x y)

pattern (:∧) :: Exp v -> Exp v -> Exp v
pattern x :∧ y = BinOp And x y

(∧) :: Exp v -> Exp v -> Exp v
TRUE ∧ y = y
y ∧ TRUE = y
(x :∧ y) ∧ z = x :∧ (y ∧ z)
x ∧ y = x :∧ y

(∨) :: Exp v -> Exp v -> Exp v
x ∨ y = BinOp Or x y


-- substOp :: Subst -> Op -> Op
-- substOp _ op = op

-- subst :: Subst -> Exp -> Exp
-- subst f (Lam t) = Lam (\x -> subst f (t x))
-- subst f (Quant a p v t b) = Quant a p v (subst f t) (subst f b)
-- subst f (Var x) = f x
-- subst _ (Con x) = Con x
-- subst f (Op o xs) = Op (substOp f o) (map (subst f) xs)

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

instance Show v => Show (Exp v) where
  show = ppExp 1 Not . fmap show


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

ppExp :: Int -> Op -> Exp String -> String -- TODO: remove n
ppExp n ctx e0 =
  let prns op x = if needsParens ctx op then parens x else x
  in case e0 of
      V x -> x
      (Lam f) -> parens ("fun " ++ varName n ++ " => " ++ ppExp (n+1) LAST_OPERATOR (f `lapp` (Var (varName n))))
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
      (APP f arg) -> prns App $ ppExp n Not f ++ " " ++ ppExp n App arg
      (BinOp op x y) -> prns op $ ppExp n op x ++ " " ++ ppOp op ++ " " ++ ppExp n op y
      (Op op args) -> ppOp op ++ "(" ++ intercalate "," [ppExp n op a | (a) <- args] ++ ")"


parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

pattern The :: Exp v -> Exp v
pattern The body =  APP (Con "THE") body
pattern Forall :: forall t. Var -> Exp t -> Exp t -> Exp t
pattern Forall x dom body = Quant One Neg x dom body
pattern Exists :: forall t. Var -> Exp t -> Exp t -> Exp t
pattern Exists x dom body = Quant One Pos x dom body

-- pattern Sigma x dom body = Quant Pi Pos x dom body
pattern MOST :: forall t. Var -> Exp t -> Exp t -> Exp t
pattern MOST x dom body = Quant Few Neg x dom  body
pattern FEW :: forall t. Var -> Exp t -> Exp t -> Exp t
pattern FEW x dom body = Quant Few Pos x dom  body
pattern SEVERAL :: forall t. Var -> Exp t -> Exp t -> Exp t
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

freeVars :: forall t. Exp t -> [String]
freeVars (Con _x) = []
freeVars (V _) = []
freeVars (Lam f) = freeVars f
freeVars (Var x) = [x]
freeVars (Quant _ _ x dom body) = (freeVars dom ++ nub (freeVars body)) \\ [x]
freeVars (Op _ xs) = (concatMap (freeVars) xs)

boundVars :: forall t. Exp t -> [String]
boundVars (V _) = []
boundVars (Var _) = []
boundVars (Lam f) = boundVars f 
boundVars (Con _) = []
boundVars (Quant _ _ x dom body) = x:boundVars dom++boundVars body
boundVars (Op _ xs) = concatMap (boundVars) xs

negativeContext :: (Num a, Eq a) => Op -> a -> Bool
negativeContext Implies 0 = True
negativeContext ImpliesOften 0 = True
negativeContext Not _ = True
negativeContext _ _ = False

-- FIMXE: rename
isQuant :: [Var] -> Exp v -> Bool
isQuant x' (e) = case e of
  (Quant One _ x _ _) -> x `elem` x'
  _ -> False

matchQuantArg :: Alternative m => Monad m => [Var] -> [Exp v] -> m ([Exp v],Exp v,[Exp v])
matchQuantArg _ [] = fail "not found"
matchQuantArg x' (a:as) = (guard (isQuant x' a) >> return ([],a,as)) <|> do
  (l,q,r) <- matchQuantArg x' as
  return (a:l,q,r)

negativePol :: Pol -> Bool
negativePol = \case
  Neg -> True
  _ -> False

liftQuantifiers :: (Alternative m, Monad m) => [Var] -> Exp v -> m (Exp v)
liftQuantifiers xs (Quant amount pol x dom inner@(Quant a' pol' x' dom' body))
  | isQuant xs inner = return (Quant a' (maybeDual pol') x' dom' (Quant amount pol x dom body))
    where maybeDual = if negativePol pol then dualize else id
liftQuantifiers xs (Lam (Quant a p v d b))
  | v `elem` xs, There d' <- sequenceA d = return (Quant a p v d' (Lam b))
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


-- (Exp -> Exp) -> m (Exp -> Exp)
anywhere :: Alternative m => (Monad m) => (forall w. Exp w -> m (Exp w)) -> (Exp v -> m (Exp v))
anywhere f e = f e <|> case e of
  (Quant a p v d b) -> Quant a p v <$> anywhere f d <*> anywhere f b
  (Lam q) -> Lam <$> f q
  (Op op args) -> Op op <$> mapM (anywhere f) args
  _ -> empty

liftQuantifiersAnyWhere :: (Monad m, Alternative m) => [Var] -> (Exp v) -> m (Exp v)
liftQuantifiersAnyWhere x = anywhere (liftQuantifiers x)


extendAllScopes :: Eq v => Exp v -> Exp v
extendAllScopes e = case freeVars e `intersect` boundVars e of
  [] -> e
  xs -> case liftQuantifiersAnyWhere xs e of
    Nothing -> error "freevars, but nothing to lift!"
    Just e' -> if e == e' then e else extendAllScopes e'

{-
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

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
module Logic where

import Data.Char (toLower)
import Data.List

type Var = String

data Exp = Op Op [Exp]
         | Var Var
         | Con String
         | Lam (Exp -> Exp)
         | Quant Amount Pol Var Exp Exp




eqExp :: Int -> Exp -> Exp -> Bool
eqExp n (Op op1 exps1) (Op op2 exps2) = op1 == op2 && length exps1 == length exps2 && and (zipWith (eqExp n) (exps1) (exps2))
eqExp n (Quant a1 p1 v1 t1 b1) (Quant a2 p2 v2 t2 b2) = a1 == a2 && p1 == p2 && v1 == v2 && eqExp n t1 t2 && eqExp n b1 b2
eqExp n (Lam f1) (Lam f2) = eqExp (n+1) (f1 x) (f2 x)
  where x = Var $ "_V" ++ show n
eqExp _ (Var x) (Var x') = x == x'
eqExp _ (Con x) (Con x') = x == x'
eqExp _ _ _ = False

type Type = Exp

newtype Nat = Nat Integer deriving (Show,Eq,Num,Enum,Integral,Ord,Real)

data Amount = One | Few | Several | Many | Lots | Exact Nat | AtLeast Nat -- amount for the *positive* polarity
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

pattern BinOp :: Op -> Exp -> Exp -> Exp
pattern BinOp op x y = Op op [(x),(y)]

pattern UnOp :: Op -> Exp -> Exp
pattern UnOp op x = Op op [(x)]

(<->) :: Exp -> Exp -> Exp
a <-> b = (a --> b) ∧ (b --> a)

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

data Pol = Pos | Neg | Both deriving (Eq,Ord,Show)


quoteTex :: String -> String
quoteTex = concatMap q
  where q x | x `elem` "_#\\%" = "\\" ++ [x]
            | otherwise = [x]

-- showTex :: Exp -> [Char]
-- showTex = texExp LAST_OPERATOR


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


freeVars :: Exp -> [Var]
freeVars (Con _x) = []
freeVars (Lam f) = freeVars (f (Con "__FREE__"))
freeVars (Var x) = [x]
freeVars (Quant _ _ x dom body) = (freeVars dom ++ nub (freeVars body)) \\ [x]
freeVars (Op _ xs) = (concatMap (freeVars) xs)


parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
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


check :: Bool -> Maybe ()
check c = if c then Just () else Nothing

-- | solveThe metaVariable t1 t2. metaVariable occurs t1; not in t2.
-- Attempt to unify t1 and t2; return the necessary assignments of metaVariable if it exists.

-- ATTN: currently unused. But this could be a more principled
-- solution to solving for definites (or times). Rather than having a
-- special environment, solve for a variable that makes the thing that you lookup true.
solveThe :: Int -> Var -> [(Exp,Exp)] -> Maybe [Exp]
solveThe _ _ [] = Just []
solveThe n meta ((Op op1 e1,Op op2 e2):cs)
  = check (op1 == op2 && length e1 == length e2) >> solveThe n meta (zip e1 e2 ++ cs)
solveThe n meta ((Var x,t):cs) | x == meta = (t:) <$> solveThe n meta cs
solveThe n meta ((Var x,Var y):cs) | x == y = solveThe n meta cs
solveThe n meta ((Lam f,Lam g):cs) = solveThe (n+1) meta ((f v, g v):cs)
  where v = Var $ "_V_" ++ show n
solveThe n meta ((Quant a1 p1 v1 d1 b1,Quant a2 p2 v2 d2 b2):cs) =
  check (a1 == a2 && p1 == p2 && v1 == v2) >>
  solveThe n meta ((d1,d2):(b1,b2):cs)
solveThe _ _ _ = Nothing




eqExp' :: Exp -> Exp -> Bool
eqExp' = eqExp 0 []

eqNat' :: Nat -> Nat -> Bool
eqNat' = eqNat 0 []

instance Eq Nat where
  (==) = eqNat'

eqExp :: Int -> [(Var,Var)] -> Exp -> Exp -> Bool
eqExp n equs e1 e2 = case (e1,e2) of
  (Op op1 exps1,Op op2 exps2) -> op1 == op2 && length exps1 == length exps2 && and (zipWith (eqExp n equs) (exps1) (exps2))
  (Quant a1 p1 v1 t1 b1,Quant a2 p2 v2 t2 b2) -> eqAmount n equs a1 a2 && p1 == p2 && eqExp n eq' t1 t2 && eqExp n eq' b1 b2
    where eq' = (v1,v2):equs
  (Lam f1,Lam f2) -> eqExp (n+1) equs (f1 x) (f2 x)
     where x = Var $ "_V" ++ show n
  (Var x,Var x') -> x == x' || (x,x') `elem` equs
  (Con x,Con x') -> x == x'
  _ -> False

eqAmount :: Int -> [(Var, Var)] -> Amount -> Amount -> Bool
eqAmount n eqs (Exact x) (Exact x') = eqNat n eqs x x'
eqAmount n eqs(AtLeast x) (AtLeast x') = eqNat n eqs x x'
eqAmount _ _ One One = True
eqAmount _ _ Few Few = True
eqAmount _ _ Several Several = True
eqAmount _ _ Many Many = True
eqAmount _ _ Most Most = True
eqAmount _ _ Lots Lots = True
eqAmount _ _ _ _ = False

eqNat :: Int -> [(Var, Var)] -> Nat -> Nat -> Bool
eqNat n es (Nat x) (Nat x') = eqExp n es x x'

type Type = Exp

newtype Nat = Nat {fromNat :: Exp}

instance Num Nat where
  fromInteger n = Nat (Con (show n))
  (Nat x) + (Nat y) = Nat (BinOp Plus x y)

data Amount' n = One | Few | Several | Many | Most | Lots | Exact n | AtLeast n -- amount for the *positive* polarity
  deriving (Show,Eq,Functor,Foldable,Traversable)

type Amount = Amount' Nat 

data Op = Fld String -- ^ field lookup
        | Custom String
        | App
        | Not
        | And
        | Or
        | Plus
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

pattern Forall :: Var -> Type -> Exp -> Exp
pattern Forall x dom body = Quant One Neg x dom body
pattern Exists :: Var -> Type -> Exp -> Exp
pattern Exists x dom body = Quant One Pos x dom body

-- pattern Sigma x dom body = Quant Pi Pos x dom body
pattern MOST :: Var -> Type -> Exp -> Exp
pattern MOST x dom body = Quant Most Neg x dom  body
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

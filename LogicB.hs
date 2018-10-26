{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
module LogicB where

import qualified Logic as L
import Logic hiding (Exp(..), freeVars)
import Data.Char (toLower)
import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Traversable

data Next v = Here | There v deriving (Eq, Functor)
data Zero

deriving instance (Eq Zero)
deriving instance (Show Zero)

instance Applicative Next where
  pure = There
  Here <*> _ = Here
  _ <*> Here = Here
  There f <*> There a = There (f a)

newtype Nat = Nat Integer deriving (Show,Eq,Num,Enum,Integral,Ord,Real)

data Exp v where
  Op :: Op -> [Exp v] -> Exp v
  Con :: String -> Exp v
  V :: v -> Exp v
  Var :: String -> Exp v 
  Lam :: Exp (Next v) -> Exp v
  Quant :: Amount -> Pol -> Var -> (Exp v) -> (Exp v) -> Exp v
  deriving (Eq, Functor)


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

lapp :: Exp (Next w) -> Exp w -> Exp w
lapp f a = f >>= \case
  Here -> a
  There v -> V v


instance Applicative Exp where
  (<*>) = ap
  pure = V

instance Monad Exp where
  (>>=) :: forall v w. Exp v -> (v -> Exp w) -> Exp w
  e >>= f = case e of
    (V x) -> f x
    (Op p args) -> Op p (map (>>= f) args)
    (Con k) -> Con k
    (Var v) -> Var v
    (Quant a p v dom body) -> Quant a p v (dom >>= f) (body >>= f)
    (Lam t) -> Lam (t >>= f')
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

pattern Proj :: Exp v -> String -> Exp v
pattern Proj e f = Op (Fld f) [e]

pattern BinOp :: Op -> Exp v -> Exp v -> Exp v
pattern BinOp op x y = Op op [(x),(y)]

pattern UnOp :: Op -> Exp v -> Exp v
pattern UnOp op x = Op op [(x)]


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

ppExp :: Int -> Op -> Exp String -> String
ppExp n ctx e0 =
  let prns op x = if needsParens ctx op then parens x else x
  in case e0 of
      V x -> x
      (Lam f) -> parens ("fun " ++ varName n ++ " => " ++ ppExp (n+1) LAST_OPERATOR (f `lapp` (Var (varName n))))
      (Con x) -> x
      (Var x) -> x
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
      (Op App [f,arg]) -> prns App $ ppExp n Not f ++ " " ++ ppExp n App arg
      (Op op [x,y]) -> prns op $ ppExp n op x ++ " " ++ ppOp op ++ " " ++ ppExp n op y
      (Op op args) -> ppOp op ++ "(" ++ intercalate "," [ppExp n op a | (a) <- args] ++ ")"

normalize :: [Char] -> [Char]
normalize = map toLower


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


fromHOAS' :: L.Exp -> Exp v
fromHOAS' = fromHOAS 0 (error "nein!")

fromHOAS :: Int -> (Int -> v) -> L.Exp -> Exp v
fromHOAS n f = \case
  (L.Op op args) -> Op op (map (fromHOAS n f) args)
  (L.Con k) -> Con k
  (L.Quant a p v d b) -> Quant a p v (fromHOAS n f d) (fromHOAS n f b)
  (L.Var ('*':k)) -> V (f (read k))
  L.Var x -> Var x
  L.Lam t -> Lam (fromHOAS (n+1) (\x -> if x == n then Here else There (f n)) (t (L.Var ('*':show n))))



instance Show L.Exp where
  show = ppExp 1 Not . fromHOAS'

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
module Logic where

import Data.Char (toLower)
import Data.List
import Control.Applicative
import Control.Monad
import Control.Monad.State

type Var = String

data Exp = Op Op [Exp]
         | Var Var
         | Con String
         | Lam (Exp -> Exp)

instance Eq Exp where

type Type = Exp
data Op = THE
        | Fld String -- ^ field lookup
        | App
        | Not
        | And
        | Or
        | Implies
        | ImpliesOften
        | Qu Qu Pol Var Type
        deriving (Eq)

opPrc :: Op -> Int
opPrc = \case
  THE -> 0
  Fld _ -> 1
  App -> 2
  Not -> 3
  And -> 4
  Or -> 5
  ImpliesOften -> 6
  Implies -> 6
  Qu{} -> 7
  


pattern TRUE :: Exp
pattern TRUE = Con "true"

apps :: Exp -> [Exp] -> Exp
apps f args  = Op App (f:args)

true :: Exp
true = TRUE

pattern Proj :: Exp -> String -> Exp
pattern Proj e f = Op (Fld f) [e]

(-->),(~~>) :: Exp -> Exp -> Exp
x --> y = Op Implies [x,y]
x ~~> y = Op ImpliesOften [x,y]

pattern (:∧) :: Exp -> Exp -> Exp
pattern x :∧ y = Op And [x,y]

(∧) :: Exp -> Exp -> Exp
(x :∧ y) ∧ z = x :∧ (y ∧ z)
x ∧ y = x :∧ y
(∨) :: Exp -> Exp -> Exp
x ∨ y = Op Or [x,y]

data Qu = All | Most | Pi
        deriving (Eq,Ord)
data Pol = Pos | Neg
        deriving (Eq,Ord)

substOp :: Subst -> Op -> Op
substOp f (Qu q p v t) = Qu q p v (subst f t)
substOp _ op = op

subst :: Subst -> Exp -> Exp
subst f (Var x) = f x
subst _ (Con x) = Con x
subst f (Op o xs) = Op (substOp f o) (map (subst f) xs)

dualize :: Pol -> Pol
dualize Pos = Neg
dualize Neg = Pos

isAssoc :: Op -> Bool
isAssoc Implies = False
isAssoc ImpliesOften = False
isAssoc _ = True

needsParens :: Op -> Op -> Bool
needsParens ctx op = opPrc ctx < opPrc op || (opPrc ctx == opPrc op && not (isAssoc op))

instance Show Exp where
  show = ppExp Not


quoteTex :: String -> String
quoteTex = concatMap q
  where q x | x `elem` "_#\\%" = "\\" ++ [x]
            | otherwise = [x]

-- showTex :: Exp -> [Char]
-- showTex = texExp LAST_OPERATOR

ppOp :: Op -> [Char]
ppOp o = case o of
  THE -> "THE"
  Not -> "NOT"
  And -> "/\\"
  Or -> "\\/"
  Implies -> "->"
  ImpliesOften -> "~>"
  Qu k p v dom -> (++ (v ++ ":" ++ show dom ++ ".")) $ case (k,p) of
    (All,Neg) -> "FORALL"
    (All,Pos) -> "EXISTS"
    (Pi,Pos) -> "SIGMA"
    (Pi,Neg) -> "PI"
    (Most,Pos) -> "FEW "
    (Most,Neg) -> "MOST "


ppExp :: Op -> Exp -> String
ppExp _ (Var x) = x
ppExp _ (Lam f) = parens ("Lam FV. " ++ ppExp THE (f (Var "FV")))
ppExp _ (Con x) = x
ppExp op (Proj e f) = ppExp op e ++ "." ++ f
-- ppExp _ (Op op@(Custom _) args) = ppOp op ++ "(" ++ intercalate "," (map (ppExp op) args) ++ ")"
ppExp _ctx (Op App args) = parens $ intercalate " " $ map (ppExp App) args
ppExp ctx (Op op args) = prns $ case args of
  [x,y] -> ppExp op x ++ " " ++ ppOp op ++ " " ++ ppExp op y
  [x] -> ppOp op ++ " " ++ ppExp op x
  where prns x = if needsParens ctx op then parens x else x


parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

pattern The body =  Op THE [body]
pattern Quant k pol x dom body = Op (Qu k pol x dom) [body]
pattern Forall x dom body = Quant All Neg x dom body
pattern Exists x dom body = Quant All Pos x dom body
pattern Sigma x dom body = Quant Pi Pos x dom body
pattern MOST x dom body = Quant Most Neg x dom body
pattern FEW x dom body = Quant Most Pos x dom body

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
freeVars (Op _ xs) = (concatMap freeVars xs)

boundVars :: Exp -> [Var]
boundVars (Var _) = []
boundVars (Lam f) = boundVars (f (Con "__BOUND__")) 
boundVars (Con _) = []
boundVars (Quant _ _ x dom body) = x:boundVars dom++boundVars body
boundVars (Op _ xs) = concatMap boundVars xs

negativeContext :: (Num a, Eq a) => Op -> a -> Bool
negativeContext Implies 0 = True
negativeContext ImpliesOften 0 = True
negativeContext Not _ = True
negativeContext _ _ = False

-- FIMXE: rename
isQuant :: [Var] -> Exp -> Bool
isQuant x' e = case e of
  (Quant All _ x _ _) -> x `elem` x'
  _ -> False

matchQuantArg :: Alternative m => Monad m => [Var] -> [Exp] -> m ([Exp],Exp,[Exp])
matchQuantArg _ [] = fail "not found"
matchQuantArg x' (a:as) = (guard (isQuant x' a) >> return ([],a,as)) <|> do
  (l,q,r) <- matchQuantArg x' as
  return (a:l,q,r)

liftQuantifiers :: (Alternative m, Monad m) => [Var] -> Exp -> m Exp
liftQuantifiers _ (Var x) = return (Var x)
liftQuantifiers _ (Con x) = return (Con x)
liftQuantifiers xs (Op op args) = do
  (l,Quant All pol x dom body,r) <- matchQuantArg xs args
  let pol' = if negativeContext op (length l) then dualize pol else pol
  return (Quant All pol' x dom (Op op (l++body:r)))

bottomUp :: (Monad m) => (Exp -> m Exp) -> (Exp -> m Exp)
bottomUp f (Var x) = f (Var x)
bottomUp f (Con x) = f (Con x)
bottomUp f (Op op args) = do
  r <- Op op <$> mapM (bottomUp f) args
  f r

anywhere :: Alternative m => (Monad m) => (Exp -> m Exp) -> (Exp -> m Exp)
anywhere f (Var x) = f (Var x)
anywhere f (Con x) = f (Con x)
anywhere f e@(Op op args) = f e <|> Op op <$> mapM (anywhere f) args


liftQuantifiersAnyWhere :: (Monad m, Alternative m) => [Var] -> Exp -> m Exp
liftQuantifiersAnyWhere x = anywhere (liftQuantifiers x)


extendAllScopes :: Exp -> Exp
extendAllScopes e = case freeVars e `intersect` boundVars e of
  [] -> e
  xs -> case liftQuantifiersAnyWhere xs e of
    Nothing -> error "freevars, but nothing to lift!"
    -- Just e' -> if e == e' then e else extendAllScopes e'

type Subst = Var -> Exp

mkSubst :: [(Var,Exp)] -> Subst
mkSubst s x' = case lookup x' s of
  Nothing -> Var x'
  Just e -> e

after :: Subst -> Subst -> Subst
(s1 `after` s2) x = subst s1 (s2 x)

-- FIXME: there are actually accessible fields in the domain here. Are
-- they handled otherwise thanks to the substituting mechanism?
recordFields :: Exp -> [Var]
recordFields (Quant _ Pos y _ t) = y:recordFields t
recordFields _ = []

repairInnerfields :: MonadState Subst m => Exp -> m Exp
repairInnerfields (Con c) = return (Con c)
repairInnerfields (Var v) = do
  σ <- get
  return (σ v)
repairInnerfields (Quant k pol x dom body) = do
  dom' <- repairInnerfields dom
  -- Here, all the objects bound in the domain become inaccessible in
  -- the body; furthermore, no scope extension will make them visible
  -- again. But they are in fact easily accessible by taking a record
  -- projection IF the domain is a record. So we make sure that it is so at (1)
  modify (mkSubst [(y,Proj (Var x) y) | y <- recordFields dom] `after`)
  Quant k pol x dom' <$> repairInnerfields body

repairInnerfields (Op op as) = Op op <$> mapM repairInnerfields as
-- Fixme: repair op too

repairFields :: Exp -> Exp
repairFields e = evalState (repairInnerfields e) Var

substRepairFields :: Exp -> Subst
substRepairFields e = execState (repairInnerfields e) Var

unsupported :: Exp
unsupported = Var "unsupported"


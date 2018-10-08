{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module MS where

import Prelude hiding (pred)
import Control.Monad.State hiding (ap)
import Logic hiding (Pol)

type Object = Exp
type Prop = Exp


data Gender where
   Male :: Gender
   Female :: Gender
   Neutral :: Gender
   Unknown :: Gender -- male or female
  deriving (Eq,Show)

-- data Number where
--   Singular :: Number
--   Plural :: Number
--   deriving (Eq,Show)

data Role where
  Subject :: Role
  Other :: Role
  deriving (Eq,Show)

-- first :: (t2 -> t1) -> (t2, t) -> (t1, t)
-- first f (x,y) = (f x,y)
-- second :: forall t t1 t2. (t2 -> t1) -> (t, t2) -> (t, t1)
-- second f (x,y) = (x,f y)

data Descriptor = Descriptor {dGender :: Gender
                             ,dNumber :: Number
                             ,dRole :: Role} deriving Show

type ObjQuery = Descriptor -> Bool
type ObjEnv = [(Descriptor,NP)]
type NounEnv = [CN]


clearRole :: Env -> Env
clearRole Env{..} = Env{objEnv = map cr objEnv,..}
  where cr (d,np) = (d {dRole = Other},np)

type VPEnv = VP
-- Just remember the last VP; could be more fine-grained because we have "does", "is", "has" as placehodlers in English.

data Env = Env {vpEnv :: VPEnv
               ,vp2Env :: V2
               ,apEnv :: AP
               ,cn2Env :: CN2
               ,objEnv :: ObjEnv
               ,cnEnv :: NounEnv
               ,sEnv :: S
               ,envThings :: Exp -> Object -- map from CN to pure objects
               ,envSloppyFeatures :: Bool
               ,freshVars :: [String]}
         -- deriving Show

------------------------------
-- Gets

isNeutral, isMale, isFemale :: Descriptor -> Bool
isMale Descriptor{..} = dGender `elem` [Unknown, Male]
isFemale Descriptor{..} = dGender `elem` [Unknown, Female]
isNeutral Descriptor{..} = dGender `elem` [Neutral]

isSingular :: Descriptor -> Bool
isSingular = (== Singular) . dNumber

isPlural :: Descriptor -> Bool
isPlural = (== Plural) . dNumber

isNotSubject :: Descriptor -> Bool
isNotSubject = (/= Subject) . dRole

isCoArgument :: Descriptor -> Bool
isCoArgument = (== Subject) . dRole

getCN :: Env -> CN
getCN Env{cnEnv=cn:_} = cn
getCN _ = assumedCN

getCN2 :: Env -> CN2
getCN2 Env{cn2Env=cn} = cn

getNP' :: ObjQuery -> Env -> NP
getNP' _q Env{objEnv=[]} = return $ MkNP assumedNumber (\_num _cn _role -> return (\vp -> vp (constant "assumedNP"))) assumedCN
getNP' q Env{objEnv=((d,o):os),..} = if q d then o else getNP' q Env{objEnv=os,..}


getNP :: ObjQuery -> Dynamic NP
getNP q = gets (getNP' q)

-------------------------------
-- Pushes
pushNP :: Descriptor -> NP -> Env -> Env
pushNP d o1 Env{..} = Env{objEnv = (d,o1):objEnv,..}

pushCN :: CN -> Env -> Env
pushCN cn Env{..} = Env{cnEnv=cn:cnEnv,..}

pushVP :: VP -> Env -> Env
pushVP vp Env{..} = Env{vpEnv=vp,..}

pushV2 :: V2 -> Env -> Env
pushV2 vp2 Env{..} = Env{vp2Env=vp2,..}

pushAP :: AP -> Env -> Env
pushAP a Env{..} = Env{apEnv=a,..}

pushCN2 :: CN2 -> Env -> Env
pushCN2 cn2 Env{..} = Env{cn2Env=cn2,..}

pushS :: S -> Env -> Env
pushS s Env{..} = Env{sEnv=s,..}

allVars :: [String]
allVars = map (:[]) ['a'..'z'] ++ cycle (map (:[]) ['α'..'ω'])

type Dynamic a = (State Env a)
type Effect = Dynamic Prop

mkPred :: String -> Object -> Prop
mkPred p x = Op (Custom p) [x]

mkRel2 :: String -> Object -> Object -> Prop
mkRel2 p x y = Op (Custom p) [x,y]

mkRel3 :: String -> Object -> Object -> Object -> Prop
mkRel3 p x y z = Op (Custom p) [x,y,z]

constant :: String -> Exp
constant x = Con x

pureObj :: Exp -> Number -> CN -> NP
pureObj x number cn  = return $ MkNP number (\_number _cn _role -> return $ \vp -> vp x) cn

-- _ _ return (\vp -> vp (x))

pureVar :: Var -> Number -> CN -> NP
pureVar x = pureObj (Var x)

-- pureIntersectiveAP :: (Object -> Prop) -> AP
-- pureIntersectiveAP q = do
--   modify (pushAP (pureIntersectiveAP q))
--   x <- getFresh
--   return (\typ -> Sigma x typ (q (Var x)))

getFresh :: Dynamic String
getFresh = do
  (x:_) <- gets freshVars
  modify (\Env{freshVars=_:freshVars,..} -> Env{..})
  return x


----------------------------------
-- Assumed

-- assumedPred :: String -> Dynamic (Object -> Prop)
-- assumedPred predName = do
--   return $ \x -> (mkPred predName x)

assumedCN :: CN
assumedCN = return (mkPred "assumedCN",Unknown)

assumedNumber :: Number
assumedNumber = Singular

assumed :: Env
assumed = Env {
              vp2Env = return $ \x y -> (mkRel2 "assumedV2" x y)
               --, vpEnv = assumedPred "assumedVP"
              -- ,apEnv = (pureIntersectiveAP (mkPred "assumedAP"))
              -- ,cn2Env = pureCN2 (mkPred "assumedCN2") Neutral Singular
              ,objEnv = []
              ,sEnv = return (constant "assumedS")
              ,cnEnv = [assumedCN]
              ,envThings = \x -> Op THE [x]
              ,envSloppyFeatures = False
              ,freshVars = allVars}

_TRUE :: Effect -> Prop
_TRUE x = evalState x assumed

_ENV :: Effect -> Env
_ENV x = execState x assumed

type S' = Prop
type S = Dynamic Prop
type VP' = (Object -> Prop)
-- type VP' = (({-subjectClass-} Object -> Prop) -> Object -> Prop) -- in Coq
type VP = Dynamic VP'
type V2 = Dynamic (Object -> Object -> Prop)
type V3 = Dynamic (Object -> Object -> Object -> Prop)
type CN' = (Object -> Prop,Gender)
type CN = Dynamic CN'
type AP = Dynamic (Type -> Type)
type CN2 = Dynamic ((Object -> Type),Gender,Number)
type NP' = ((Object -> Prop) -> Prop)
type NP = Dynamic NPData
type AdvV = Dynamic ((Object -> Prop) -> (Object -> Prop))

type V = Dynamic (Object -> Prop)
type V2S = Dynamic (Object -> S' -> Object -> Prop)
type V2V = Dynamic (Object -> VP' -> Object -> Prop)
type VV = Dynamic (VP' -> Object -> Prop)
type Subj = Dynamic (Prop -> Prop -> Prop)
type SC = Dynamic (VP')
type VPS = Dynamic (VP')
type VS = Dynamic (S -> VP')

-- Definition NP0 := VP ->Prop.
-- Definition NP1 := (object -> Prop) ->Prop.

type A' = Object -> Prop
type Cl =  Dynamic (Prop)
type Temp =  (Prop -> Prop) 
type Phr =  Dynamic (Prop)
type Ord = Dynamic ( A' )
type Comp  = Dynamic ( VP') 
type Predet  = Dynamic ( NP' -> NP')
type AdA  = Dynamic (A' -> A')
type ClSlash  = Dynamic (VP') 
type RCl  = Dynamic (RCl')
type RCl' = VP'
type RS  = Dynamic ( RCl')
type Pol = Prop -> Prop


data Nat = Nat Integer deriving (Show,Eq)

data Number where
  Singular :: Number
  Plural   :: Number
  UnknownNumber :: Number
  MoreThan :: Number -> Number
  Cardinal :: Nat -> Number
  deriving (Show,Eq)

numSg :: Number
numSg = Singular

data NPData where
  MkNP :: Number -> Quant -> CN -> NPData

type N = CN


all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

-------------------
-- "PureX"
genderedN :: String -> Gender -> CN
genderedN s gender =
  do modify (pushCN (genderedN s gender))
     return (mkPred s,gender)

pureV2 :: (Object -> Object -> Prop) -> V2
pureV2 v2 = do
  modify (pushV2 (pureV2 v2))
  return (\y x -> (v2 x y))

pureV3 :: (Object -> Object -> Object -> Prop) -> V3
pureV3 v3 = do
  -- modify (pushV2 (pureV2 v2)) -- no v3 yet in the env
  return v3

-----------------
-- Lexemes

lexemeN :: String -> N
lexemeN x = genderedN x Unknown

lexemeV2 :: String -> V2
lexemeV2 x = pureV2 (mkRel2 x)

---------------------
-- Unimplemented categories

past :: Temp
past = id

pPos :: Pol
pPos = id

--------------------
-- CNs

useN :: N -> CN
useN = id


------------------------
-- NP
interpNP :: NP -> Role -> Dynamic NP'
interpNP np role = do
  MkNP n q c <- np
  q n c role

detCN :: Det -> CN -> NP
detCN (num,quant) cn = return (MkNP num quant cn)

usePron :: Pron -> NP
usePron q = do
  np <- getNP q
  np

----------------------
-- Pron

type Pron = ObjQuery

sheRefl_Pron :: Pron
sheRefl_Pron = (all' [isFemale, isSingular, isCoArgument])

-- his :: CN2 -> NP
-- his cn2 role = do
--   (isSloppy :: Bool) <- gets envSloppyFeatures
--   poss (pron (\x -> isSloppy || (all' [isMale, isSingular] x))) cn2 role


---------------------------
-- Det

type Det = (Number,Quant)

detQuant :: Quant -> Number -> Det
detQuant q n = (n,q)

every_Det :: Det
every_Det = (UnknownNumber {- FIXME? -},) $ \number cn role -> do -- allow any number so that it can be reused in 'few'
  x <- getFresh
  (cn',gender) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x number cn))
  return $ \vp' -> (Forall x (cn' (Var x)) (vp' (Var x)))

----------------------------
-- VPSlash
type VPSlash = V2

slashV2a :: V2 -> VPSlash
slashV2a = id

complSlash :: VPSlash -> NP -> VP
complSlash v2 directObject = do
  v2' <- v2
  do' <- interpNP directObject Other
  modify (pushVP (complSlash v2 directObject))
  return (\y -> do' $ \x -> (v2' x y))

----------------------------
-- Cl

predVP :: NP -> VP -> Effect
predVP np vp = do
  np' <- interpNP np Subject
  vp' <- vp
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the direct arguments.
  modify (pushS (predVP np vp))
  return (np' vp')


--------------------
-- S, Phr
sentence :: S -> Phr
sentence = id


useCl :: Temp -> Pol -> Cl -> S
useCl = \temp pol cl -> temp <$> (pol <$> cl)

-------------------------
-- Quant

type Quant' = (Number -> CN -> Role -> Dynamic NP')
type Quant = Quant'

possPron :: Pron -> Quant
possPron q _number cn _role = do
  np <- getNP q
  them <- interpNP np Other -- only the direct arguments need to be referred by "self"
  (cn', _gender) <- cn
  x <- getFresh
  return (\vp' -> them $ \y -> Forall x (cn' (Var x) ∧ mkRel2 "HAVE" y (Var x)) (vp' (Var x)))


-- _of :: CN2 -> NP -> CN
-- _of cn2 np =
--   do (cn2',gender,number) <- cn2
--      them <- np Other -- only the direct arguments need to be referred by "self"
--      return (them cn2',gender,number)


{-

(!) :: NP -> VP -> Effect
(!) = predVP


(?) :: V2 -> NP -> VP
(?) = appV2

appV2 :: V2 -> NP -> VP
appV2 v2 directObject = do
  v2' <- v2
  do' <- directObject Other
  modify (pushVP (appV2 v2 directObject))
  return (\y -> do' $ \x -> (v2' x y))

(¿) :: NP -> V2 -> VP
(¿) = slashVP

slashVP :: NP -> V2 -> VP
slashVP subj v2 = do
  subj' <- subj Subject
  v2' <- v2
  -- Don't push these things (slash vps).
  return $ \x -> subj' $ \y -> v2' x y

appV3 :: V3 -> NP -> V2
appV3 v3 obj = do
  v3' <- v3
  o' <- obj Other
  -- Don't push these things (not implemented)
  return $ \x y -> o' $ \z -> v3' z x y

  
-- instance Show VP where
--   show vp = "λω. " ++ mkRec (evalState (vp "ω") assumed)
-- instance Show NP where
--   show np = mkRec (evalState (np Other $ \x -> return [("_",x)]) assumed)


pushThing :: Exp -> Var -> Env -> Env
pushThing source target Env{..} = Env{envThings = \x -> if x == source then Var target else envThings x,..}


pureNP :: Object -> Gender ->  Number -> NP
pureNP o dGender dNumber dRole = do
  modify (pushNP (Descriptor{..}) (pureNP o dGender dNumber))
  return (\vp -> vp o)
  

purePN ::  String -> Gender -> NP
purePN o dGender = pureNP (Con o) dGender Singular

sheNP :: NP
sheNP = pron (all' [isFemale, isSingular])

himNP :: NP
himNP = pron (all' [isMale, isSingular, isNotSubject])

herNP :: NP
herNP = pron (all' [isFemale, isSingular, isNotSubject])

heNP :: NP
heNP = pron (all' [isMale, isSingular])


theySingNP :: NP -- as in everyone owns their book 
theySingNP = pron (isSingular)

themSingNP :: NP -- as in everyone owns their book 
themSingNP = pron (all' [isSingular, isNotSubject])

itNP :: NP
itNP =  pron (all' [isNeutral, isSingular])

-- nthNP :: Int -> Role -> VP -> Env -> (Prop, Env)
-- nthNP n = \role vp ρ -> (getNthNP n ρ) role vp ρ

theyPlNP :: NP
theyPlNP = pron isPlural

poss :: NP -> CN2 -> NP
poss np cn2 role =
  do them <- np Other -- only the direct arguments need to be referred by "self"
     (cn2',gender,number) <- cn2
     modify (pushNP (Descriptor gender number role) (poss np cn2))
     the' (return (them cn2',gender,number)) Other

_of :: CN2 -> NP -> CN
_of cn2 np =
  do (cn2',gender,number) <- cn2
     them <- np Other -- only the direct arguments need to be referred by "self"
     return (them cn2',gender,number)

his :: CN2 -> NP
his cn2 role = do
  (isSloppy :: Bool) <- gets envSloppyFeatures
  poss (pron (\x -> isSloppy || (all' [isMale, isSingular] x))) cn2 role

their :: CN2 -> NP
their = poss theyPlNP

its :: CN2 -> NP
its = poss itNP


-- TODO: remove
-- | Definite which cannot look up in the environment (mostly because
-- our environment does not contain the necessary information)
the' :: CN -> NP
the' cn _role = do
  (cn',_g,_n) <- cn
  return $ \vp -> vp (The cn')

-- | Definite which looks up in the environment.
the :: CN -> NP
the cn role = do
  (cn',gender,number) <- cn
  it <- ($ cn') <$> gets (envThings)
  -- note that here we push the actual object (it seems that the strict reading is preferred in this case)
  pureNP it gender number role

(<==)  :: Effect -> Effect -> Effect
a <== b = do
  a' <- a
  b' <- b
  return (b' --> a')


imply :: Monad m => (t1 -> t -> b) -> m t1 -> m t -> m b
imply implication a b = do
  a' <- a
  b' <- b
  return (implication a' b')

(==>) :: Effect -> Effect -> Effect
(==>) = imply (-->)

not' :: Exp -> Exp
not' x = Op Not [x]

negation :: Effect -> Effect
negation x = not' <$> x

(###) :: Effect -> Effect -> Effect
(###) = liftM2 (∧)

pureVP :: (Object -> Prop) -> VP
pureVP v = do
  modify (pushVP (pureVP v))
  return v
-- pushes itself in the env for reference


pureCN2 :: (Object -> Type) -> Gender -> Number -> CN2
pureCN2 v gender number = do
  modify (pushCN2 (pureCN2 v gender number))
  return (v,gender,number)


pureEval :: Effect -> Exp
pureEval = extendAllScopes . repairFields . _TRUE

eval :: Effect -> IO ()
eval = print . pureEval

evalDbg :: Effect -> IO ()
evalDbg e = do
  let p = _TRUE e
  let r = repairFields p
      q = extendAllScopes r
  print p
  print r
  print q
  print (freeVars q)

doesTooVP :: VP
doesTooVP = do
  vp <- gets vpEnv
  sloppily vp

-- admitVP :: S -> VP
-- admitVP p = do
--   p' <- p
--   modify (pushVP (admitVP p))
--   return (\x -> (_ADMIT_V (p') x))

-- may :: VP -> VP
-- may vp = do
--   vp' <- vp
--   modify (pushVP (may vp))
--   return (\x -> mkPred "may" (vp' x))

everyone :: NP
everyone = every (pureCN (constant "PERSON") Unknown Singular)

hide :: State s x -> State s x
hide a = do
  s <- get
  x <- a
  put s
  return x

unbound :: String
unbound = "<unbound>"

that :: CN -> VP -> CN
that cn vp = do
    x <- getFresh
    -- creating a variable here is less
    -- than ideal because the NP
    -- (quantifier) will already have created a suitable variable to refer to the CN.
    -- Example:
    -- (FEW a:(∃b:MAN. LOVE((THE c:MARRIED(b). TRUE),b)). BEAT(a,(THE d:MARRIED(b). TRUE)))
    -- Really we'd like to have a reference to 'a' directly, but it is out of scope.
    (cn',gender,number) <- cn
    modify (pushNP (Descriptor gender number Subject) (pureVar x))
    vp' <- vp
    return (Sigma x cn' (vp' (Var x)),gender,number)

-}


{-
some :: CN -> NP
some cn role = do
  x <- getFresh
  (cn',gender,number) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x))
  return (\vp' -> Exists x cn' (vp' (Var x)))

few :: CN -> NP
few (cn) role = do
  x <- getFresh
  z <- getFresh
  (cn',gender,Plural) <- cn
  modify (pushNP (Descriptor gender Plural role) (pureVar x))
  return $ \vp' -> FEW x cn' (vp' (Var x)) ∧ Forall z (Sigma x cn' (vp' (Var x))) true

most :: CN -> NP
most (cn) role = do
  x <- getFresh
  z <- getFresh
  (cn',gender,Plural) <- cn
  modify (pushNP (Descriptor gender Plural role) (pureVar x))
  return $ \vp' -> MOST x cn' (vp' (Var x)) ∧ Forall z (Sigma x cn' (vp' (Var x))) true


-- hisSpouseNP :: NP
-- hisSpouseNP = his marriedCN2

lovesVP :: NP -> VP
lovesVP directObject = do
  do' <- directObject Other
  pureVP $ \y -> do' $ \x -> (mkRel2 "LOVE" x y)



-- thereIs :: CN -> S
-- thereIs cn = do
--   x <- getFresh
--   (cn',gender,number) <- cn
--   modify (pushNP (Descriptor gender number Subject) (pureVar x))
--   modify (pushThing cn' x)
--   return (Exists x cn' (isHere (Var x)))

aDet :: CN -> NP
aDet cn role = do
  x <- getFresh
  (cn',gender,number) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x))
  modify (pushThing cn' x)
  return (\vp' -> Exists x cn' (vp' (Var x)))


one :: CN
one = do
  cn <- gets getCN
  cn

thatOf :: NP -> NP
thatOf x role = do
  cn2 <- gets getCN2
  the (cn2 `_of` x) role

oneToo :: NP
oneToo role = aDet one role

sloppily :: Dynamic a -> Dynamic a
sloppily = withState (\Env{..} -> Env{envSloppyFeatures = True,..})

doTooV2 :: V2
doTooV2 = do
  v2 <- gets vp2Env
  sloppily v2

hasTooV2 :: V2
hasTooV2 = doTooV2

so :: S
so = do
  s <- gets sEnv
  s

suchDet :: CN -> NP
suchDet (cn) role = do
  ap <- gets apEnv
  ap' <- ap
  x <- getFresh
  (cn',gender,number) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x))
  return $ \vp' -> (Forall x (ap' cn') (vp' (Var x)))


oldAP :: AP
oldAP = pureIntersectiveAP (mkPred "old")

redAP :: AP
redAP = pureIntersectiveAP (mkPred "red")


donkeys :: CN
donkeys = pureCN (constant "donkeys") Neutral Plural

(#) :: AP -> CN -> CN
ap # cn = do
  ap' <- ap
  (cn', g,n) <- cn
  return (ap' cn',g,n)

carCN :: CN
carCN = pureCN (constant "car") Neutral Singular

bathroomCN :: CN
bathroomCN = pureCN (constant "bathroom") Neutral Singular

hatCN2 :: CN2
hatCN2 = pureCN2 (mkPred "hat") Neutral Singular

colleaguesCN2 :: CN2
colleaguesCN2 = pureCN2 (mkPred "colleagues") Neutral Singular

shouldersCN2 :: CN2
shouldersCN2 = pureCN2 (mkPred "shoulders") Neutral Singular

carsCN :: CN
carsCN = pureCN (constant "cars") Neutral Plural

slappedV2 :: V2
slappedV2 = pureV2 (mkRel2 "slapped")
hurtV2 :: V2
hurtV2 = pureV2 (mkRel2 "hurt")

is_wiser_thanV2 :: V2
is_wiser_thanV2 = pureV2 (mkRel2 "wiser")

is_larger_thanV2 :: V2
is_larger_thanV2 = pureV2 (mkRel2 "larger")

gaveV3 :: V3
gaveV3 = pureV3 (mkRel3 "gave")

andNP :: NP -> NP -> NP
andNP np1 np2 role = do
  np1' <- np1 role
  np2' <- np2 role
  return (\vp -> np1' vp ∧ np2' vp)

andVP :: VP -> VP -> VP
andVP np1 np2 = do
  np1' <- np1
  np2' <- np2
  return (\x -> np1' x ∧ np2' x)

type AdVP = Dynamic ((Object -> Prop) -> (Object -> Prop))


pureAdVP :: String -> AdVP
pureAdVP name = return (\vp x -> mkPred name (vp x))


adVP :: VP -> AdVP ->  VP
adVP vp ad = do
  vp' <- vp
  ad' <- ad
  modify (pushVP (adVP vp ad))
  return (ad' vp')


-- everyday :: AdVP
-- everyday = pureAdVP "everyday"
-- today :: AdVP
-- today = pureAdVP "today"
-- thisEvening :: AdVP
-- thisEvening = pureAdVP "this_evening"
-- onSundays :: AdVP
-- onSundays = pureAdVP "on_sundays"


-- CN2 example%


orS :: S -> S -> S
orS s1 s2 = (∨) <$> s1 <*> s2


-- >>> evalDbg exx1
-- (¬ (∃a:bathroom. here(a)) ∨ Hidden(a))
-- (¬ (∃a:bathroom. here(a)) ∨ Hidden(a))
-- (∃a:bathroom. ¬ here(a) ∨ Hidden(a))
-- []

unsupported :: Effect
unsupported = return (constant "unsupported")

-}

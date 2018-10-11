{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

--------------------------------
-- Operators

not' :: Exp -> Exp
not' x = Op Not [x]

(###) :: Effect -> Effect -> Effect
(###) = liftM2 (∧)


data Gender where
   Male :: Gender
   Female :: Gender
   Neutral :: Gender
   Unknown :: Gender -- male or female
  deriving (Eq,Show)

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

isPerson :: Descriptor -> Bool
isPerson = const True -- FIXME

isSingular :: Descriptor -> Bool
isSingular Descriptor {..} = dNumber `elem` [Singular, Unspecified]

isPlural :: Descriptor -> Bool
isPlural Descriptor {..} = dNumber `elem` [Plural, Unspecified] -- FIXME

isNotSubject :: Descriptor -> Bool
isNotSubject = (/= Subject) . dRole

isCoArgument :: Descriptor -> Bool
isCoArgument = (== Subject) . dRole

getCN :: Env -> CN
getCN Env{cnEnv=cn:_} = cn
getCN _ = return assumedCN

getCN2 :: Env -> CN2
getCN2 Env{cn2Env=cn} = cn

getNP' :: ObjQuery -> Env -> NP
getNP' _q Env{objEnv=[]} = return $ MkNP assumedNumber (\_num _cn _role -> return (\vp -> vp (constant "assumedNP"))) assumedCN
getNP' q Env{objEnv=((d,o):os),..} = if q d then o else getNP' q Env{objEnv=os,..}


getNP :: ObjQuery -> Dynamic NP
getNP q = gets (getNP' q)


getDefinite :: CN' -> Dynamic Object
getDefinite (cn',_gender) = do
  things <- gets envThings
  return (things (cn' (constant "__DEFINITE__")))

-------------------------------
-- Pushes


pushThing :: (Object -> Prop) -> Var -> Env -> Env
pushThing source target Env{..} = Env{envThings = \x -> if x == source (constant "__DEFINITE__") then Var target else envThings x,..}

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

----------------------------------
-- Effects/Dynamic

allVars :: [String]
allVars = map (:[]) ['a'..'z'] ++ cycle (map (:[]) ['α'..'ω'])

type Dynamic a = (State Env a)
type Effect = Dynamic Prop

mkPred :: String -> Object -> Prop
mkPred p x = Con p `apps` [x]

mkRel2 :: String -> Object -> Object -> Prop
mkRel2 p x y = Con p `apps` [x,y]

mkRel3 :: String -> Object -> Object -> Object -> Prop
mkRel3 p x y z = Con p `apps` [x,y,z]

constant :: String -> Exp
constant x = Con x

pureObj :: Exp -> Number -> CN' -> NP
pureObj x number cn  = return $ MkNP number (\_number _cn _role -> return $ \vp -> vp x) cn

-- _ _ return (\vp -> vp (x))

pureVar :: Var -> Number -> CN' -> NP
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

assumedPred :: String -> Dynamic (Object -> Prop)
assumedPred predName = do
  return $ \x -> (mkPred predName x)

assumedCN :: CN'
assumedCN = (mkPred "assumedCN",Unknown)

assumedNumber :: Number
assumedNumber = Singular

assumed :: Env
assumed = Env {
              vp2Env = return $ \x y -> (mkRel2 "assumedV2" x y)
               , vpEnv = assumedPred "assumedVP"
              -- ,apEnv = (pureIntersectiveAP (mkPred "assumedAP"))
              -- ,cn2Env = pureCN2 (mkPred "assumedCN2") Neutral Singular
              ,objEnv = []
              ,sEnv = return (constant "assumedS")
              ,cnEnv = [return assumedCN]
              ,envThings = \x -> Op THE [x]
              ,envSloppyFeatures = False
              ,freshVars = allVars}

_TRUE :: Effect -> Prop
_TRUE x = evalState x assumed

_ENV :: Effect -> Env
_ENV x = execState x assumed

type S' = Prop
type S = Dynamic Prop
type V2 = Dynamic (Object -> Object -> Prop) --  Object first, subject second.
type V3 = Dynamic (Object -> Object -> Object -> Prop)
type CN' = (Object -> Prop,Gender)
type CN = Dynamic CN'
type AP = Dynamic A'
type CN2 = Dynamic ((Object -> Type),Gender,Number)
type NP' = ((Object -> Prop) -> Prop)
type NP = Dynamic NPData

type V = Dynamic (Object -> Prop)
type V2S = Dynamic (Object -> S' -> Object -> Prop)
type V2V = Dynamic (Object -> VP' -> Object -> Prop)
type VV = Dynamic (VP' -> Object -> Prop)
type SC = Dynamic (VP')
type VS = Dynamic (S' -> VP')

-- Definition NP0 := VP ->Prop.
-- Definition NP1 := (object -> Prop) ->Prop.

type Cl =  Dynamic Prop
type Temp = Prop -> Prop
type Ord = Dynamic  A'
type Predet = NPData -> NPData
type AdA  = Dynamic (A' -> A')
type ClSlash  = Dynamic VP'
type RCl  = Dynamic RCl'
type RCl' = VP'
type RS  = Dynamic RCl'
type Pol = Prop -> Prop



data Number where
  Singular :: Number
  Plural   :: Number
  Unspecified :: Number
  MoreThan :: Number -> Number
  Cardinal :: Nat -> Number
  deriving (Show,Eq)

numSg,numPl :: Number
numSg = Singular
numPl = Singular

data NPData where
  MkNP :: Number -> Quant -> CN' -> NPData

type N = CN
type PN = (String,Gender,Number)

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

any' :: [a -> Bool] -> a -> Bool
any' fs x = any ($ x) fs

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

lexemeV :: String -> V
lexemeV x = return $ mkPred x

lexemeA :: String -> A
lexemeA a = return $ \cn obj -> apps (Con a) [Lam cn, obj]

lexemeV3 :: String -> V3
lexemeV3 x = return $ mkRel3 x

lexemeAdv :: String -> Adv
lexemeAdv adv = return $ \vp subj -> apps (Con adv) [Lam vp, subj]

lexemeAdV :: String -> AdV
lexemeAdV adv = return $ \vp subj -> apps (Con adv) [Lam vp, subj]

lexemeV2 :: String -> V2
lexemeV2 x = pureV2 (mkRel2 x)

lexemeV2S :: String -> V2S
lexemeV2S v2s = return $ mkRel3 v2s

lexemeVS :: String -> VS
lexemeVS vs = return $ \s x -> mkRel2 vs s x

lexemeV2V :: String -> V2V
lexemeV2V v2v = return $ \x vp y -> apps (Con v2v) [x,Lam vp,y]

lexemePN :: String -> PN
lexemePN x@"smith_PN" = (x,Female,Singular)
lexemePN x = (x,Unknown,Unspecified)

type Prep = Dynamic (Object -> VP' -> VP')
lexemePrep :: String -> Prep
lexemePrep prep  = return $ \x vp subj -> apps (Con prep) [x, Lam vp, subj]

type PConj = String

lexemePConj :: String -> PConj
lexemePConj = id

type RP = ()
lexemeRP :: String -> RP
lexemeRP _ = ()

idRP :: RP
idRP = ()

---------------------
-- Unimplemented categories

future,pastPerfect,past,present,presentPerfect :: Temp
past = id
present = id
presentPerfect = id
pastPerfect = id
future = id

pPos :: Pol
pPos = id

pNeg :: Pol
pNeg = not'

uncNeg :: Pol
uncNeg = not'

-----------------
-- Numbers

numCard :: Nat -> Number
numCard = Cardinal

numNumeral :: Integer -> Nat
numNumeral = Nat

n_two :: Integer
n_two = 2
n_10 :: Integer
n_10 = 10
n_100 :: Integer
n_100 = 100
n_13 :: Integer
n_13 = 13
n_14 :: Integer
n_14 = 14
n_15 :: Integer
n_15 = 15
n_150 :: Integer
n_150 = 150
n_2 :: Integer
n_2 = 2
n_2500 :: Integer
n_2500 = 2500
n_3000 :: Integer
n_3000 = 3000
n_4 :: Integer
n_4 = 4
n_500 :: Integer
n_500 = 500
n_5500 :: Integer
n_5500 = 5500
n_8 :: Integer
n_8 = 8
n_99 :: Integer
n_99 = 99
n_eight :: Integer
n_eight = 8
n_eleven :: Integer
n_eleven = 11
n_five :: Integer
n_five = 5
n_fortyfive :: Integer
n_fortyfive = 45
n_four :: Integer
n_four = 4
n_one :: Integer
n_one = 1
n_six :: Integer
n_six = 6
n_sixteen :: Integer
n_sixteen = 16
n_ten :: Integer
n_ten = 10
n_three :: Integer
n_three = 3
n_twenty :: Integer
n_twenty = 20


--------------------
-- A

type A = Dynamic A'
type A' = (Object -> Prop) -> (Object -> Prop)

positA :: A -> A
positA = id

--------------------
-- Subjs
type Subj = Dynamic (Prop -> Prop -> Prop)

before_Subj :: Subj
before_Subj = return (∧) -- no tense


--------------------
-- Adv

type ADV = Dynamic (VP' -> VP')
type Adv = ADV
type AdvV = ADV
type AdV = ADV

prepNP :: Prep -> NP -> AdV
prepNP prep np = do
  prep' <- prep
  np' <- interpNP np Other
  return (\vp' subj -> np' $ \x -> prep' x vp' subj)

subjS :: Subj -> S -> Adv
subjS subj s = do
  subj' <- subj
  s' <- s
  return $ \vp x -> subj' s' (vp x)


--------------------
-- CN

useN :: N -> CN
useN = id

relCN :: CN->RS->CN
relCN cn rs = do
  (cn',gender) <- cn
  rs' <- rs
  return $ (\x -> cn' x ∧ rs' x, gender)
   -- GF FIXME: Relative clauses should apply to NPs. See 013, 027, 044.  

advCN :: CN -> Adv -> CN
advCN cn adv = do
  (cn',gender) <- cn
  adv' <- adv
  return (adv' cn',gender)

adjCN :: A -> CN -> CN
adjCN a cn = do
  a' <- a
  (cn',gendr) <- cn
  return $ (a' cn',gendr)

elliptic_CN :: CN
elliptic_CN = do
  cn <- gets getCN
  cn


------------------------
-- NP
interpNP :: NP -> Role -> Dynamic NP'
interpNP np role = do
  MkNP n q c <- np
  q n c role

usePN ::  PN -> NP
usePN (o,g,n) = pureNP (Con o) g n Subject -- FIXME: role

pureNP :: Object -> Gender -> Number -> Role -> NP
pureNP o dGender dNumber dRole = do
  modify (pushNP (Descriptor{..}) (pureNP o dGender dNumber dRole))
  return $ MkNP Singular q (\_ -> true,dGender)
  where q :: Quant
        q _dNumber _oClass _dRole = do
          return (\vp -> vp o)

massNP :: CN -> NP
massNP cn = do
  cn' <- cn
  return $ MkNP Singular some_Quant cn'

detCN :: Det -> CN -> NP
detCN (num,quant) cn = do
  cn' <- cn
  return (MkNP num quant cn')

usePron :: Pron -> NP
usePron = id 

advNP :: NP -> Adv -> NP
advNP np adv = do
  MkNP num1 q1 (cn1,gender1) <- np
  adv' <- adv
  return $ MkNP num1
           (\num' cn' role -> do
               p1 <- q1 num' cn' role
               return $ \vp -> (p1 (adv' vp)))
           (cn1,gender1)

predetNP :: Predet -> NP -> NP
predetNP f np = do
  np' <- np
  return (f np')

-- FIXME: WTF?
detNP :: Det -> NP
detNP (number,quant) =
  return (MkNP number quant (const TRUE {- fixme -},Unknown))


pPartNP :: NP -> V2 -> NP  -- Word of warning: in FraCas partitives always behave like intersection, which is probably not true in general
pPartNP np v2 = do
  MkNP num q (cn,gender) <- np
  v2' <- v2
  subject <- getFresh
  return $ MkNP num q ((\x -> cn x ∧ Exists subject true (v2' x (Var subject))),gender)

relNPa :: NP -> RS -> NP
relNPa np rs = do
  MkNP num q (cn,gender) <- np
  rs' <- rs
  return $ MkNP num q (\x -> cn x ∧ rs' x, gender)


conjNP2 :: Conj -> NP -> NP -> NP
conjNP2 c np1 np2 = do
  MkNP num1 q1 (cn1,gender1) <- np1
  MkNP _num2 q2 (cn2,_gender2) <- np2
  return $ MkNP (num1) {- FIXME add numbers? min? max? -}
                -- (\num' cn' vp -> apConj2 c (q1 num' cn' vp) (q2 num' cn' vp))
                (\num' cn' role -> do
                    p1 <- q1 num' cn' role
                    p2 <- q2 num' cn' role
                    return $ \vp -> apConj2 c (p1 vp) (p2 vp))
                (\x -> cn1 x ∨ cn2 x, gender1)

conjNP3 :: Conj -> NP -> NP -> NP -> NP
conjNP3 c np1 np2 np3 = do
  MkNP num1 q1 (cn1,gender1) <- np1
  MkNP _num2 q2 (cn2,_gender2) <- np2
  MkNP _num3 q3 (cn3,_gender3) <- np3
  return $ MkNP (num1) {- FIXME add numbers? min? max? -}
                -- (\num' cn' vp -> apConj2 c (q1 num' cn' vp) (q2 num' cn' vp))
                (\num' cn' role -> do
                    p1 <- q1 num' cn' role
                    p2 <- q2 num' cn' role
                    p3 <- q3 num' cn' role
                    return $ \vp -> apConj3 c (p1 vp) (p2 vp) (p3 vp))
                (\x -> cn1 x ∨ cn2 x ∨ cn3 x, gender1)


----------------------
-- Pron

type Pron = NP

qPron :: ObjQuery -> Pron
qPron q = do
  np <- getNP q
  np

sheRefl_Pron :: Pron
sheRefl_Pron = qPron $ all' [isFemale, isSingular, isCoArgument]

heRefl_Pron :: Pron
heRefl_Pron = qPron $ all' [isMale, isSingular, isCoArgument]

he_Pron, she_Pron :: Pron
he_Pron = qPron $ all' [isMale, isSingular]
she_Pron = qPron $ all' [isFemale, isSingular]


it_Pron :: Pron
it_Pron = qPron $ all' [isNeutral, isSingular]

itRefl_Pron :: Pron
itRefl_Pron = qPron $ all' [isNeutral, isSingular, isCoArgument]

they_Pron :: Pron
they_Pron = qPron $ isPlural

someone_Pron :: Pron
someone_Pron = qPron $ all' [isSingular, isPerson]

maximallySloppyPron :: Pron
maximallySloppyPron = qPron $ const True

everyone_Pron :: Pron
everyone_Pron = return $ MkNP Unspecified every_Quant (mkPred "Person_N",Unknown)


-- his :: CN2 -> NP
-- his cn2 role = do
--   (isSloppy :: Bool) <- gets envSloppyFeatures -- FIXME: put this in Pron -> NP
--   poss (pron (\x -> isSloppy || (all' [isMale, isSingular] x))) cn2 role


---------------------------
-- Det

type Det = (Number,Quant)

detQuant :: Quant -> Number -> Det
detQuant q n = (n,q)

every_Det :: Det
every_Det = (Unspecified,every_Quant)

each_Det :: Det
each_Det = (Singular,every_Quant)

somePl_Det :: Det
somePl_Det = (Plural,indefArt)

several_Det :: (Number, Quant)
several_Det = (Plural,several_Quant)

exactly_Det :: Det
exactly_Det = (numPl,q) where
  q :: Quant
  q number@(Cardinal n) (cn',gender) role = do
      x <- getFresh
      modify (pushNP (Descriptor gender number role) (pureVar x number (cn',gender)))
      return (\vp' -> Quant (Exact n) Both x (cn' (Var x)) (vp' (Var x)))

anySg_Det :: Det
anySg_Det = each_Det

----------------------------
-- Comp

type Comp = VP

useComp :: VP -> Comp
useComp = id

-- | be a thing given by the CN
compCN :: CN -> Comp
compCN cn = do
  (cn',_gender) <- cn
  return cn'

compAP :: AP -> Comp
compAP ap = do
  a' <- ap
  return $ \x -> a' (const TRUE) x 

compNP :: NP -> Comp
compNP np = do
  np' <- interpNP np Other
  return $ \x -> np' $ \y -> mkRel2 "EQUAL" x y

compAdv :: Adv -> Comp
compAdv adv = do
  adv' <- adv
  return $ \x -> adv' (\y -> (Con "_BE_" `apps` [y])) x


---------------------------
-- V2

elliptic_VPSlash :: VPSlash
elliptic_VPSlash = do
  v2 <- gets vp2Env
  sloppily v2

---------------------------
-- VPS

type VPS = Dynamic (VP')

conjVPS2 :: Conj -> Temp -> Pol -> VP -> Temp -> Pol -> VP -> VPS
conjVPS2 conj _t1 pol1 vp1 _t2 pol2 vp2 = do
  vp1' <- vp1
  vp2' <- vp2
  return $ \x -> (apConj2 conj (pol1 (vp1' x)) (pol2 (vp2' x)))

---------------------------
-- VV

do_VV :: VV
do_VV = return $ \vp x -> vp x

going_to_VV :: VV
going_to_VV = do_VV -- ignoring tense

---------------------------
-- VP
type VP' = (Object -> Prop)
-- type VP' = (({-subjectClass-} Object -> Prop) -> Object -> Prop) -- in Coq
type VP = Dynamic VP'

progrVPa :: VP -> VP
progrVPa = id -- ignoring tense

complVV :: VV -> VP -> VP
complVV vv vp = vv <*> vp

doesTooVP :: VP
doesTooVP = do
  vp <- gets vpEnv
  sloppily vp

elliptic_VP :: VP
elliptic_VP = doesTooVP


-- | Passive
passV2s :: V2 -> VP
passV2s v2 = do
  v2' <- v2
  x <- getFresh
  return $ \subject -> Exists x true (v2' (Var x) subject) 

passVPSlash :: VPSlash -> VP
passVPSlash = passV2s

complSlash :: VPSlash -> NP -> VP
complSlash v2 directObject = do
  v2' <- v2
  do' <- interpNP directObject Other
  modify (pushVP (complSlash v2 directObject))
  return (\y -> do' $ \x -> (v2' x y))

adVVP :: Adv -> VP -> VP
adVVP adv vp = do
  adv' <- adv
  vp' <- vp
  return (adv' vp')

advVP :: VP -> Adv -> VP
advVP vp adv = do
  vp' <- vp
  adv' <- adv
  return (adv' vp')

useV :: V -> VP
useV v = do
  modify (pushVP (useV v))
  v

relVP :: RP->VP->RCl
relVP _ vp = vp

complVS :: VS -> S -> VP
complVS vs s = do
  vs' <- vs
  s' <- s
  return (vs' s')

complVSa :: VS -> S -> VP
complVSa = complVS -- FIXME: what is the difference from ComplVS? 

reflVP :: VPSlash -> VP
reflVP v2 =  do
  v2' <- v2
  return $ \subject -> v2' subject subject


----------------------------
-- VPSlash
type VPSlash = V2

slash2V3 :: V3 -> NP -> VPSlash
slash2V3 v np = do
  v' <- v
  np' <- interpNP np Other
  return $ \indirectObject subject -> np' $ \directObject -> v' indirectObject directObject subject

slash3V3 :: V3 -> NP -> VPSlash
slash3V3 v np = do
  v' <- v
  np' <- interpNP np Other
  return $ \directObject subjectClass -> np' $ \indirectObject -> v' indirectObject directObject subjectClass

slashV2S :: V2S -> S -> VPSlash
slashV2S v2s s = do
  v2s' <- v2s
  s' <- s
  return $ \directObject subject -> v2s' directObject s' subject

slashV2V :: V2V -> VP -> VPSlash
slashV2V v2v vp = do
  v2v' <- v2v
  vp' <- vp
  return $ \directObject subject -> v2v' directObject vp' subject

slashVV :: VV -> VPSlash -> VPSlash
slashVV vv v2 = do
  vv' <- vv
  v2' <- v2
  return $ \directObject subject -> vv' (\x -> v2' directObject x) subject


slashV2a :: V2 -> VPSlash
slashV2a = id


----------------------------
-- Cl

existNP :: NP -> Cl
existNP np = do
  np' <- interpNP np Other
  return $ (np' $ \_ -> TRUE)

predVP :: NP -> VP -> Cl
predVP np vp = do
  np' <- interpNP np Subject
  vp' <- vp
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the direct arguments.
  modify (pushS (predVP np vp))
  return (np' vp')

sloppily :: Dynamic a -> Dynamic a
sloppily = withState (\Env{..} -> Env{envSloppyFeatures = True,..})


soDoI :: NP -> Cl
soDoI np = predVP np doesTooVP

elliptic_Cl :: Cl
elliptic_Cl = do
  cl <- gets sEnv
  cl

---------------------
-- RCl

emptyRelSlash :: ClSlash -> RCl
emptyRelSlash = id

relSlash :: RP -> ClSlash -> RCl
relSlash _rpIgnored cl = cl

strandRelSlash :: RP -> ClSlash -> RCl
strandRelSlash _rp cl = cl


--------------------
-- ClSlash
slashVP :: NP -> VPSlash -> ClSlash
slashVP np vp = do
  np' <- interpNP np Other
  vp' <- vp
  return $ \object -> np' (\subject -> vp' object subject)



--------------------
-- Conj
data Conj where
  RightAssoc :: (Prop -> Prop -> Prop) -> Conj
  EitherOr :: Conj

and_Conj :: Conj
and_Conj = RightAssoc (∧)

comma_and_Conj :: Conj
comma_and_Conj = RightAssoc (∧)

if_comma_then_Conj :: Conj
if_comma_then_Conj = RightAssoc (-->)

apConj2 :: Conj -> Prop -> Prop -> Prop
apConj2 conj = case conj of
  RightAssoc c -> c
  EitherOr -> \p q -> (p ∧ not' q) ∨ (not' p ∧ q)

apConj3 :: Conj -> Prop -> Prop-> Prop-> Prop
apConj3 conj = case conj of
  RightAssoc c -> \p q r -> (p `c` q) `c` r
  EitherOr -> \p q r -> (p ∧ not' q ∧ not' r) ∨ (not' p ∧ q ∧ not' r) ∨ (not' p ∧ not' q ∧ r)


----------------------
-- RS

useRCl :: Temp->Pol->RCl->RS
useRCl temp pol r = do
  r' <- r
  return $ \x -> temp (pol (r' x))

--------------------
-- S

extAdvS :: Adv -> S -> S
extAdvS adv s = do
  adv' <- adv
  s' <- s
  return $ adv' (\_ -> s') (Con "IMPERSONAL")


useCl :: Temp -> Pol -> Cl -> S
useCl = \temp pol cl -> temp <$> (pol <$> cl)

conjS2 :: Conj -> S -> S -> S
conjS2 c s1 s2 = apConj2 c <$> s1 <*> s2

predVPS :: NP -> VPS -> S
predVPS np vp = do
  np' <- interpNP np Subject
  vp' <- vp
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the direct arguments.
  return (np' vp')

--------------------
-- Phr
type Phr =  Dynamic (Prop)

sentence :: S -> Phr
sentence = id

pSentence :: PConj -> S -> Phr
pSentence _ x = x

-------------------------
-- Quant

type Quant' = (Number -> CN' -> Role -> Dynamic NP')
type Quant = Quant'

possPron :: Pron -> Quant
possPron np number cn role = genNP np number cn role

no_Quant :: Quant
no_Quant num cn role = do
  q <- every_Quant num cn role
  return $ \vp' -> q (\x -> not' (vp' x))

every_Quant :: Quant
every_Quant = \number (cn',gender) role -> do
  x <- getFresh
  modify (pushNP (Descriptor gender number role) (pureVar x number (cn',gender)))
  return $ \vp' -> (Forall x (cn' (Var x)) (vp' (Var x)))

some_Quant :: Quant
some_Quant = \number (cn',gender) role -> do
  x <- getFresh
  modify (pushNP (Descriptor gender number role) (pureVar x number (cn',gender)))
  return (\vp' -> Exists x (cn' (Var x)) (vp' (Var x)))

most_Quant :: Quant
most_Quant number  (cn',gender) role = do
  x <- getFresh
  z <- getFresh
  modify (pushNP (Descriptor gender Plural role) (pureVar x number (cn',gender)))
  return $ \vp' -> MOST x (cn' (Var x)) (vp' (Var x)) ∧ Forall z ((cn' (Var z)) ∧ (vp' (Var z))) true

indefArt :: Quant
indefArt number (cn',gender) role = do
  x <- getFresh
  modify (pushNP (Descriptor gender number role) (pureVar x number (cn',gender)))
  modify (pushThing cn' x)
  return (\vp' -> Exists x (cn' (Var x)) (vp' (Var x)))

several_Quant :: Quant
several_Quant number (cn',gender) role = do
  x <- getFresh
  modify (pushNP (Descriptor gender number role) (pureVar x number (cn',gender)))
  modify (pushThing cn' x)
  return (\vp' -> SEVERAL x (cn' (Var x)) (vp' (Var x)))


-- | Definite which looks up in the environment.
defArt :: Quant
defArt number (cn',gender) role = do
  it <- getDefinite (cn',gender) 
  -- note that here we push the actual object (it seems that the strict reading is preferred in this case)
  _ <- pureNP it gender number role
  return $ \vp' -> vp' it


genNP :: NP -> Quant
genNP np _number (cn',_gender) _role = do
  them <- interpNP np Other -- only the direct arguments need to be referred by "self"
  x <- getFresh
  return (\vp' -> them $ \y -> Forall x (cn' (Var x) ∧ mkRel2 "HAVE" y (Var x)) (vp' (Var x)))
  -- FIXME: is  -- FIXME: is the above quantifier the right one?

-------------------------
-- Predet

most_of_Predet :: Predet
most_of_Predet (MkNP n _q cn) = MkNP n most_Quant cn

most_Predet :: Predet
most_Predet (MkNP n _q cn) = MkNP n most_Quant cn 

all_Predet :: Predet
all_Predet  (MkNP n _q cn) = MkNP n every_Quant cn

{-


sheNP :: NP
sheNP = pron (all' [isFemale, isSingular])

himNP :: NP
himNP = pron (all' [isMale, isSingular, isNotSubject])

herNP :: NP
herNP = pron (all' [isFemale, isSingular, isNotSubject])

heNP :: NP
heNP = pron (all' [isMale, isSingular])



themSingNP :: NP -- as in everyone owns their book 
themSingNP = pron (all' [isSingular, isNotSubject])

-- nthNP :: Int -> Role -> VP -> Env -> (Prop, Env)
-- nthNP n = \role vp ρ -> (getNthNP n ρ) role vp ρ

his :: CN2 -> NP
his cn2 role = do
  (isSloppy :: Bool) <- gets envSloppyFeatures
  poss (pron (\x -> isSloppy || (all' [isMale, isSingular] x))) cn2 role


-- TODO: remove
-- | Definite which cannot look up in the environment (mostly because
-- our environment does not contain the necessary information)
the' :: CN -> NP
the' cn _role = do
  (cn',_g,_n) <- cn
  return $ \vp -> vp (The cn')


(<==)  :: Effect -> Effect -> Effect
a <== b = do
  a' <- a
  b' <- b
  return (b' --> a')



negation :: Effect -> Effect
negation x = not' <$> x

-- pushes itself in the env for reference


pureCN2 :: (Object -> Type) -> Gender -> Number -> CN2
pureCN2 v gender number = do
  modify (pushCN2 (pureCN2 v gender number))
  return (v,gender,number)


pureEval :: Effect -> Exp
pureEval = extendAllScopes . repairFields . _TRUE

eval :: Effect -> IO ()
eval = print . pureEval



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



thatOf :: NP -> NP
thatOf x role = do
  cn2 <- gets getCN2
  the (cn2 `_of` x) role

oneToo :: NP
oneToo role = aDet one role


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



-- CN2 example%


orS :: S -> S -> S
orS s1 s2 = (∨) <$> s1 <*> s2


-}
evalDbg :: Effect -> IO ()
evalDbg e = do
  let p = _TRUE e
  -- let r = repairFields p
  --     q = extendAllScopes r
  print p
  -- print r
  -- print q
  -- print (freeVars q)

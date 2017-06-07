{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
import Prelude hiding (pred)
type Object = String
type Prop = String


data Gender where
   Male :: Gender
   Female :: Gender
   Neutral :: Gender
   Unknown :: Gender
  deriving (Eq,Show)

data Number where
  Singular :: Number
  Plural :: Number
  deriving (Eq,Show)

data Role where
  Subject :: Role
  Other :: Role
  deriving (Eq,Show)

first :: (t2 -> t1) -> (t2, t) -> (t1, t)
first f (x,y) = (f x,y)
second :: forall t t1 t2. (t2 -> t1) -> (t, t2) -> (t, t1)
second f (x,y) = (x,f y)
data Descriptor = Descriptor {dGender :: Gender
                             ,dNumber :: Number
                             ,dRole :: Role} deriving Show

type ObjQuery = Descriptor -> Bool
type ObjEnv = [(Descriptor,NP)]
type NounEnv = [CN]

clearRole :: Env -> Env
clearRole Env{..} = Env{objEnv = map (first (\d -> d {dRole = Other})) objEnv,..}

type VPEnv = VP
-- Just remember the last VP; could be more fine-grained because we have "does", "is", "has" as placehodlers in English.

data Env = Env {vpEnv :: VPEnv,
                objEnv :: ObjEnv,
                cnEnv :: NounEnv} deriving Show

type Effect = Env -> (Prop, Env)

mkPred :: String -> Object -> Prop
mkPred p x = p ++ "(" ++ x ++ ")"

mkRel2 :: String -> Object -> Object -> Prop
mkRel2 p x y = p ++ "(" ++ x ++ "," ++ y ++ ")"

assumedVP :: VPEnv
assumedVP x ρ = ("assumedVP " ++ x, ρ) 

assumedCN :: CN
assumedCN x ρ = (mkPred "assumedCN" x, ρ)
assumed :: Env
assumed = Env assumedVP [] [assumedCN]

_TRUE :: Effect -> Prop
_TRUE = \x -> let (x',_) = x assumed in x'

_ENV :: Effect -> Env
_ENV = \x -> snd (x assumed)

type S = Effect
type VP = Object -> Effect
type CN = Object -> Effect
type CN2 = Object -> CN
type NP = Role -> VP -> Effect

instance Show VP where
  show vp = "λw. " ++ fst (vp "w" assumed)
instance Show NP where
  show np = fst (np Other (\x rho -> (x,rho)) assumed)

isNeutral :: Descriptor -> Bool
isNeutral = (== Neutral) . dGender

isMale :: Descriptor -> Bool
isMale = (== Male) . dGender

isFemale :: Descriptor -> Bool
isFemale =  (== Female) . dGender

isSingular :: Descriptor -> Bool
isSingular = (== Singular) . dNumber

isPlural :: Descriptor -> Bool
isPlural = (== Plural) . dNumber

isNotSubject :: Descriptor -> Bool
isNotSubject = (/= Subject) . dRole

pushNP :: Descriptor -> NP -> Env -> Env
pushNP d obj Env{..} = Env{objEnv = (d,obj):objEnv,..}

pushVP :: VP -> Env -> Env
pushVP vp Env{..} = Env{vpEnv=vp,..}

pushCN :: CN -> Env -> Env
pushCN cn Env{..} = Env{cnEnv=cn:cnEnv,..}

getCN :: Env -> CN
getCN Env{cnEnv=cn:_} = cn
getCN _ = error "panic: no cn in env"

getNP :: Env -> ObjQuery -> NP
getNP Env{objEnv=[]} _ = \_ vp -> vp "assumedObj"
getNP Env{objEnv=((d,o):os),..} q = if q d then o else getNP Env{objEnv=os,..} q

-- Some debugging function
getNthNP :: Int -> Env ->  NP
getNthNP _ Env{objEnv=[]} =  \_ vp -> vp "assumedObj"
getNthNP 0 Env{objEnv=((_,o):_),..} = o
getNthNP n Env{objEnv=((d,o):os),..} = getNthNP (n-1) Env{objEnv=((d,o):os),..}

purePN ::  Object -> Gender -> NP
purePN o dGender dRole vp ρ = vp o (pushNP (Descriptor{..} ) (purePN o dGender) ρ)
  where dNumber = Singular

maryNP :: NP
maryNP = purePN "MARY" Female

johnNP :: NP
johnNP = purePN "JOHN" Male

billNP :: NP
billNP = purePN "BILL" Male

sheNP :: NP
sheNP = \role vp ρ -> (getNP ρ (all' [isFemale, isSingular])) role vp ρ

himNP :: NP
himNP = \role vp ρ -> (getNP ρ (all' [isMale, isSingular, isNotSubject])) role vp ρ

heNP :: NP
heNP = \role vp ρ -> (getNP ρ (all' [isMale, isSingular])) role vp ρ

himSelfNP :: NP
himSelfNP = heNP

theySingNP :: NP -- as in everyone owns their book 
theySingNP = \role vp ρ -> (getNP ρ isSingular) role vp ρ

themSingNP :: NP -- as in everyone owns their book 
themSingNP = \role vp ρ -> (getNP ρ (all' [isSingular, isNotSubject])) role vp ρ

itNP :: Role -> VP -> Env -> (Prop, Env)
itNP = \role vp ρ -> (getNP ρ (all' [isNeutral, isSingular])) role vp ρ

nthNP :: Int -> Role -> VP -> Env -> (Prop, Env)
nthNP n = \role vp ρ -> (getNthNP n ρ) role vp ρ

theyPlNP :: NP -- as in everyone owns their book 
theyPlNP = \role vp ρ -> (getNP ρ isPlural) role vp ρ

his :: CN2 -> NP
his cn2 role vp = himSelfNP role $ \x -> the (cn2 x) Other vp

the :: CN -> NP
the cn role vp rho = second (pushNP (Descriptor Unknown Singular role) (the cn)) (vp (_THE $ \x -> fst (cn x rho)) rho)
-- FIXME: the CN won't update the environment in this situation.
-- FIXME: fetch the gender/number from the CN
_THE :: (Object -> Prop) -> Prop
_THE f = "(THE y. " ++ f "y" ++")"


all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

lift2 :: (Prop -> Prop -> Prop) -> Effect -> Effect -> Effect
lift2 = \op x y rho1 -> let (x' , rho2) = x rho1 in
                      let (y' , rho3) = y rho2 in
                       (op x' y' , rho3)

lift1 :: (Prop -> Prop) -> Effect -> Effect
lift1 op x rho0 = let (x',rho1) = x rho0 in (op x', rho1)

(<==) :: Effect -> Effect -> Effect
a <== b = lift2 (\x y -> y --> x) a b
(==>) :: Effect -> Effect -> Effect
(==>) = lift2 (-->)
(-->), (~~>) :: Prop -> Prop -> Prop
x --> y = x ++ " → " ++ y
x ~~> y = x ++ " ∼> " ++ y
not' :: Effect -> Effect
not' = lift1 (mkPred "NOT")


(###) :: Effect -> Effect -> Effect
(###) = (∧)

(∧) :: Effect -> Effect -> Effect
a ∧ b = lift2 (\x y -> x ++" ∧ "++ y) a b


_LEAVE_V :: Object -> Prop
_LEAVE_V = mkPred "LEAVES"


pureVP :: (Object -> Prop) -> VP
pureVP = \v x rho -> (v x, pushVP (pureVP v) rho)
-- pushes itself in the env for reference

pureCN :: (Object -> Prop) -> CN
pureCN cn = \x rho -> (cn x, pushCN (pureCN cn) rho)
-- CN leaves the env as is. The quantifiers may update it.

pureCN2 :: (Object -> Object -> Prop) -> CN2
pureCN2 = \v x y rho -> (v x y, rho)
-- CN2 leaves the env as is. The quantifiers may update it.

leavesVP :: VP
leavesVP = pureVP _LEAVE_V

isTiredVP :: VP
isTiredVP = pureVP (mkPred "IS_TIRED")

-- (* EXAMPLE:: john leaves if he is tired *)
example0 :: Prop
example0 = _TRUE ((johnNP ! leavesVP) <== (heNP ! isTiredVP))

{-> putStrLn example0

IS_TIRED(JOHN) → LEAVES(JOHN)
-}

doesTooVP :: VP
doesTooVP = \x env -> let Env{..} = env in vpEnv x env

-- (* EXAMPLE:: john leaves if mary does [too] *)
example1 :: Prop
example1 = _TRUE ((johnNP ! leavesVP) <== (maryNP ! doesTooVP))

{-> putStrLn example1

LEAVES(MARY) → LEAVES(JOHN)
-}

_ADMIT_V :: Prop -> Object -> Prop
_ADMIT_V = mkRel2 "ADMIT"

admitVP :: Effect -> VP
admitVP = \p x rho0 -> let (p',rho1) = p rho0 in
                   (_ADMIT_V p' x, pushVP (admitVP p) rho1)

_PERSON :: Object -> Prop
_PERSON = mkPred "PERSON"

_FORALL :: (Object -> Prop) -> Prop
_FORALL f = "(∀ x. " ++ f "x" ++")"

_EXISTS :: (Object -> Prop) -> Prop
_EXISTS f = "(∃ z. " ++ f "z" ++")"

pureObj :: Object -> NP
pureObj x _role vp ρ = vp x ρ

everyone :: NP
everyone = every (pureCN (mkPred "PERSON"))

every :: CN -> NP
every cn = \role vp ρ -> (_FORALL $ \x -> fst ((cn x ==> vp x) (pushNP (Descriptor Male Singular Subject) (pureObj x) ρ)),
                   pushVP vp
                    (pushNP (Descriptor Unknown Plural role) (every (cn `that` vp)) -- "e-type" referent
                      (envModOf (vp "<unbound>") -- the things that we talk about in the CN/VP can be referred to anyway! (see example8)
                       ρ)))

-- The referents pushed within the FORALL scope cannot escape to the top level

-- the bound variable is still referrable within the scope. It is pushed there
-- (with the appropriate descriptor)

some :: CN -> NP
some cn = \role vp ρ -> (_EXISTS $ \x -> fst ((cn x ∧ vp x) (pushNP (Descriptor Male Singular Subject) (pureObj x) ρ)),
                   pushVP vp
                    (pushNP (Descriptor Unknown Plural role) (the (cn `that` vp)) -- "e-type" referent {- this one can done better because existential quantifiers are "positive" -}
                      (envModOf (vp "<unbound>") -- {- same: can use positiveness -}
                       ρ)))

{- in fact, it seems that all quantifiers have an existential aspect to them. -}

few :: CN -> NP
few cn = \_role vp ρ -> (_FORALL $ \x -> fst (lift2 (~~>) (cn x) (not' (vp x) ) (pushNP (Descriptor Male Singular Subject) (pureObj x) ρ)),
                   pushVP vp
                    (pushNP (Descriptor Unknown Plural Other) (every (cn `that` vp)) -- "e-type" referent
                      (envModOf (vp "<unbound>") -- the things that we talk about in the CN/VP can be referred to anyway! (see example8)
                       ρ)))

envModOf :: Effect -> Env -> Env
envModOf f rho = snd (f rho)

effect :: (Env -> Env) -> Effect -> Effect
effect f g x = second f (g x)

(!) :: NP -> VP -> Effect
(np ! vp) rho = second clearRole ((np Subject vp) rho)
-- Once the sentence is complete, accusative pronouns can refer to the subject. (see example9)


-- EXAMPLE:: everyone admits that they are tired
example2 :: Prop
example2 = _TRUE (everyone ! (admitVP (theySingNP ! isTiredVP)))

{-> putStrLn example2

(∀ x. PERSON(x) → ADMIT(IS_TIRED(x),x))
-}


-- EXAMPLE:: everyone admits that they are tired Mary does too
example3 :: Prop
example3 = _TRUE ((everyone ! (admitVP (theySingNP ! isTiredVP))) ### (maryNP ! doesTooVP))

{-> putStrLn example3

(∀ x. PERSON(x) → ADMIT(IS_TIRED(x),x)) ∧ ADMIT(IS_TIRED(MARY),MARY)
-}


_MARRIED :: [Char] -> [Char] -> [Char]
_MARRIED = mkRel2 "MARRIED"

married :: CN2
married = pureCN2 _MARRIED

hisSpouseNP :: NP
hisSpouseNP = his married

lovesVP :: NP -> VP
lovesVP directObject subject = directObject Other $ \x -> pureVP (mkRel2 "LOVE" x) subject


-- (* EXAMPLE:: john leaves his wife. Bill does too.  *)
example4 :: Prop
example4 = _TRUE (johnNP ! (lovesVP hisSpouseNP) ### (billNP ! doesTooVP) )

-- Note what happens here.
-- lovesVP calls the directObject, ("hisSpouseNP"), which has the effect of resolving the anaphora.
-- Only then, 'pureVP' is called and the vp is pushed onto the environment
{-> putStrLn example4

LOVE((THE x. MARRIED(JOHN,x)),JOHN) ∧ LOVE((THE x. MARRIED(JOHN,x)),BILL)
-}


pureV2' :: (Object -> Object -> Prop) -> NP -> VP
pureV2' v2 directObject subject = directObject Other
  (\x rho -> (v2 x subject,pushVP (pureV2' v2 directObject) rho))

lovesVP' :: NP -> VP
lovesVP' = pureV2' (mkRel2 "LOVE")

-- (* EXAMPLE:: john leaves his wife. Bill does too. [second reading] *)
example5b :: Prop
example5b = _TRUE (johnNP ! (lovesVP' hisSpouseNP) ### (billNP ! doesTooVP) )
-- With the above version of "love", the direct object is re-evaluated after it is being referred to.

{-> putStrLn example5b

LOVE((THE y. MARRIED(JOHN,y)),JOHN) ∧ LOVE((THE y. MARRIED(BILL,y)),BILL)
-}


-- (* EXAMPLE:: john leaves his spouse. Mary does too. *)
example6 :: Prop
example6 = _TRUE (johnNP ! (lovesVP' hisSpouseNP) ### (maryNP ! doesTooVP) )
-- Because "his" is looking for a masculine object, the re-evaluation
-- in the "does too" points back to John anyway.

{-> putStrLn example6

LOVE((THE x. MARRIED(JOHN,x)),JOHN) ∧ LOVE((THE x. MARRIED(JOHN,x)),MARY)
-}


that :: CN -> VP -> CN
that cn vp x = cn x ∧ vp x



congressmen :: CN
congressmen = pureCN (mkPred "CONGRESSMAN")

example7 :: Prop
example7 = _TRUE ((few congressmen ! (lovesVP billNP)) ### (theyPlNP ! isTiredVP))


-- (* EXAMPLE:: Few congressmen love bill. They are tired. *)
{-> putStrLn example7

(∀ x. CONGRESSMAN(x) ∼> NOT(LOVE(BILL,x))) ∧ (∀ x. CONGRESSMAN(x) ∧ LOVE(BILL,x) → IS_TIRED(x))
-}


example8 :: Prop
example8 = _TRUE ((few congressmen ! (lovesVP billNP)) ### (heNP ! isTiredVP))

-- (* EXAMPLE:: Few congressmen love bill. He is tired. *) -- The e-type referent is plural.
{-> putStrLn example8

(∀ x. CONGRESSMAN(x) ∼> LOVE(BILL,x)) ∧ IS_TIRED(BILL)
-}


example9 :: Prop
example9 = _TRUE ((johnNP ! isTiredVP) ### (billNP ! (lovesVP himNP)))
-- John is tired. Bill loves him. -- (Bill loves John, not himself.)
{-> putStrLn example9

IS_TIRED(JOHN) ∧ LOVE(JOHN,BILL)
-}

man :: CN
man = pureCN (mkPred "MAN")

beatV2 :: NP -> VP
beatV2 = pureV2' (mkRel2 "BEAT")

example10 :: Prop
example10 = _TRUE ((few (man `that` (lovesVP hisSpouseNP))) ! (beatV2 themSingNP))

-- (* EXAMPLE:: Few men that love their wife beat them.

{-> putStrLn example10

(∀ x. MAN(x) ∧ LOVE((THE y. MARRIED(x,y)),x) ∼> NOT(BEAT((THE y. MARRIED(x,y)),x)))
-}

donkey :: CN
donkey = pureCN (mkPred "DONKEY")

own :: NP -> VP
own = pureV2' (mkRel2 "OWN")

aDet :: CN -> NP
aDet cn = \role vp ρ -> (_EXISTS $ \x -> fst ((cn x ∧ vp x) ρ),
                          {- note that this isn't a quantifier, 'x' is not accessible in the CN-}
                         pushNP (Descriptor Neutral Singular role) (pureObj "Z")
                         {- FIXME: fetch gender from CN -}
                         (snd ((cn "Z" ∧ vp "Z") ρ))
                         )

oneToo :: NP
oneToo = \role vp ρ -> aDet (getCN ρ) role vp ρ


example11a = (((aDet donkey) ! isTiredVP) ### (itNP ! leavesVP))
eval :: Effect -> IO ()
eval = putStrLn . _TRUE
-- A donkey is tired. It leaves.

{-> eval example11a

(∃ z. DONKEY(z) ∧ IS_TIRED(z)) ∧ LEAVES(Z)
-}

example11b :: Effect
example11b = (((aDet donkey) ! leavesVP) <== (itNP ! isTiredVP))
-- A donkey leaves if it is tired.
{-> eval example11b

IS_TIRED(Z) → (∃ z. DONKEY(z) ∧ LEAVES(z))
-}
-- The proper interpretation is : ∃z. DONKEY(z) ∧ IS_TIRED(z) ∧ LEAVES(z)
-- Seemingly the existential quantifiers gets "pulled" up as far as possible.

example11c :: Effect
example11c = (aDet (man `that` own (aDet donkey)) ! (beatV2 itNP))
-- A man that owns a donkey beats it.

{-> eval example11c

(∃ z. MAN(z) ∧ (∃ z. DONKEY(z) ∧ OWN(z,z)) ∧ BEAT(Z,z))
-}

example11d :: Effect
example11d = ((billNP ! (own (aDet donkey))) ### (heNP ! (beatV2 itNP)))
-- Bill owns a donkey. He beats it.

{-> eval example11d

(∃ z. DONKEY(z) ∧ OWN(z,BILL)) ∧ BEAT(Z,BILL)
-}

example11 :: Effect
example11 = (every (man `that` own (aDet donkey)) ! (beatV2 itNP))
-- Every man that owns a donkey beat it.

{-> eval example11

(∀ x. MAN(x) ∧ (∃ z. DONKEY(z) ∧ OWN(z,x)) → BEAT(Z,x))
-}

example12 :: Effect
example12 = the (man `that` own (aDet donkey)) ! (beatV2 (nthNP 0))
-- The man that own a donkey beat it.

{-> eval example12

BEAT(assumedObj,(THE y. MAN(y) ∧ (∃ z. DONKEY(z) ∧ OWN(z,y))))
-}

example13 :: Effect
example13 = billNP ! (own (aDet (donkey `that` (\x -> heNP ! (beatV2 (pureObj x))))))
-- Bill owns a donkey that he beats.


{-> eval example13

(∃ z. DONKEY(z) ∧ BEAT(z,BILL) ∧ OWN(z,BILL))
-}


example14 :: Effect
example14 = (billNP ! own (aDet donkey)) ### (johnNP ! (own oneToo))

{-> eval example14

(∃ z. DONKEY(z) ∧ OWN(z,BILL)) ∧ (∃ z. DONKEY(z) ∧ OWN(z,JOHN))
-}

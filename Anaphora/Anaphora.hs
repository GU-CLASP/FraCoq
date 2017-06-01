{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
import Prelude hiding (pred)
type Object = String
type Prop = String

_MARY, _JOHN, _BILL :: Object
_MARY = "MARY"
_JOHN = "JOHN"
_BILL = "BILL"

data Gender where
   Male :: Gender
   Female :: Gender
   Unknown :: Gender

data Number where
  Singular :: Number
  Plural :: Number
  deriving (Eq,Show)

  
type Descriptor = (Gender,Number)

type ObjQuery = Descriptor -> Bool
type ObjEnv = ObjQuery -> NP

type VPEnv = VP
-- Just remember the last VP; could be more fine-grained because we have "does", "is", "has" as placehodlers in English.

data Env = Env {vpEnv :: VPEnv,
                objEnv :: ObjEnv}

type Effect = Env -> (Prop, Env)

mkPred p x = p ++ "(" ++ x ++ ")"
mkRel2 p x y = p ++ "(" ++ x ++ "," ++ y ++ ")"

assumedObj :: ObjEnv
assumedObj _query vp rho = vp "assumedObj" rho

assumedVP :: VPEnv
assumedVP x ρ = ("assumedVP " ++ x, ρ) 

assumed :: Env
assumed = Env assumedVP assumedObj


_TRUE :: Effect -> Prop
_TRUE = \x -> let (x',_) = x assumed in x'


type S = Effect
type VP = Object -> Effect
type CN = Object -> Effect
type NP = VP -> Effect

isMale :: Descriptor -> Bool
isMale = \(x,_) -> case x of
  Male -> True
  _ -> False

isFemale :: Descriptor -> Bool
isFemale = \(x,_) -> case x of
  Female -> True
  _ -> False

isSingular :: Descriptor -> Bool
isSingular = (==Singular) . snd

isPlural :: Descriptor -> Bool
isPlural = (== Plural) . snd


pushNP :: Descriptor -> NP -> Env -> Env
pushNP = \objDescr obj env -> let Env{..} = env in
     Env vpEnv $ \pred ->
     case pred objDescr of
       True -> obj
       False -> objEnv pred

pushVP :: VP -> Env -> Env
pushVP = \vp env -> let Env{..} = env in Env vp objEnv

getNP :: Env -> ObjQuery -> NP
getNP = \env descr -> let Env{..} = env in objEnv descr


maryNP :: NP
maryNP = \vp ρ -> vp _MARY (pushNP (Female,Singular) maryNP ρ)

johnNP :: NP
johnNP = \vp ρ -> vp _JOHN (pushNP (Male,Singular) johnNP ρ)

billNP :: NP
billNP = \vp ρ -> vp _BILL (pushNP (Male,Singular) billNP ρ)

sheNP :: NP
sheNP = \vp ρ -> (getNP ρ ((&&) <$> isFemale <*> isSingular)) vp ρ

heNP :: NP
heNP = \vp ρ -> (getNP ρ ((&&) <$> isMale <*> isSingular)) vp ρ

theySingNP :: NP -- as in everyone owns their book 
theySingNP = \vp ρ -> (getNP ρ isSingular) vp ρ

theyPlNP :: NP -- as in everyone owns their book 
theyPlNP = \vp ρ -> (getNP ρ isPlural) vp ρ


lift2 :: (Prop -> Prop -> Prop) -> Effect -> Effect -> Effect
lift2 = \op x y rho1 -> let (x' , rho2) = x rho1 in
                      let (y' , rho3) = y rho2 in
                       (op x' y' , rho3)


(<==) :: Effect -> Effect -> Effect
a <== b = lift2 (\x y -> y --> x) a b
(==>) :: Effect -> Effect -> Effect
(==>) = flip (<==)
(-->) :: Prop -> Prop -> Prop
x --> y = x ++ " → " ++ y
x ~~> y = x ++ " ∼> " ++ y


(###) :: Effect -> Effect -> Effect
a ### b = lift2 (\x y -> x ++" ∧ "++ y) a b


_LEAVE_V :: Object -> Prop
_LEAVE_V = mkPred "LEAVES"


pureVP :: (Object -> Prop) -> VP
pureVP = \v x rho -> (v x, pushVP (pureVP v) rho)
-- pushes itself in the env for reference

pureCN :: (Object -> Prop) -> CN
pureCN = \v x rho -> (v x, rho)
-- CN leave the env as is. The quantifiers may update it.

leavesVP :: VP
leavesVP = pureVP _LEAVE_V

_IS_TIRED :: Object -> Prop
_IS_TIRED = mkPred "IS_TIRED"
isTiredVP :: VP
isTiredVP = pureVP _IS_TIRED

-- (* EXAMPLE:: john leaves if he is tired *)
example0 :: Prop
example0 = _TRUE ((johnNP leavesVP) <== (heNP isTiredVP))

{-> example0

"IS TIRED JOHN->LEAVES JOHN"
-}

doesTooVP :: VP
doesTooVP = \x env -> let Env{..} = env in vpEnv x env

-- (* EXAMPLE:: john leaves if mary does [too] *)

example1 :: Prop
example1 = _TRUE ((johnNP leavesVP) <== (maryNP doesTooVP))

{-> example1

"LEAVES MARY -> LEAVES JOHN"
-}

_ADMIT_V :: Prop -> Object -> Prop
_ADMIT_V p x = "ADMIT(" ++ p ++ "," ++ x ++")"

admitVP :: Effect -> VP
admitVP = \p x rho0 -> let (p',rho1) = p rho0 in
                   (_ADMIT_V p' x, pushVP (admitVP p) rho1)

_PERSON :: Object -> Prop
_PERSON = mkPred "PERSON"

_FORALL :: (Object -> Prop) -> Prop
_FORALL f = "(∀ x. " ++ f "x" ++")"

_THE :: (Object -> Prop) -> Prop
_THE f = "(THE x. " ++ f "x" ++")"

pureObj :: Object -> NP
pureObj x vp ρ = vp x ρ
everyOne :: NP
everyOne = \vp ρ -> (_FORALL $ \x -> _PERSON x --> fst (vp x (pushNP (Unknown,Singular) (pureObj x) ρ)),
                      pushVP vp ρ)

-- EXAMPLE:: everyone admits that they are tired
example2 :: Prop
example2 = _TRUE (everyOne (admitVP (theySingNP isTiredVP)))

{-> putStrLn example2

(∀ x. PERSON(x) → ADMIT(IS_TIRED(x),x))
-}


-- EXAMPLE:: everyone admits that they are tired Mary does too
example3 :: Prop
example3 = _TRUE ((everyOne (admitVP (theySingNP isTiredVP))) ### (maryNP doesTooVP))

{-> putStrLn example3

(∀ x. PERSON(x) → ADMIT(IS_TIRED(x),x)) ∧ ADMIT(IS_TIRED(MARY),MARY)
-}


_MARRIED :: [Char] -> [Char] -> [Char]
_MARRIED = mkRel2 "MARRIED"

hisSpouseNP :: NP
hisSpouseNP vp = heNP $ \x rho -> vp (_THE (\y -> _MARRIED x y)) rho

lovesVP :: NP -> VP
lovesVP directObject subject = directObject $ \x -> pureVP (mkRel2 "LOVE" x) subject


example4 :: Prop
example4 = _TRUE (johnNP (lovesVP hisSpouseNP) ### (billNP doesTooVP) )

-- Note what happens here.
-- lovesVP calls the directObject, ("hisSpouseNP"), which has the effect of resolving the anaphora.
-- Only then, 'pureVP' is called and the vp is pushed onto the environment
{-> putStrLn example4

LOVE((THE x. MARRIED(JOHN,x)),JOHN)/\LOVE((THE x. MARRIED(JOHN,x)),BILL)
-}


lovesVP'' :: NP -> VP
lovesVP'' directObject subject = directObject (\x rho ->
                                                (mkRel2 "LOVE" x subject,pushVP (lovesVP'' directObject) rho))

example5b :: Prop
example5b = _TRUE (johnNP (lovesVP'' hisSpouseNP) ### (billNP doesTooVP) )
-- With the above version of "love", the direct object is re-evaluated after it is being referred to.

{-> putStrLn example5b

LOVE((THE x. MARRIED(JOHN,x)),JOHN) ∧ LOVE((THE x. MARRIED(BILL,x)),BILL)
-}


example6 :: Prop
example6 = _TRUE (johnNP (lovesVP'' hisSpouseNP) ### (maryNP doesTooVP) )
-- Because "his" is looking for a masculine object, the re-evaluation
-- in the "does too" points back to John anyway.

{-> putStrLn example6

LOVE((THE x. MARRIED(JOHN,x)),JOHN) ∧ LOVE((THE x. MARRIED(JOHN,x)),MARY)
-}


that :: CN -> VP -> CN
that cn vp x = cn x ### vp x

the :: CN -> NP
the cn vp rho = vp (_THE $ \x -> fst (cn x rho)) rho
-- FIXME: the CN won't update the environment in this situation.

few :: CN -> NP
few cn = \vp ρ -> (_FORALL $ \x -> fst (lift2 (~~>) (cn x) (vp x) ρ),
                   pushVP vp
                    (pushNP (Unknown,Plural) (the (cn `that` vp)) -- "e-type" referent
                      (envModOf (vp "<unbound>") -- the things that we talk about in the CN/VP can be referred to anyway! (see example8)
                       ρ)))

envModOf :: Effect -> Env -> Env
envModOf f rho = snd (f rho)

congressmen = pureCN (mkPred "CONGRESSMAN")
admireKennedy :: VP
admireKennedy = pureVP (mkPred "ADMIRE_K")

example7 :: Prop
example7 = _TRUE (few congressmen (lovesVP billNP) ### theyPlNP isTiredVP)


{-> putStrLn example7

(∀ x. CONGRESSMAN(x) ∼> LOVE(BILL,x)) ∧ IS_TIRED((THE x. CONGRESSMAN(x) ∧ LOVE(BILL,x)))
-}


example8 :: Prop
example8 = _TRUE (few congressmen (lovesVP billNP) ### heNP isTiredVP)

{-> putStrLn example8

(∀ x. CONGRESSMAN(x) ∼> LOVE(BILL,x)) ∧ IS_TIRED(BILL)
-}

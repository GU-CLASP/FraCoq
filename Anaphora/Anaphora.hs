{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
import Prelude hiding (pred)
type Object = String
type Prop = String

_MARY, _JOHN :: Object
_MARY = "MARY"
_JOHN = "JOHN"
_BILL = "BILL"

data Gender where
   Male :: Gender
   Female :: Gender
   Unknown :: Gender

type Descriptor = Gender

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
type NP = VP -> Effect

isMale :: Gender -> Bool
isMale = \x -> case x of
  Male -> True
  _ -> False

isFemale :: Gender -> Bool
isFemale = \x -> case x of
  Female -> True
  _ -> False


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
maryNP = \vp ρ -> vp _MARY (pushNP Female maryNP ρ)

johnNP :: NP
johnNP = \vp ρ -> vp _JOHN (pushNP Male johnNP ρ)

billNP :: NP
billNP = \vp ρ -> vp _BILL (pushNP Male billNP ρ)

sheNP :: NP
sheNP = \vp ρ -> (getNP ρ isFemale) vp ρ

heNP :: NP
heNP = \vp ρ -> (getNP ρ isMale) vp ρ

theySingNP :: NP -- as in everyone owns their book 
theySingNP = \vp ρ -> (getNP ρ (\_ -> True)) vp ρ


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

(###) :: Effect -> Effect -> Effect
a ### b = lift2 (\x y -> x ++" ∧ "++ y) a b


_LEAVE_V :: Object -> Prop
_LEAVE_V = mkPred "LEAVES"


pureVP :: (Object -> Prop) -> VP
pureVP = \v x rho -> (v x, pushVP (pureVP v) rho)
-- pushes itself in the env for reference

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
_CONGRESSMAN :: Object -> Prop
_CONGRESSMAN = mkPred "CONGRESSMAN"
_ADMIRE_KENNEDY :: Object -> Prop
_ADMIRE_KENNEDY = mkPred "ADMIRE_K"

_FORALL :: (Object -> Prop) -> Prop
_FORALL f = "(∀ x. " ++ f "x" ++")"

_THE :: (Object -> Prop) -> Prop
_THE f = "(THE x. " ++ f "x" ++")"

pureObj :: Object -> NP
pureObj x vp ρ = vp x ρ
everyOne :: NP
everyOne = \vp ρ -> (_FORALL $ \x -> _PERSON x --> fst (vp x (pushNP Unknown (pureObj x) ρ)),
                      pushVP vp ρ)

-- EXAMPLE:: everyone admits that they are tired
example2 :: Prop
example2 = _TRUE (everyOne (admitVP (theySingNP isTiredVP)))

{-> example2


<interactive>:1621:1: error: Variable not in scope: example2
-}


-- EXAMPLE:: everyone admits that they are tired Mary does too
example3 :: Prop
example3 = _TRUE ((everyOne (admitVP (theySingNP isTiredVP))) ### (maryNP doesTooVP))

{-> putStrLn example3

(∀ x. PERSON x -> ADMIT(IS TIRED x,x))/\ADMIT(IS TIRED MARY,MARY)
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


lovesVP' :: NP -> VP
lovesVP' directObject subject rho = (fst (directObject (\y rho'  -> (mkRel2 "LOVE" y subject,rho')) rho),
                                      pushVP (lovesVP' directObject) rho)

example5 :: Prop
example5 = _TRUE (johnNP (lovesVP' hisSpouseNP) ### (billNP doesTooVP) )
-- With the above version of "love", the direct object is re-evaluated after it is being referred to.
{-> putStrLn example5

LOVE((THE x. MARRIED(JOHN,x)),JOHN)/\LOVE((THE x. MARRIED(BILL,x)),BILL)
-}


example6 :: Prop
example6 = _TRUE (johnNP (lovesVP' hisSpouseNP) ### (maryNP doesTooVP) )
-- Because "his" is looking for a masculine object, the re-evaluation
-- in the "does too" points back to John anyway.
{-> putStrLn example6

LOVE((THE x. MARRIED(JOHN,x)),JOHN) ∧ LOVE((THE x. MARRIED(JOHN,x)),MARY)
-}

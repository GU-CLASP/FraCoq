{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
import Prelude hiding (pred)
import Data.List (intercalate, partition)
import Control.Monad.State
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

data Env = Env {vpEnv :: VPEnv
               ,objEnv :: ObjEnv
               ,cnEnv :: NounEnv
               ,freshVars :: [String]} deriving Show

allVars :: [String]
allVars = map (:[]) ['a'..'z'] ++ cycle (map (:[]) ['α'..'ω'])

type Disc a = State Env a
type Effect = Disc Row
-- Env -> (Prop, Env)

type Row = [(String,String)]
mkRec :: Row -> Prop
-- mkRec row = "[" ++ intercalate " ; " ++ map showField row ++ "]"
mkRec row = intercalate " × " (map showField row)
  where showField ("_",p) = p
        showField (field,typ) = "(" ++ field ++ " : " ++ typ  ++ ")"

mkPred :: String -> Object -> Prop
mkPred p x = p ++ "(" ++ x ++ ")"

mkRel2 :: String -> Object -> Object -> Prop
mkRel2 p x y = p ++ "(" ++ x ++ "," ++ y ++ ")"

assumedPred :: String -> Object -> Effect
assumedPred predName x = do
  f <- getFresh
  return [(f,mkPred predName x)]

assumedVP :: VPEnv
assumedVP = assumedPred "assumedVP"

assumedCN :: CN
assumedCN = (assumedPred "assumedCN",Unknown,Singular)

assumed :: Env
assumed = Env assumedVP [] [assumedCN] allVars

_TRUE :: Effect -> Prop
_TRUE x = mkRec $ evalState x assumed

_ENV :: Effect -> Env
_ENV x = execState x assumed

type S = Effect
type VP = Object -> Effect -- FIXME: attempt to change to Disc (Object -> Prop)
type CN = (Object -> Effect,Gender,Number)
type CN2 = Object -> CN
type NP = Role -> VP -> Effect

(!) :: NP -> VP -> Effect
np ! vp = do
  x <- np Subject vp
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the subject. (see example9)
  return x


instance Show VP where
  show vp = "λω. " ++ mkRec (evalState (vp "ω") assumed)
instance Show NP where
  show np = mkRec (evalState (np Other $ \x -> return [("_",x)]) assumed)

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
getCN _ = (assumedPred "assumedCN",Unknown,Singular)

getNP' :: ObjQuery -> Env -> NP
getNP' _ Env{objEnv=[]} = \_ vp -> vp "assumedObj"
getNP' q Env{objEnv=((d,o):os),..} = if q d then o else getNP' q Env{objEnv=os,..}

getNP :: ObjQuery -> Disc NP
getNP q = gets (getNP' q)

-- Some debugging function
getNthNP :: Int -> Env ->  NP
getNthNP _ Env{objEnv=[]} =  \_ vp -> vp "assumedObj"
getNthNP 0 Env{objEnv=((_,o):_),..} = o
getNthNP n Env{objEnv=((d,o):os),..} = getNthNP (n-1) Env{objEnv=((d,o):os),..}

purePN ::  Object -> Gender -> NP
purePN o dGender dRole vp = do
  modify (pushNP (Descriptor{..} ) (purePN o dGender))
  vp o
  where dNumber = Singular

maryNP :: NP
maryNP = purePN "MARY" Female

johnNP :: NP
johnNP = purePN "JOHN" Male

billNP :: NP
billNP = purePN "BILL" Male

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

pron :: ObjQuery -> NP
pron q role vp = do
  np <- getNP q
  np role vp

sheNP :: NP
sheNP = pron (all' [isFemale, isSingular])

himNP :: NP
himNP = pron (all' [isMale, isSingular, isNotSubject])

heNP :: NP
heNP = pron (all' [isMale, isSingular])

himSelfNP :: NP
himSelfNP = heNP

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

his :: CN2 -> NP
his cn2 role vp = himSelfNP role $ \x -> the (cn2 x) Other vp

getFresh :: Disc String
getFresh = do
  (x:_) <- gets freshVars
  modify (\Env{freshVars=_:freshVars,..} -> Env{..})
  return x

the :: CN -> NP
the (cn,gender,number) role vp = do
  modify (pushNP (Descriptor gender number role) (the (cn,gender,number)))
  v <- getFresh
  p <- cn v
  vp ("(THE " ++ v ++ ". " ++ mkRec p ++")")
  -- FIXME: variable may escape its scope


lift2 :: (Row -> Row -> Row) -> Effect -> Effect -> Effect
lift2 = liftM2

lift1 :: (Row -> Row) -> Effect -> Effect
lift1 = fmap

prop :: Prop -> Row
prop x = [("_",x)]

imply :: String -> Row -> Row -> Row
imply implicationSymbol = \x y -> prop (mkRec x ++ " " ++ implicationSymbol ++ " " ++ mkRec y)
(<==), (~~>) :: Effect -> Effect -> Effect
a <== b = do
  a' <- a
  b' <- b
  let (props::Row,binders::Row) = partition (\(x,_) -> x == "_") a'
  return (binders ++ prop (mkRec b' ++ "->" ++ mkRec props))
(==>) :: Effect -> Effect -> Effect
(==>) = lift2 (imply "->")
(-->) :: Prop -> Prop -> Prop
x --> y = x ++ " → " ++ y
(~~>) = lift2 (imply "~>")
not' :: Effect -> Effect
not' a = do
  x <- a
  return (prop (mkPred "NOT" (mkRec x)))

(###) :: Effect -> Effect -> Effect
(###) = (∧)

(∧) :: Effect -> Effect -> Effect
(∧) = liftM2 (++)


pureVP :: (Object -> Prop) -> VP
pureVP v x = do
  modify (pushVP (pureVP v))
  return (prop (v x))
-- pushes itself in the env for reference


pureCN :: (Object -> Prop) -> Gender -> Number -> CN
pureCN cn gender number = (\x -> do
                              modify (pushCN (pureCN cn gender number))
                              return (prop (cn x))
                          ,gender,number)

pureCN2 :: (Object -> Object -> Prop) -> Gender -> Number -> CN2
pureCN2 v gender number x = pureCN (v x) gender number

leavesVP :: VP
leavesVP = pureVP (mkPred "LEAVES")

isTiredVP :: VP
isTiredVP = pureVP (mkPred "IS_TIRED")

-- (* EXAMPLE:: john leaves if he is tired *)
example0 :: Prop
example0 = _TRUE ((johnNP ! leavesVP) <== (heNP ! isTiredVP))

{-> putStrLn example0

IS_TIRED(JOHN) -> LEAVES(JOHN)
-}

doesTooVP :: VP
doesTooVP x = do
  vp <- gets vpEnv
  vp x


-- (* EXAMPLE:: john leaves if mary does [too] *)
example1 :: Prop
example1 = _TRUE ((johnNP ! leavesVP) <== (maryNP ! doesTooVP))

{-> putStrLn example1

LEAVES(MARY) -> LEAVES(JOHN)
-}

_ADMIT_V :: Prop -> Object -> Prop
_ADMIT_V = mkRel2 "ADMIT"

admitVP :: Effect -> VP
admitVP p x = do
  p' <- p
  modify (pushVP (admitVP p))
  return (prop (_ADMIT_V (mkRec p') x))

_PERSON :: Object -> Prop
_PERSON = mkPred "PERSON"

_FORALL :: String -> Prop -> Prop
_FORALL var f = "(Π("++var++" : i). " ++ f ++")"

pureObj :: Object -> NP
pureObj x _role vp = vp x

everyone :: NP
everyone = every (pureCN (mkPred "PERSON") Unknown Singular)

hide :: State s x -> State s x
hide a = do
  s <- get
  x <- a
  put s
  return x

unbound :: String
unbound = "<unbound>"

that :: CN -> VP -> CN
that (cn,gender,number) vp = (\x -> cn x ∧ vp x,gender,number)

every :: CN -> NP
every cn0@(cn,gender,Singular) role vp = do
  x <- getFresh
  p' <- hide $ do
    modify (pushNP (Descriptor gender Singular Subject) (pureObj x))
    cn x ==> vp x
  _ <- cn unbound ==> vp unbound -- the things that we talk about in the CN/VP can be referred to anyway! (see example8)
  when (role == Subject) (modify (pushVP vp)) -- see example5c for why the guard is needed.
  modify (pushNP (Descriptor Unknown Plural role) (every (cn0 `that` vp))) -- "e-type" referent
  return (prop (_FORALL x (mkRec p')))

-- The referents pushed within the FORALL scope cannot escape to the top level

-- the bound variable is still referrable within the scope. It is pushed there
-- (with the appropriate descriptor)

some :: CN -> NP
some cn0@(cn,gender,Singular) role vp = do
  x <- getFresh
  modify (pushNP (Descriptor gender Singular Subject) (pureObj x))
  p' <- cn x ∧ vp x
  modify (pushNP (Descriptor Unknown Plural role) (the (cn0 `that` vp)))
  return ((x,"i"):p')

few :: CN -> NP
few cn0@(cn,gender,Plural) role vp = do
  x <- getFresh
  p' <- hide $ do
    modify (pushNP (Descriptor gender Singular Subject) (pureObj x)) -- Attn: the number is doubtful here; in the examples I've used singular pronouns.
    cn x ~~> not' (vp x)
  _ <- cn unbound ~~> vp unbound -- the things that we talk about in the CN/VP can be referred to anyway! (see example8)
  modify (pushVP vp)
  modify (pushNP (Descriptor Unknown Plural role) (every (cn0 `that` vp))) -- "e-type" referent
  return (prop (_FORALL x (mkRec p')))


-- EXAMPLE:: everyone admits that they are tired
example2 :: Prop
example2 = _TRUE (everyone ! (admitVP (theySingNP ! isTiredVP)))


{-> putStrLn example2

(Π(a : i). PERSON(a) -> ADMIT(IS_TIRED(a),a))
-}


-- EXAMPLE:: everyone admits that they are tired Mary does too
example3 :: Prop
example3 = _TRUE ((everyone ! (admitVP (theySingNP ! isTiredVP))) ### (maryNP ! doesTooVP))

{-> putStrLn example3

(Π(a : i). PERSON(a) -> ADMIT(IS_TIRED(a),a)) × ADMIT(IS_TIRED(MARY),MARY)
-}


married :: CN2
married = pureCN2 (mkRel2 "MARRIED") Unknown Singular

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

LOVE((THE a. MARRIED(JOHN,a)),JOHN) × LOVE((THE a. MARRIED(JOHN,a)),BILL)
-}


pureV2' :: (Object -> Object -> Prop) -> NP -> VP
pureV2' v2 directObject subject = directObject Other $ \x -> do
  modify (pushVP (pureV2' v2 directObject))
  return (prop (v2 x subject))

lovesVP' :: NP -> VP
lovesVP' = pureV2' (mkRel2 "LOVE")

-- (* EXAMPLE:: john leaves his wife. Bill does too. [second reading] *)
example5b :: Effect
example5b = johnNP ! (lovesVP' hisSpouseNP) ### (billNP ! doesTooVP) 
-- With the above version of "love", the direct object is re-evaluated after it is being referred to.

{-> eval example5b

LOVE((THE a. MARRIED(JOHN,a)),JOHN) × LOVE((THE b. MARRIED(BILL,b)),BILL)
-}


lawyerCN = pureCN (mkPred "lawyer") Unknown Singular
auditorCN = pureCN (mkPred "auditor") Unknown Singular
reportCN = pureCN (mkPred "report") Neutral Singular
signV2 = pureV2' (mkRel2 "sign")

-- A lawyer signed every report, and so did an auditor.

example5c :: Effect
example5c = (aDet lawyerCN ! signV2 (every reportCN)) ### (aDet auditorCN ! doesTooVP)
{-

Analysis: in S := PN VP, the VP can refer to the subject. So the VP
must be evaluated in a context where the subject (which may be a
variable bound by a quantifier from the NP) is pushed in the
environment. Thus, the NP must take care of evaluating the VP.  A
side-effect of this evaluation is that the VP itself is pushed in the
environment by the NP

Yet, as in the above example, we have (V2 NP). In this situation V2 is
not a proper noun phrase. If we push the VP argument in the NP we get
nonsense.

A possible solution would be to separate the updates and the lookup in
the environment:

type VP = (Env -> Env, Env -> Object -> Prop)

The first component woud be evaluated "once per lexical occurence",
while the second component would be evaluated "according to the
semantic context". Yet, if we were to be doing something like this, it
would preclude "strict" readings, as in example4.

-}

{-> eval example5c

(a : i) × (c : i) × lawyer(a) × (∀ b. report(b) -> sign(b,a)) × auditor(c) × (∀ d. report(d) -> sign(d,c))
-}


-- (* EXAMPLE:: john leaves his spouse. Mary does too. *)
example6 :: Prop
example6 = _TRUE (johnNP ! (lovesVP' hisSpouseNP) ### (maryNP ! doesTooVP) )
-- Because "his" is looking for a masculine object, the re-evaluation
-- in the "does too" points back to John anyway.

{-> putStrLn example6

LOVE((THE a. MARRIED(JOHN,a)),JOHN) × LOVE((THE b. MARRIED(JOHN,b)),MARY)
-}




congressmen :: CN
congressmen = pureCN (mkPred "CONGRESSMEN") Male Plural

example7 :: Prop
example7 = _TRUE ((few congressmen ! (lovesVP billNP)) ### (theyPlNP ! isTiredVP))


-- (* EXAMPLE:: Few congressmen love bill. They are tired. *)
{-> putStrLn example7

(∀ a. CONGRESSMAN(a) ~> NOT(LOVE(BILL,a))) × (∀ b. CONGRESSMAN(b) × LOVE(BILL,b) -> IS_TIRED(b))
-}


example8 :: Prop
example8 = _TRUE ((few congressmen ! (lovesVP billNP)) ### (heNP ! isTiredVP))

-- (* EXAMPLE:: Few congressmen love bill. He is tired. *) -- The e-type referent is plural.
{-> putStrLn example8

(∀ a. CONGRESSMAN(a) ~> NOT(LOVE(BILL,a))) × IS_TIRED(BILL)
-}


example9 :: Prop
example9 = _TRUE ((johnNP ! isTiredVP) ### (billNP ! (lovesVP himNP)))
-- John is tired. Bill loves him. -- (Bill loves John, not himself.)
{-> putStrLn example9

IS_TIRED(JOHN) × LOVE(JOHN,BILL)
-}


man :: CN
man = pureCN (mkPred "MAN") Male Singular

men :: CN
men = pureCN (mkPred "MAN") Male Plural

beatV2 :: NP -> VP
beatV2 = pureV2' (mkRel2 "BEAT")

example10 :: Prop
example10 = _TRUE ((few (men `that` (lovesVP hisSpouseNP))) ! (beatV2 themSingNP))

-- (* EXAMPLE:: Few men that love their wife beat them.

{-> putStrLn example10

(Π(a : i). MAN(a) × LOVE((THE b. MARRIED(a,b)),a) ~> NOT(BEAT((THE c. MARRIED(a,c)),a)))
-}

donkey :: CN
donkey = pureCN (mkPred "DONKEY") Neutral Singular

own :: NP -> VP
own = pureV2' (mkRel2 "OWN")

aDet :: CN -> NP
aDet (cn,gender,number) role vp = do
  x <- getFresh {- note that this isn't a quantifier, 'x' is not accessible in the CN nor the VP -}
  p' <- (cn x ∧ vp x)
  modify (pushNP (Descriptor gender number role) (pureObj x))
  return ((x,"i"):p')

example11a :: Effect
example11a = (((aDet donkey) ! isTiredVP) ### (itNP ! leavesVP))
eval :: Effect -> IO ()

eval = putStrLn . _TRUE
-- A donkey is tired. It leaves.

{-> eval example11a

(a : i) × DONKEY(a) × IS_TIRED(a) × LEAVES(a)
-}


example11b :: Effect
example11b = (((aDet donkey) ! leavesVP) <== (itNP ! isTiredVP))
-- Some donkey leave if it is tired.
{-> eval example11b

(a : i) × IS_TIRED(a)->DONKEY(a) × LEAVES(a)
-}
-- The proper interpretation is : ∃z. DONKEY(z) ∧ IS_TIRED(z) ∧ LEAVES(z)
-- Seemingly the existential quantifiers gets "pulled" up as far as possible.

example11c :: Effect
example11c = (aDet (man `that` own (aDet donkey)) ! (beatV2 itNP))
-- A man that owns a donkey beats it.

{-> eval example11c

(a : i) × (b : i) × MAN(a) × DONKEY(b) × OWN(b,a) × BEAT(b,a)
-}

example11d :: Effect
example11d = ((billNP ! (own (aDet donkey))) ### (heNP ! (beatV2 itNP)))
-- Bill owns a donkey. He beats it.

{-> eval example11d

(a : i) × DONKEY(a) × OWN(a,BILL) × BEAT(a,BILL)
-}

example11 :: Effect
example11 = (every (man `that` own (aDet donkey)) ! (beatV2 itNP))
-- Every man that owns a donkey beat it.

{-> eval example11

(Π(a : i). (b : i) × MAN(a) × DONKEY(b) × OWN(b,a) -> BEAT(b,a))
-}


example13 :: Effect
example13 = billNP ! (own (aDet (donkey `that` (\x -> heNP ! (beatV2 (pureObj x))))))
-- Bill owns a donkey that he beats.


{-> eval example13

(a : i) × DONKEY(a) × BEAT(a,BILL) × OWN(a,BILL)
-}

oneToo :: NP
oneToo role vp = do
  cn <- gets getCN
  aDet cn role vp


example14 :: Effect
example14 = (billNP ! own (aDet donkey)) ### (johnNP ! (own oneToo))

{-> eval example14

(a : i) × DONKEY(a) × OWN(a,BILL) × (b : i) × DONKEY(b) × OWN(b,JOHN)
-}

commitee :: CN
commitee = pureCN (mkPred "commitee") Neutral Singular

chairman :: CN
chairman = pureCN (mkPred "chairman") Male Singular

has = pureV2' (mkRel2 "have")

example15 :: Effect
example15 = every commitee ! has (aDet chairman)
-- every man owns a donkey. He beats it. #?!
-- every commitee has a chairman. He is appointed by its members. #?

{-> eval example15

(Π(a : i). commitee(a) -> (b : i) × chairman(b) × have(b,a))
-}



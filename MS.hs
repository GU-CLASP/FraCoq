{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}

module MS where

import Prelude hiding (pred)
import Control.Monad.State hiding (ap)
import Logic

type Object = Exp

type Prop = Exp


data Gender where
   Male :: Gender
   Female :: Gender
   Neutral :: Gender
   Unknown :: Gender -- male or female
  deriving (Eq,Show)

data Number where
  Singular :: Number
  Plural :: Number
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
               ,vp2Env :: VP2
               ,apEnv :: AP
               ,cn2Env :: CN2
               ,objEnv :: ObjEnv
               ,cnEnv :: NounEnv
               ,sEnv :: S
               ,envThings :: Exp -> Object -- map from CN to pure objects
               ,envSloppyFeatures :: Bool
               ,freshVars :: [String]}
         -- deriving Show

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

assumedPred :: String -> Dynamic (Object -> Prop)
assumedPred predName = do
  return $ \x -> (mkPred predName x)

assumed :: Env
assumed = Env {vpEnv = assumedPred "assumedVP"
              ,vp2Env = return $ \x y -> (mkRel2 "assumedV2" x y)
              ,apEnv = (pureIntersectiveAP (mkPred "assumedAP"))
              ,cn2Env = pureCN2 (mkPred "assumedCN2") Neutral Singular
              ,objEnv = []
              ,sEnv = return (constant "assumedS")
              ,cnEnv = [return (Var "assumedCN",Unknown,Singular)]
              ,envThings = \x -> Op THE [x]
              ,envSloppyFeatures = False
              ,freshVars = allVars}

_TRUE :: Effect -> Prop
_TRUE x = evalState x assumed

_ENV :: Effect -> Env
_ENV x = execState x assumed

type S = Dynamic Prop
type VP = Dynamic (Object -> Prop)
type VP2 = Dynamic (Object -> Object -> Prop)
type VP3 = Dynamic (Object -> Object -> Object -> Prop)
type CN = Dynamic (Type,Gender,Number)
type AP = Dynamic (Type -> Type)
type CN2 = Dynamic ((Object -> Type),Gender,Number)
type NP = Role -> Dynamic ((Object -> Prop) -> Prop)
type AdvV = Dynamic ((Object -> Prop) -> (Object -> Prop))

(!) :: NP -> VP -> Effect
(!) = predVP

predVP :: NP -> VP -> Effect
predVP np vp = do
  np' <- np Subject
  vp' <- vp
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the direct arguments.
  modify (pushS (predVP np vp))
  return (np' vp')

(?) :: VP2 -> NP -> VP
(?) = appVP2

appVP2 :: VP2 -> NP -> VP
appVP2 v2 directObject = do
  v2' <- v2
  do' <- directObject Other
  modify (pushVP (appVP2 v2 directObject))
  return (\y -> do' $ \x -> (v2' x y))

(¿) :: NP -> VP2 -> VP
(¿) = slashVP

slashVP :: NP -> VP2 -> VP
slashVP subj v2 = do
  subj' <- subj Subject
  v2' <- v2
  -- Don't push these things (slash vps).
  return $ \x -> subj' $ \y -> v2' x y

appVP3 :: VP3 -> NP -> VP2
appVP3 v3 obj = do
  v3' <- v3
  o' <- obj Other
  -- Don't push these things (not implemented)
  return $ \x y -> o' $ \z -> v3' z x y

  
-- instance Show VP where
--   show vp = "λω. " ++ mkRec (evalState (vp "ω") assumed)
-- instance Show NP where
--   show np = mkRec (evalState (np Other $ \x -> return [("_",x)]) assumed)

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

pushNP :: Descriptor -> NP -> Env -> Env
pushNP d o1 Env{..} = Env{objEnv = (d,o1):objEnv,..}

pushThing :: Exp -> Var -> Env -> Env
pushThing source target Env{..} = Env{envThings = \x -> if x == source then Var target else envThings x,..}


pushVP :: VP -> Env -> Env
pushVP vp Env{..} = Env{vpEnv=vp,..}

pushV2 :: VP2 -> Env -> Env
pushV2 vp2 Env{..} = Env{vp2Env=vp2,..}

pushAP :: AP -> Env -> Env
pushAP a Env{..} = Env{apEnv=a,..}

pushCN :: CN -> Env -> Env
pushCN cn Env{..} = Env{cnEnv=cn:cnEnv,..}

pushCN2 :: CN2 -> Env -> Env
pushCN2 cn2 Env{..} = Env{cn2Env=cn2,..}

pushS :: S -> Env -> Env
pushS s Env{..} = Env{sEnv=s,..}

getCN :: Env -> CN
getCN Env{cnEnv=cn:_} = cn
getCN _ = return (constant "assumedCN",Unknown,Singular)

getCN2 :: Env -> CN2
getCN2 Env{cn2Env=cn} = cn

getNP' :: ObjQuery -> Env -> NP
getNP' _ Env{objEnv=[]} = \_role -> return (\vp -> vp (constant "assumedNP"))
getNP' q Env{objEnv=((d,o):os),..} = if q d then o else getNP' q Env{objEnv=os,..}


getNP :: ObjQuery -> Dynamic NP
getNP q = gets (getNP' q)

pureNP :: Object -> Gender ->  Number -> NP
pureNP o dGender dNumber dRole = do
  modify (pushNP (Descriptor{..}) (pureNP o dGender dNumber))
  return (\vp -> vp o)
  

purePN ::  String -> Gender -> NP
purePN o dGender = pureNP (Con o) dGender Singular

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

pron :: ObjQuery -> NP
pron q role = do
  np <- getNP q
  np role

sheNP :: NP
sheNP = pron (all' [isFemale, isSingular])

himNP :: NP
himNP = pron (all' [isMale, isSingular, isNotSubject])

herNP :: NP
herNP = pron (all' [isFemale, isSingular, isNotSubject])

heNP :: NP
heNP = pron (all' [isMale, isSingular])

himSelfNP :: NP
himSelfNP = pron (all' [isMale, isSingular, isCoArgument])

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

getFresh :: Dynamic String
getFresh = do
  (x:_) <- gets freshVars
  modify (\Env{freshVars=_:freshVars,..} -> Env{..})
  return x

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


pureCN :: Type -> Gender -> Number -> CN
pureCN cn gender number =
  do modify (pushCN (pureCN cn gender number))
     return (cn,gender,number)

pureCN2 :: (Object -> Type) -> Gender -> Number -> CN2
pureCN2 v gender number = do
  modify (pushCN2 (pureCN2 v gender number))
  return (v,gender,number)

constant :: String -> Exp
constant x = Con x


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


pureObj :: Exp -> NP
pureObj x _role = return (\vp -> vp (x))

pureVar :: Var -> NP
pureVar x = pureObj (Var x)

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

every :: CN -> NP
every cn role = do -- allow any number so that it can be reused in 'few'
  x <- getFresh
  (cn',gender,number) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x))
  return $ \vp' -> (Forall x cn' (vp' (Var x)))

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

pureV2 :: (Object -> Object -> Prop) -> VP2
pureV2 v2 = do
  modify (pushV2 (pureV2 v2))
  return (\y x -> (v2 x y))

pureV3 :: (Object -> Object -> Object -> Prop) -> VP3
pureV3 v3 = do
  -- modify (pushV2 (pureV2 v2)) -- no v3 yet in the env
  return v3




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

doTooV2 :: VP2
doTooV2 = do
  v2 <- gets vp2Env
  sloppily v2

hasTooV2 :: VP2
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

pureIntersectiveAP :: (Object -> Prop) -> AP
pureIntersectiveAP q = do
  modify (pushAP (pureIntersectiveAP q))
  x <- getFresh
  return (\typ -> Sigma x typ (q (Var x)))

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

slappedV2 :: VP2
slappedV2 = pureV2 (mkRel2 "slapped")
hurtV2 :: VP2
hurtV2 = pureV2 (mkRel2 "hurt")

is_wiser_thanV2 :: VP2
is_wiser_thanV2 = pureV2 (mkRel2 "wiser")

is_larger_thanV2 :: VP2
is_larger_thanV2 = pureV2 (mkRel2 "larger")

gaveV3 :: VP3
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


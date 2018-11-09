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

import Prelude hiding (pred,Ord,Num)
import Control.Monad.State hiding (ap)
import Logic hiding (Pol)
import qualified Logic
import Data.List (intersect,nub,partition,nubBy,sortBy)
import Control.Monad.Logic hiding (ap)
import Control.Applicative
import Control.Applicative.Alternative
import Data.Function (on)
import Control.Arrow (first)

type Object = Exp
type Prop = Exp


--------------------------------
-- Operators

protected :: Dynamic a -> Dynamic a
protected a = do
  s <- get
  x <- a
  put s
  return x


imply :: Monad m => (t1 -> t -> b) -> m t1 -> m t -> m b
imply implication a b = do
  a' <- a
  b' <- b
  return (implication a' b')

(==>) :: Effect -> Effect -> Effect
(==>) = imply (-->)

data Gender where
   Male :: Gender
   Female :: Gender
   Neutral :: Gender
  deriving (Eq,Show)

data Role where
  Subject :: Role
  Other :: Role
  deriving (Eq,Show)

-- first :: (t2 -> t1) -> (t2, t) -> (t1, t)
-- first f (x,y) = (f x,y)
second :: forall t t1 t2. (t2 -> t1) -> (t, t2) -> (t, t1)
second f (x,y) = (x,f y)

data Descriptor = Descriptor {dPluralizable :: Bool
                             ,dGender :: [Gender]
                             ,dNum :: Num
                             ,dRole :: Role} deriving Show

type ObjQuery = Descriptor -> Bool
type ObjEnv = [(Descriptor,NP)]
type NounEnv = [CN]


clearRole :: Env -> Env
clearRole Env{..} = Env{objEnv = map cr objEnv,..}
  where cr (d,np) = (d {dRole = Other},np)


-- | After a sentence is closed, we may need to allow to refer certain objects by a plural.
-- See fracas 131.
pluralize :: Env -> Env
pluralize Env{..} = Env{objEnv = map (first pl) objEnv,..}
  where pl Descriptor{..} = Descriptor{dNum = if dPluralizable then Unspecified else dNum,..}
  -- FIXME this should be done only on things that are introduced inside the sentence!

withClause :: MonadState Env m => m b -> m b
withClause e = do
  pl <- gets envPluralizingQuantifier
  x <- e
  modify clearRole -- Once the sentence is complete, accusative pronouns can refer to the direct arguments.
  modify pluralize
  modify $ \Env{..} -> Env{envPluralizingQuantifier = pl,..}
  return x



type VPEnv = [VP]

data Env = Env {vpEnv :: VPEnv
               ,vp2Env :: V2
               ,apEnv :: AP
               ,cn2Env :: CN2
               ,objEnv :: ObjEnv
               ,cnEnv :: NounEnv
               ,sEnv :: S
               ,envDefinites :: Exp -> Object -- map from CN to pure objects
               ,envSloppyFeatures :: Bool
               ,envPluralizingQuantifier :: Bool
               ,freshVars :: [String]}
         -- deriving Show

------------------------------
-- Gets

overlaps :: Eq a => [a] -> [a] -> Bool
overlaps a b = case intersect a b of
  [] -> False
  _ -> True

isNeutral, isMale, isFemale :: Descriptor -> Bool
isMale Descriptor{..} = dGender `overlaps` [Male]
isFemale Descriptor{..} = dGender `overlaps` [Female]
isNeutral Descriptor{..} = dGender `overlaps` [Neutral]

isPerson :: Descriptor -> Bool
isPerson = const True -- FIXME

isSingular :: Descriptor -> Bool
isSingular Descriptor {..} = dNum `elem` [Singular, Cardinal 1, Unspecified]

isPlural :: Descriptor -> Bool
isPlural Descriptor {..} = dNum `elem` [Plural, Unspecified] -- FIXME: many more cases

isNotSubject :: Descriptor -> Bool
isNotSubject = (/= Subject) . dRole

isCoArgument :: Descriptor -> Bool
isCoArgument = (== Subject) . dRole

getCN :: Env -> [CN]
getCN Env{cnEnv=cn:cns} = cn:cns
getCN _ = [return assumedCN]

getCN2 :: Env -> CN2
getCN2 Env{cn2Env=cn} = cn

getNP' :: ObjQuery -> Env -> [NP]
getNP' q Env{objEnv=os,..} = case filter (q . fst) os of
  [] -> [return $ MkNP assumedNum (\_num _cn _role -> return (\vp -> vp (constant "assumedNP"))) assumedCN]
  xs -> map snd xs


getNP :: ObjQuery -> Dynamic [NP]
getNP q = gets (getNP' q)

getDefinite :: CN' -> Dynamic Object
getDefinite (cn',_gender) = do
  things <- gets envDefinites
  return (things (lam (\x -> noExtraObjs (cn' x))))

-------------------------------
-- Pushes


pushDefinite :: (Object -> S') -> Var -> Env -> Env
pushDefinite source target Env{..} = Env{envDefinites = \x ->
                                                    if eqExp 0 x (lam (\x' -> noExtraObjs (source x')))
                                                    then Var target
                                                    else envDefinites x,..}

pushNP :: Descriptor -> NP -> Env -> Env
pushNP d o1 Env{..} = Env{objEnv = (d,o1):objEnv,..}

pushCN :: CN -> Env -> Env
pushCN cn Env{..} = Env{cnEnv=cn:cnEnv,..}

pushVP :: VP -> Env -> Env
pushVP vp Env{..} = Env{vpEnv=vp:vpEnv,..}

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

newtype Dynamic a = Dynamic {fromDynamic :: StateT Env Logic a} deriving (Monad,Applicative,Functor,MonadState Env,Alternative,MonadPlus,MonadLogic)
allInterpretations :: Dynamic a -> [a]
allInterpretations (Dynamic x) = (observeAll (evalStateT x assumed))

-- newtype Dynamic a = Dynamic {fromDynamic :: LogicT (State Env) a} deriving (Monad,Applicative,Functor,MonadState Env,Alternative,MonadPlus,MonadLogic)

type Effect = Dynamic Prop

appArgs :: String -> [Object] -> ExtraArgs -> Prop
appArgs nm objs@(_:_) (prepositions0,adverbs) = adverbs  (app prep'd) directObject
  where prep'd = Con (nm ++ concatMap fst prepositions) `apps` (map snd prepositions ++ indirectObjects)
        indirectObjects = init objs
        directObject = last objs
        prepositions = sortBy (compare `on` fst) $ nubBy ((==) `on` fst) prepositions0

appAdjArgs :: String -> [Object] -> ExtraArgs -> Prop
appAdjArgs nm [cn,obj] (prepositions0,adverbs) = adverbs  (\x -> apps prep'd [cn,x]) obj
  where prep'd = Con "appA" `app` (Con (nm ++ concatMap fst prepositions) `apps` ((map snd prepositions)))
        prepositions = nubBy ((==) `on` fst) prepositions0

mkPred :: String -> Object -> S'
mkPred p x extraObjs = appArgs p [x] extraObjs


mkRel2 :: String -> Object -> Object -> S'
mkRel2 p x y extraObjs = appArgs p [x,y] extraObjs


mkRel3 :: String -> Object -> Object -> Object -> S'
mkRel3 p x y z extraObjs = appArgs p [x,y,z] extraObjs

constant :: String -> Exp
constant x = Con x

pureObj :: Exp -> Num -> CN' -> NP
pureObj x number cn  = return $ MkNP number (\_number _cn _role -> return $ \vp -> vp x) cn

pureVar :: Var -> Num -> CN' -> NP
pureVar x = pureObj (Var x)

getFresh :: Dynamic String
getFresh = do
  (x:_) <- gets freshVars
  modify (\Env{freshVars=_:freshVars,..} -> Env{..})
  return x


----------------------------------
-- Assumed

assumedPred :: String -> Dynamic (Object -> S')
assumedPred predName = do
  return $ \x -> (mkPred predName x)

assumedCN :: CN'
assumedCN = (mkPred "assumedCN", [Male,Female,Neutral])

assumedNum :: Num
assumedNum = Singular

assumed :: Env
assumed = Env {vp2Env = return $ \x y -> (mkRel2 "assumedV2" x y)
               , vpEnv = []
               -- ,apEnv = (pureIntersectiveAP (mkPred "assumedAP"))
               -- ,cn2Env = pureCN2 (mkPred "assumedCN2") Neutral Singular
               ,objEnv = []
               ,sEnv = return (\_ -> constant "assumedS")
               ,cnEnv = []
               ,envDefinites = The
               ,envSloppyFeatures = False
               ,envPluralizingQuantifier = False
               ,freshVars = allVars}


onS' :: (Prop -> Prop) -> S' -> S'
onS' f p eos = f (p eos)

type ExtraArgs = ([(Var,Object)] -- prepositions
                 ,(Object -> Prop) -> Object -> Prop) -- adverbs

type S' = ExtraArgs -> Prop
type S = Dynamic S'
type V2 = Dynamic (Object -> Object -> S') --  Object first, subject second.
type V3 = Dynamic (Object -> Object -> Object -> S')
type CN' = (Object -> S',[Gender])
type CN = Dynamic CN'
type CN2 = Dynamic CN2'
type CN2' = (Object -> Object -> S',[Gender])
type NP' = (Object -> S') -> S'
type NP = Dynamic NPData

type V = Dynamic (Object -> S')
type V2S = Dynamic (Object -> S' -> Object -> S')
type V2V = Dynamic (Object -> VP' -> Object -> S')
type VV = Dynamic (VP' -> Object -> S')
type SC = Dynamic VP'
type VS = Dynamic (S' -> VP')

type Cl =  Dynamic S'
type Temp = Prop -> Prop
type Predet = NPData -> NPData
type ClSlash  = Dynamic VP'
type RCl  = Dynamic RCl'
type RCl' = Object -> Prop
type RS  = Dynamic RCl'

data Num where
  Unspecified :: Num
  Singular :: Num
  Plural   :: Num
  AFew :: Num
  MoreThan :: Num -> Num
  Cardinal :: Nat -> Num
  deriving (Show,Eq)

numSg,numPl :: Num
numSg = Singular
numPl = Singular

data NPData where
  MkNP :: Num -> Quant -> CN' -> NPData

type N = CN
type PN = (String,[Gender],Num)

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

any' :: [a -> Bool] -> a -> Bool
any' fs x = any ($ x) fs

-------------------
-- "PureX"
genderedN :: String -> [Gender] -> CN
genderedN s gender =
  do modify (pushCN (genderedN s gender))
     return (mkPred s,gender)

genderedN2 :: String -> [Gender] -> CN2
genderedN2 s gender =
  do modify (pushCN2 (genderedN2 s gender))
     return (mkRel2 s,gender)

pureV2 :: (Object -> Object -> S') -> V2
pureV2 v2 = do
  modify (pushV2 (pureV2 v2))
  return (\x y -> (v2 x y))

pureV3 :: (Object -> Object -> Object -> S') -> V3
pureV3 v3 = do
  -- modify (pushV2 (pureV2 v2)) -- no v3 yet in the env
  return v3

-----------------
-- Lexemes
meta :: Exp
meta = Con "META"

lexemeV :: String -> V
lexemeV x = return $ mkPred x

lexemeVP :: String -> VP
lexemeVP "elliptic_VP" = elliptic_VP
lexemeVP x = return $ mkPred x

lexemeA :: String -> A
lexemeA a = return $ (\cn obj -> appAdjArgs a [lam cn,obj])

lexemeV3 :: String -> V3
lexemeV3 x = return $ mkRel3 x

lexemeV2 :: String -> V2
lexemeV2 x = pureV2 (mkRel2 x)

lexemeV2S :: String -> V2S
lexemeV2S v2s = return $ \x s y -> mkRel3 v2s x (noExtraObjs s) y

lexemeVS :: String -> VS
lexemeVS vs = return $ \s x -> mkRel2 vs (noExtraObjs s) x

lexemeV2V :: String -> V2V
lexemeV2V v2v = return $ \x vp y -> appArgs v2v [x,lam (\z -> noExtraObjs (vp z)),y]

pnTable :: [(String,([Gender],Num))]
pnTable = [("smith_PN" , ([Male,Female],Singular)) -- smith is female in 123 but male in 182 and following
          ,("john_PN" , ([Male],Singular))
          ,("itel_PN" , ([Neutral],Plural))
          ,("gfi_PN" , ([Neutral],Singular))
          ,("bt_PN" , ([Neutral],Plural))
          ,("mary_PN" , ([Female],Singular))]

lexemePN :: String -> PN
lexemePN x = case lookup x pnTable of
  Just (g,n) -> (x,g,n)
  Nothing -> (x,[Male,Female,Neutral],Unspecified)

type Prep = Dynamic (Object -> S' -> S')
lexemePrep :: String -> Prep
lexemePrep "by8agent_Prep" = return (modifyingPrep "by")
lexemePrep prep  = return (modifyingPrep (takeWhile (/= '_') prep))


modifyingPrep :: String -> Object -> S' -> S'
modifyingPrep aname x s (preps,adv) = s (preps++[(aname,x)],adv)

type RP = ()
lexemeRP :: String -> RP
lexemeRP _ = ()

idRP :: RP
idRP = ()

implicitRP :: RP
implicitRP = ()

---------------------
-- Unimplemented categories

future,pastPerfect,past,present,presentPerfect :: Temp
past = id
present = id
presentPerfect = id
pastPerfect = id
future = id

------------------
-- Pol
type Pol = Prop -> Prop

pPos :: Pol
pPos = id

pNeg :: Pol
pNeg = not'

uncNeg :: Pol
uncNeg = pNeg

-----------------
-- Card

type Card = Num

adNum :: AdN -> Card -> Card
adNum = id

numNumeral :: Numeral -> Card
numNumeral = Cardinal

--------------------
-- AdN
type AdN = Card -> Card

more_than_AdN :: AdN
more_than_AdN = MoreThan

-----------------
-- Nums

numCard :: Card -> Num
numCard = id

type Numeral = Nat

n_two :: Nat
n_two = 2
n_10 :: Nat
n_10 = 10
n_100 :: Nat
n_100 = 100
n_13 :: Nat
n_13 = 13
n_14 :: Nat
n_14 = 14
n_15 :: Nat
n_15 = 15
n_150 :: Nat
n_150 = 150
n_2 :: Nat
n_2 = 2
n_2500 :: Nat
n_2500 = 2500
n_3000 :: Nat
n_3000 = 3000
n_4 :: Nat
n_4 = 4
n_500 :: Nat
n_500 = 500
n_5500 :: Nat
n_5500 = 5500
n_8 :: Nat
n_8 = 8
n_99 :: Nat
n_99 = 99
n_eight :: Nat
n_eight = 8
n_eleven :: Nat
n_eleven = 11
n_five :: Nat
n_five = 5
n_fortyfive :: Nat
n_fortyfive = 45
n_four :: Nat
n_four = 4
n_one :: Nat
n_one = 1
n_six :: Nat
n_six = 6
n_sixteen :: Nat
n_sixteen = 16
n_ten :: Nat
n_ten = 10
n_three :: Nat
n_three = 3
n_twenty :: Nat
n_twenty = 20

-------------------
-- N2
lexemeN2 :: String -> N2
lexemeN2 x = genderedN2 x [Male,Female,Neutral]

--------------------
-- N

lexemeN :: String -> N
lexemeN "one_N" = one_N
lexemeN x@"line_N" = genderedN x [Neutral]
lexemeN x@"department_N" = genderedN x [Neutral]
lexemeN x@"committee_N" = genderedN x [Neutral]
lexemeN x@"customer_N" = genderedN x [Male,Female]
lexemeN x@"executive_N" = genderedN x [Male,Female]
lexemeN x@"sales_department_N" = genderedN x [Neutral]
lexemeN x@"invoice_N" = genderedN x [Neutral]
lexemeN x@"meeting_N" = genderedN x [Neutral]
lexemeN x@"report_N" = genderedN x [Neutral]
lexemeN x@"laptop_computer_N" = genderedN x [Neutral]
lexemeN x@"car_N" = genderedN x [Neutral]
lexemeN x@"company_N" = genderedN x [Neutral]
lexemeN x@"proposal_N" = genderedN x [Neutral]
lexemeN x@"chairman_N" = genderedN x [Male]
lexemeN x = genderedN x [Male,Female,Neutral]

one_N :: N
one_N = elliptic_CN


--------------------
-- A

type A = Dynamic A'
type A' = (Object -> Prop) -> Object -> S'

positA :: A -> A
positA = id

--------------
-- A2

type A2' = Object -> (Object -> Prop) -> Object -> Prop
type A2 = Dynamic A2'

lexemeA2 :: String -> A2
lexemeA2 a = return $ \x cn y -> Con a `apps` [x,lam cn,y]

--------------------
-- AP

type AP = Dynamic A'

advAP :: AP -> Adv -> AP -- basically wrong syntax in the input. (Instead of AP we should have CN)
advAP ap adv = do
  adv' <- adv
  ap' <- ap
  return (\cn x -> adv' (ap' cn x))

sentAP :: AP -> SC -> AP
sentAP ap cl = do
  ap' <- ap
  cl' <- cl
  return $ \cn x -> ap' (\y -> noExtraObjs (cl' y) ∧ cn y) x

complA2 :: A2 -> NP -> AP
complA2 a2 np = do
  a2' <- a2
  np' <- interpNP np Other
  return $ \cn x -> (np' (\y _extraObjs  -> a2' x cn y))

adAP :: AdA -> AP -> AP
adAP ada a = do
  ada' <- ada
  a' <- a
  return $ ada' a'

comparA :: A -> NP -> AP
comparA a np = do
  a' <- a
  np' <- interpNP np Other
  return $ \cn' x -> (np' (\y extraObjs -> (a' cn' y extraObjs --> a' cn' x extraObjs) ∧ (not' (a' cn' x extraObjs) --> not' (a' cn' y extraObjs))))

comparAsAs :: A -> NP -> AP
comparAsAs a np = do
  a' <- a
  np' <- interpNP np Other
  return $ \cn' x -> np' (\ y extraObjs -> a' cn' x extraObjs <-> a' cn' y extraObjs)

-- FIXME: very questionable that this should even be in the syntax.
useComparA_prefix :: A -> AP
useComparA_prefix a = do
  a' <- a
  return $ \cn' x -> a' cn' x


--------------------
-- Subjs
type Subj = Dynamic (S' -> S' -> S')

lexemeSubj :: String -> Subj
lexemeSubj s = return $ \s1 s2 extraObjs -> Con s `apps` [s1 extraObjs, s2 extraObjs]

--------------------
-- AdA

type AdA  = Dynamic (A' -> A')
 
lexemeAdA :: String -> AdA
lexemeAdA ada = return $ \a cn x extraObjs -> Con ada `apps` [lam $ \cn2 -> lam $ \x2 -> a (app cn2) x2 extraObjs,lam cn,x]

--------------------
-- Adv

type ADV' = S' -> S'
type ADV = Dynamic ADV'
type Adv = ADV
type AdvV = ADV
type AdV = ADV

lexemeAdv :: String -> Adv
lexemeAdv "too_Adv" = uninformativeAdv -- TODO: in coq
lexemeAdv "also_AdV" = uninformativeAdv -- TODO: in coq
lexemeAdv adv = return $ sentenceApplyAdv (appAdverb adv)

sentenceApplyAdv :: ((Object -> Prop) -> Object -> Prop) -> S' -> S'
sentenceApplyAdv adv = \s' (preps,adv') -> s' (preps,adv . adv')

appAdverb :: String -> (Object -> Prop) -> (Object -> Prop)
appAdverb adv vp obj = apps (Con "appAdv") [Con adv,lam vp, obj]

positAdvAdj :: A -> Adv
positAdvAdj a = do
  a' <- a
  return $ sentenceApplyAdv (\p x -> noExtraObjs (a' p x) )

uninformativeAdv :: Adv
uninformativeAdv = return $ \vp x -> vp x -- ALT: Coq/HOL

lexemeAdV :: String -> AdV
lexemeAdV = lexemeAdv


prepNP :: Prep -> NP -> AdV
prepNP prep np = do
  prep' <- prep
  np' <- interpNP np Other
  return (\s' -> np' $ \x -> prep' x s')

subjS :: Subj -> S -> Adv
subjS subj s = do
  subj' <- subj
  s' <- s
  return $ subj' s'


--------------------
-- CN

useN :: N -> CN
useN = id

combineGenders :: [Gender] -> [Gender] -> [Gender]
combineGenders g1 g2 = case intersect g1 g2 of
  [] -> [Neutral]
  i -> i

conjCN2 :: Conj -> CN -> CN -> CN
conjCN2 c cn1 cn2 = do
  (c1,g1) <- cn1
  (c2,g2) <- cn2
  return (\x -> apConj2 c (c1 x) (c2 x),combineGenders g1 g2)

relCN :: CN->RS->CN
relCN cn rs = do
  (cn',gender) <- cn
  rs' <- rs
  return $ (\x eos -> cn' x eos ∧ rs' x, gender)
   -- GF FIXME: Relative clauses should apply to NPs. See 013, 027, 044

advCN :: CN -> Adv -> CN
advCN cn adv = do
  (cn',gender) <- cn
  adv' <- adv
  return (\x eos -> adv' (cn' x) eos ,gender) -- FIXME: lift cn


adjCN :: A -> CN -> CN
adjCN a cn = do
  a' <- a
  (cn',gendr) <- cn
  modify (pushCN (adjCN a cn))
  return $ (\x eos -> noExtraObjs (a' (flip cn' eos) x),gendr)

elliptic_CN :: CN
elliptic_CN = do
  cns <- gets getCN
  cn <- afromList cns
  cn

type N2 = CN2
complN2 :: N2 -> NP -> CN
complN2 n2 np = do
  (n2',gender) <- n2
  np' <- interpNP np Other
  return (\y -> np' $ \x -> n2' y x, gender)

sentCN :: CN -> SC -> CN
sentCN cn sc = do
  (cn',gender) <- cn
  sc' <- sc
  return $ (\x extraObjs -> apps (Con "SentCN") [lam (flip cn' extraObjs),lam (nos sc'),x],gender)

--------------------
-- SC

embedVP :: VP -> SC
embedVP = id

embedPresPart :: VP -> SC
embedPresPart = id

embedS :: S -> SC
embedS s = do
  s' <- s
  return $ \_x -> s' -- this is only used with an impersonal subject. so we can ignore it safely.

------------------------
-- NP

oneToo :: NP
oneToo = do
  cn' <- elliptic_CN
  return $ MkNP Singular indefArt cn'

interpNP :: NP -> Role -> Dynamic NP'
interpNP np role = do
  MkNP n q c <- np
  q n c role

elliptic_NP_Sg :: NP
elliptic_NP_Sg = qPron $ all' [isSingular]

usePN ::  PN -> NP
usePN (o,g,n) = pureNP False (Con (parens ("PN2object " ++ o))) g n Subject -- FIXME: role

pureNP :: Bool -> Object -> [Gender] -> Num -> Role -> NP
pureNP dPluralizable o dGender dNum dRole = do
  modify (pushNP (Descriptor{..}) (pureNP dPluralizable o dGender dNum dRole))
  return $ MkNP dNum q (\_ _ -> true,dGender)
  where q :: Quant
        q _dNum _oClass _dRole = do
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
               return $ \vp -> adv' (p1 vp)) 
           (cn1,gender1)

predetNP :: Predet -> NP -> NP
predetNP f np = do
  np' <- np
  return (f np')

-- FIXME: WTF?
detNP :: Det -> NP
detNP (number,quant) =
  return (MkNP number quant (const (const TRUE) {- fixme -},[Male,Female,Neutral]))


pPartNP :: NP -> V2 -> NP  -- Word of warning: in FraCas partitives always behave like intersection, which is probably not true in general
pPartNP np v2 = do
  MkNP num q (cn,gender) <- np
  v2' <- v2
  subject <- getFresh
  return $ MkNP num q ((\x eos -> (cn x eos)  ∧ Exists subject true (noExtraObjs (v2' x (Var subject)))),gender)

relNPa :: NP -> RS -> NP
relNPa np rs = do
  MkNP num q (cn,gender) <- np
  rs' <- rs
  return $ MkNP num q (\x eos -> cn x eos ∧ rs' x, gender)


conjNP2 :: Conj -> NP -> NP -> NP
conjNP2 c np1 np2 = do
  MkNP num1 q1 (cn1,gender1) <- np1
  MkNP _num2 q2 (cn2,gender2) <- np2
  modify (pushNP (Descriptor False (nub (gender1 ++ gender2)) Plural Other) (conjNP2 c np1 np2))
  return $ MkNP (num1) {- FIXME add numbers? min? max? -}
                -- (\num' cn' vp -> apConj2 c (q1 num' cn' vp) (q2 num' cn' vp))
                (\num' cn' role -> do
                    p1 <- q1 num' (cn1,gender1) role
                    p2 <- q2 num' (cn2,gender2) role
                    return $ \vp -> apConj2 c (p1 vp) (p2 vp))
                (\x eos -> cn1 x eos ∨ cn2 x eos, gender1) -- FIXME: problem 128, etc.
  

conjNP3 :: Conj -> NP -> NP -> NP -> NP
conjNP3 c np1 np2 np3 = do
  MkNP num1 q1 (cn1,gender1) <- np1
  MkNP _num2 q2 (cn2,gender2) <- np2
  MkNP _num3 q3 (cn3,gender3) <- np3
  return $ MkNP (num1) {- FIXME add numbers? min? max? -}
                -- (\num' cn' vp -> apConj2 c (q1 num' cn' vp) (q2 num' cn' vp))
                (\num' cn' role -> do
                    p1 <- q1 num' (cn1,gender1) role
                    p2 <- q2 num' (cn2,gender2) role
                    p3 <- q3 num' (cn3,gender3) role
                    return $ \vp -> apConj3 c (p1 vp) (p2 vp) (p3 vp))
                (\x eos -> cn1 x eos ∨ cn2 x eos ∨ cn3 x eos, gender1)


----------------------
-- Pron

type Pron = NP

qPron :: ObjQuery -> Pron
qPron q = do
  (isSloppy :: Bool) <- gets envSloppyFeatures
  nps <- getNP (\x -> isSloppy || q x)
  np <- afromList nps
  protected np

sheRefl_Pron :: Pron
sheRefl_Pron = qPron $ all' [isFemale, isSingular, isCoArgument]

theyRefl_Pron :: Pron
theyRefl_Pron = qPron $ all' [isPlural, isCoArgument]

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
they_Pron = qPron $ all' [isPlural
                         , not . isCoArgument -- this form excludes "themselves"
                         ]

someone_Pron :: Pron
someone_Pron = return $ MkNP Singular indefArt (mkPred "Person_N",[Male,Female])

maximallySloppyPron :: Pron
maximallySloppyPron = qPron $ const True

everyone_Pron :: Pron
everyone_Pron = return $ MkNP Unspecified every_Quant (mkPred "Person_N",[Male,Female])

no_one_Pron :: Pron
no_one_Pron = return $ MkNP Unspecified none_Quant (mkPred "Person_N",[Male,Female])

nobody_Pron :: Pron
nobody_Pron = no_one_Pron

----------------------------
-- Ord
type Ord = A' -- FIXME

ordSuperl :: A -> Ord
ordSuperl _ = return (\x _ -> x) -- FIXME

ordNumeral :: Numeral -> Ord
ordNumeral _ = return (\x _ -> x) -- FIXME

---------------------------
-- Det

type Det = (Num,Quant)

one_or_more_Det :: Det
one_or_more_Det = (Unspecified,atLeastQuant (Cardinal 1))

another_Det :: Det
another_Det = (Cardinal 1, anotherQuant)
  where anotherQuant number (cn',gender) role = do
          x <- getFresh
          y <- getDefinite (cn',gender)
          dPluralizable <- gets envPluralizingQuantifier
          modify (pushNP (Descriptor dPluralizable gender Plural role) (pureVar x number (cn',gender)))
          return $ \vp extraObjs -> Exists x (noExtraObjs (cn' (Var x)) ∧ not' (Var x === y)) (vp (Var x) extraObjs)

detQuant :: Quant -> Num -> Det
detQuant _ (Cardinal n) = (Cardinal n,atLeastQuant (Cardinal n))
detQuant q n = (n,q)

detQuantOrd :: Quant->Num->Ord->Det
detQuantOrd q n o = (n,q) -- FIXME: do not ignore the ord

boundQuant :: Logic.Pol -> Num -> Quant
boundQuant pol n0 number (cn',gender) role = do
      x <- getFresh
      modify (pushNP (Descriptor False gender Plural role) (pureVar x number (cn',gender)))
      -- modify (pushDefinite cn' x)
      return (\vp' extraObjs -> Quant n' pol x (noExtraObjs (cn' (Var x))) (vp' (Var x) extraObjs))
  where n' = case n0 of
          Cardinal n -> (AtLeast n)
          AFew -> Few
          _ -> error ("atLeastQuant: unexpected number: " ++ show n0)

atLeastQuant :: Num -> Quant
atLeastQuant = boundQuant Pos

atMostQuant :: Num -> Quant
atMostQuant = boundQuant Neg


every_Det :: Det
every_Det = (Unspecified,every_Quant)

each_Det :: Det
each_Det = (Unspecified,every_Quant)

somePl_Det :: Det
somePl_Det = (Plural,indefArt)

someSg_Det :: Det
someSg_Det = (Singular,indefArt)

several_Det :: Det
several_Det = (Plural,several_Quant)

many_Det :: Det
many_Det = (Plural,eTypeQuant (Quant Many Pos))

few_Det :: Det
few_Det = (AFew,eTypeQuant (Quant Few Neg))

a_few_Det :: Det
a_few_Det = (AFew,eTypeQuant (Quant Few Pos))

a_lot_of_Det :: Det
a_lot_of_Det = (Plural,eTypeQuant (Quant Lots Pos))

both_Det :: Det
both_Det = (Cardinal 2, bothQuant)

neither_Det :: Det
neither_Det = (Cardinal 2, neitherQuant)

anySg_Det :: Det
anySg_Det = each_Det

----------------------------
-- Comp

type Comp' = Object -> Prop
type Comp = Dynamic Comp'

useComp :: Comp -> VP
useComp c = do
  c' <- c
  return (\x _extraObjs -> c' x)

-- | be a thing given by the CN
compCN :: CN -> Comp
compCN cn = do
  (cn',_gender) <- cn
  return (\x -> noExtraObjs (cn' x))

compAP :: AP -> Comp
compAP ap = do
  a' <- ap
  return $ \x -> noExtraObjs (a' (const TRUE) x) 

compNP :: NP -> Comp
compNP np = do
  np' <- interpNP np Other
  return $ \x -> noExtraObjs (np' (\y -> (mkRel2 "EQUAL" x y)))

(===) :: Exp -> Exp -> Exp
x === y = Con "EQUAL" `apps` [x,y]


compAdv :: Adv -> Comp
compAdv adv = do
  adv' <- adv
  return $ \x -> noExtraObjs (adv' (beVerb x))

beVerb :: VP'
beVerb y = appArgs "_BE_" [y]

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
  return $ \x  -> (apConj2 conj (onS' pol1 (vp1' x)) (onS' pol2 (vp2' x)))

---------------------------
-- VV


lexemeVV :: String -> VV
lexemeVV vv = return $ \vp x -> appArgs vv [lam (\subj -> noExtraObjs (vp subj) ), x]

---------------------------
-- VP
type VP' = (Object -> S')
-- type VP' = (({-subjectClass-} Object -> Prop) -> Object -> Prop) -- in Coq
type VP = Dynamic VP'

complVQ :: VQ -> QS -> VP
complVQ = id

progrVPa :: VP -> VP
progrVPa = id -- ignoring tense

complVV :: VV -> VP -> VP
complVV vv vp = vv <*> vp

doesTooVP :: VP
doesTooVP = do
  vps <- gets vpEnv
  vp :: VP <- case vps of
    [] -> return (assumedPred "assumedVP")
    h:hs -> afromList (h:hs)
  protected $ sloppily vp

elliptic_VP :: VP
elliptic_VP = doesTooVP


-- | Passive
passV2s :: V2 -> VP
passV2s v2 = do
  v2' <- v2
  x <- getFresh; return $ \object eos -> Exists x true (v2' object (Var x) eos) -- alternative with quantifier
  -- return $ \object -> (v2' meta object)

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
  return (\x -> adv' (vp' x))

advVP :: VP -> Adv -> VP
advVP vp adv = do
  vp' <- vp
  adv' <- adv
  modify (pushVP (advVP vp adv))
  return (adv' . vp')

useV :: V -> VP
useV v = do
  modify (pushVP (useV v))
  v

complVS :: VS -> S -> VP
complVS vs s = do
  vs' <- vs
  s' <- s
  modify (pushVP (complVS vs s))
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
  return $ \directObject subject -> np' $ \indirectObject -> v' indirectObject directObject subject

slash3V3 :: V3 -> NP -> VPSlash
slash3V3 v np = do
  v' <- v
  np' <- interpNP np Other
  return $ \indirectObject subjectClass -> np' $ \directObject -> v' indirectObject directObject subjectClass

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

impersCl :: VP -> Cl
impersCl vp = do
  vp' <- vp
  return (vp' (Con "IMPERSONAL"))
  
existNP :: NP -> Cl
existNP np = do
  np' <- interpNP np Other
  return $ (np' beVerb)

predVP :: NP -> VP -> Cl
predVP np vp = withClause $ do
  np' <- interpNP np Subject
  vp' <- vp
  modify (pushS (predVP np vp))
  return (np' vp')

questCl :: Cl -> Cl
questCl = id

sloppily :: Dynamic a -> Dynamic a
sloppily (Dynamic x) = Dynamic (withStateT (\Env{..} -> Env{envSloppyFeatures = True,..}) x)
-- sloppily = id

soDoI :: NP -> Cl
soDoI np = predVP np doesTooVP

elliptic_Cl :: Cl
elliptic_Cl = do
  cl <- gets sEnv
  cl

---------------------
-- RCl

emptyRelSlash :: ClSlash -> RCl
emptyRelSlash c = do
  c' <- c
  return (\x -> noExtraObjs (c' x))

relSlash :: RP -> ClSlash -> RCl
relSlash _rpIgnored cl = emptyRelSlash cl

strandRelSlash :: RP -> ClSlash -> RCl
strandRelSlash _rp cl = emptyRelSlash cl

-- Not found anywhere in fracas
-- relA2 :: RP -> A2 -> NP -> RCl
-- relA2 _ a2 np = do
--   a2' <- a2
--   MkNP n q c@(cn',_gender) <- np
--   np' <- q n c Other
--   return (\x -> noExtraObjs (np' (\y _extraObjs -> a2' (nos cn') x y)))


relV2 :: RP -> V2 -> NP -> RCl
relV2 _ v2 np = do
  v2' <- v2
  np' <- interpNP np Other
  return (\x -> noExtraObjs (np' (flip v2' x)))

relVP :: RP -> VP -> RCl
relVP _ vp = do
  vp' <- vp
  return (\x -> noExtraObjs (vp' x))


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

andSg_Conj :: Conj
andSg_Conj = and_Conj

or_Conj :: Conj
or_Conj = RightAssoc (∨)

either7or_DConj :: Conj
either7or_DConj = EitherOr

comma_and_Conj :: Conj
comma_and_Conj = RightAssoc (∧)

if_comma_then_Conj :: Conj
if_comma_then_Conj = RightAssoc (-->)

apConj2 :: Conj -> S' -> S' -> S'
apConj2 conj p q extras = case conj of
  RightAssoc c -> c (p extras) (q extras)
  EitherOr -> (p extras ∧ not' (q extras)) ∨ (not' (p extras) ∧ (q extras))

apConj3 :: Conj -> S' -> S'-> S'-> S'
apConj3 conj p q r e = case conj of
  RightAssoc c -> (p e `c` q e) `c` r e
  EitherOr -> (p e ∧ not' (q e) ∧ not' (r e)) ∨ (not' (p e) ∧ (q e) ∧ not' (r e)) ∨ (not' (p e) ∧ not' (q e) ∧ (r e))


----------------------------------
-- PConj

type PConj = Conj

and_PConj :: PConj
and_PConj = and_Conj
but_PConj :: PConj
but_PConj = and_Conj
that_is_PConj :: PConj
that_is_PConj = and_Conj


----------------------
-- RS

useRCl :: Temp->Pol->RCl->RS
useRCl temp pol r = do
  r' <- r
  return $ \x -> temp (pol (r' x))

--------------------
-- S

advS :: Adv -> S -> S
advS = extAdvS

extAdvS :: Adv -> S -> S
extAdvS adv s = do
  adv' <- adv
  s' <- s
  return $ adv' s'


useCl :: Temp -> Pol -> Cl -> S
useCl = \temp pol cl -> onS' temp <$> (onS' pol <$> cl) -- FIXME: the polarity should apply to the vp.

useQCl :: Temp -> Pol -> QCl -> QS
useQCl = useCl

conjS2 :: Conj -> S -> S -> S
conjS2 c s1 s2 = apConj2 c <$> s1 <*> s2

predVPS :: NP -> VPS -> S
predVPS np vp = withClause $ do
  np' <- interpNP np Subject
  vp' <- vp
  return (np' vp')

--------------------
-- QS

type QCl = Cl
type QS = S

conjQS2 :: Conj -> QS -> QS -> QS
conjQS2 = conjS2

questVP :: NP -> VP -> QCl
questVP = predVP



--------------------
-- Phr
data Phr = Sentence S | Adverbial Adv | PAdverbial Conj Adv | PNounPhrase Conj NP

sentence :: S -> Phr
sentence = Sentence

question :: S -> Phr
question s = Sentence $ do
  _ <- s
  (return $ \_ -> TRUE) -- not sure about "TRUE" (but we keep the effects! so we know what we're talking about)

pSentence :: PConj -> S -> Phr
pSentence _ x = Sentence x

adverbial :: Adv -> Phr
adverbial = Adverbial

pAdverbial :: Conj -> Adv -> Phr
pAdverbial = PAdverbial

pNounphrase :: Conj -> NP -> Phr
pNounphrase = PNounPhrase

phrToS :: Phr -> S
phrToS p = case p of
  Sentence s -> s
  _ -> return $ \_ -> TRUE

phrToEff :: Phr -> Effect
phrToEff p = noExtraObjs <$> phrToS p

infixl ###
(###) :: Phr -> Phr -> Phr
x ### Sentence s = Sentence $ do
  x' <- phrToS x
  s' <- s
  return (\extraObjs -> noExtraObjs x' ∧ s' extraObjs)
x ### (Adverbial adv) = Sentence $ do
  x' <- phrToS x
  adv' <- adv
  return (adv' x')
  -- Sentence (extAdvS adv (phrToEff x))
  -- FIXME: the adverbs should be pushed to the VP. It should be
  -- possible to do that on the semantics (modify the predicate)
x ### (PAdverbial conj adv) = Sentence $ do
  x' <- phrToS x
  adv' <- adv
  return (apConj2 conj x' (adv' x'))
  -- FIXME: the adverbs should be pushed to the VP. It should be
  -- possible to do that on the semantics (modify the predicate)
x ### (PNounPhrase conj np) = Sentence $ do
  x' <- phrToS x
  y' <- predVP np doesTooVP
  return (apConj2 conj x' y')

-------------------------
-- Quant

type Quant' = (Num -> CN' -> Role -> Dynamic NP')
type Quant = Quant'

possPron :: Pron -> Quant
possPron np number cn role = genNP np number cn role

no_Quant :: Quant
no_Quant num cn role = do
  q <- every_Quant num cn role
  return $ \vp' -> q (\x -> onS' not' (vp' x))

universal_Quant :: Pol -> Quant
universal_Quant pol number (cn',gender) role = do
  x <- getFresh
  dPluralizable <- gets envPluralizingQuantifier
  modify $ \Env {..} -> Env {envPluralizingQuantifier = True,..}
  modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
  modify (pushDefinite cn' x)
  return $ \vp' eos -> (Forall x (noExtraObjs (cn' (Var x))) (pol (vp' (Var x) eos)))

every_Quant :: Quant
every_Quant = universal_Quant id

none_Quant :: Quant
none_Quant = universal_Quant (not')

some_Quant :: Quant
some_Quant = \number (cn',gender) role -> do
  x <- getFresh
  dPluralizable <- gets envPluralizingQuantifier
  modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
  return (\vp' eos -> Exists x (noExtraObjs (cn' (Var x))) (vp' (Var x) eos))

eType :: ([Char] -> Prop -> Exp -> Exp) -> [Char] -> Var -> (Exp -> S') -> (Exp -> t -> Exp) -> t -> Exp
eType quant x z cn' vp' eos = quant x (nos cn' (Var x)) (vp' (Var x) eos) ∧ Forall z ((nos cn' (Var z)) ∧ (vp' (Var z) eos)) true

nos :: (t -> S') -> t -> Prop
nos f a = noExtraObjs (f a)

most_Quant :: Quant
most_Quant = eTypeQuant MOST

several_Quant :: Quant
several_Quant = eTypeQuant SEVERAL

eTypeQuant :: ([Char] -> Prop -> Exp -> Exp) -> Quant
eTypeQuant q number (cn',gender) role = do
  x <- getFresh
  z <- getFresh
  modify (pushNP (Descriptor False gender Plural role) (pureVar z number (cn',gender)))
  return (eType q x z cn') 

indefArt :: Quant
indefArt (MoreThan n) cn role = atLeastQuant n n cn role
indefArt number (cn',gender) role = do
  x <- getFresh
  dPluralizable <- gets envPluralizingQuantifier
  modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
  modify (pushDefinite cn' x)
  return (\vp' eos -> Exists x (nos cn' (Var x)) (vp' (Var x) eos))


-- | Definite which looks up in the environment.
defArt :: Quant
defArt number (cn',gender) role = do
  it <- getDefinite (cn',gender) 
  -- note that here we push the actual object (it seems that the strict reading is preferred in this case)
  -- return (\vp' -> them $ \y -> Exists x (cn' (Var x) ∧ possess y (Var x)) (vp' (Var x))) -- Existence is another possibility (harder to work with)
  _ <- pureNP False it gender number role
  return $ \vp' -> vp' it


genNP :: NP -> Quant
genNP np _number (cn',_gender) _role = do
  them <- interpNP np Other -- only the direct arguments need to be referred by "self"
  x <- getFresh
  return (\vp' -> them $ \y extraObjects -> Exists x (possess y (Var x) ∧ nos cn' (Var x)) (vp' (Var x) extraObjects))

possess :: Object -> Object -> Prop
possess x y = noExtraObjs (mkRel2 "have_V2" y x) -- possesive is sometimes used in another sense, but it seems that Fracas expects this.

of_ :: (Object -> Prop) -> Object -> Object
of_ cn owner = The (lam $ \x -> possess owner x ∧ cn x)

the_other_Q :: Quant
the_other_Q _number _cn _role = return $ \vp eos -> apps (Con "theOtherQ") [lam $ \x -> vp x eos]

-------------------------
-- Predet

just_Predet :: Predet
just_Predet = exactly_Predet

most_of_Predet :: Predet
most_of_Predet (MkNP n _q cn) = MkNP n most_Quant cn

most_Predet :: Predet
most_Predet (MkNP n _q cn) = MkNP n most_Quant cn

at_least_Predet :: Predet
at_least_Predet (MkNP numb _q cn) = MkNP numb (atLeastQuant numb) cn

at_most_Predet :: Predet
at_most_Predet (MkNP numb _q cn) = MkNP numb (atMostQuant numb) cn

all_Predet :: Predet
all_Predet  (MkNP n _q cn) = MkNP n every_Quant cn

only_Predet :: Predet
only_Predet = exactly_Predet

exactly_Predet :: Predet
exactly_Predet (MkNP n _q cn) = MkNP n exactlyQuant cn where

exactlyQuant :: Num -> (Object -> S', [Gender]) -> Role -> Dynamic NP'
exactlyQuant number@(Cardinal n') (cn',gender) role = do
      x <- getFresh
      dPluralizable <- gets envPluralizingQuantifier
      modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
      return (\vp' extraObjs -> Quant (Exact n') Both x (nos cn' (Var x)) (vp' (Var x) extraObjs))

bothQuant :: Quant
bothQuant _ (cn',_gender) _role = do
  x <- getFresh
  y <- getFresh
  -- FIXME: this interpretation is incoherent with anaphora.
  return $ \vp' extraObjs -> Exists x (nos cn' (Var x)) $ Exists y (nos cn' (Var y)) $ vp' (Var x) extraObjs ∧ vp' (Var y) extraObjs ∧ not' (Var x === Var y)


neitherQuant :: Quant
neitherQuant n cn role = do
  r <- bothQuant n cn role
  return $ \vp -> r (\x -> not' . vp x)

------------------------
--

type IAdv = Cl -> QCl


questIAdv :: IAdv -> Cl -> QCl
questIAdv = id

why_IAdv :: IAdv
why_IAdv cl = do
  cl' <- cl
  return (\extraObjs -> Con "WHY" `apps` [cl' extraObjs])

------------------------
-- VQ

type VQ = QS -> VP

know_VQ :: VQ
know_VQ qs = do
  qs' <- qs
  return $ \x _extraObjs -> Con "knowVQ" `apps` [noExtraObjs qs',x]

noExtraObjs :: S' -> Prop
noExtraObjs f = f ([],id)
------------------
-- Additional combinators


{-

himNP :: NP
himNP = pron (all' [isMale, isSingular, isNotSubject])

herNP :: NP
herNP = pron (all' [isFemale, isSingular, isNotSubject])

themSingNP :: NP -- as in everyone owns their book 
themSingNP = pron (all' [isSingular, isNotSubject])

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

negation :: Effect -> Effect
negation x = not' <$> x

-- pushes itself in the env for reference


pureCN2 :: (Object -> Type) -> Gender -> Num -> CN2
pureCN2 v gender number = do
  modify (pushCN2 (pureCN2 v gender number))
  return (v,gender,number)

pureEval :: Effect -> Exp
pureEval = extendAllScopes . repairFields . _TRUE

eval :: Effect -> IO ()
eval = print . pureEval

everyone :: NP
everyone = every (pureCN (constant "PERSON") Unknown Singular)

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

thatOf :: NP -> NP
thatOf x role = do
  cn2 <- gets getCN2
  the (cn2 `_of` x) role

suchDet :: CN -> NP
suchDet (cn) role = do
  ap <- gets apEnv
  ap' <- ap
  x <- getFresh
  (cn',gender,number) <- cn
  modify (pushNP (Descriptor gender number role) (pureVar x))
  return $ \vp' -> (Forall x (ap' cn') (vp' (Var x)))


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

andVP :: VP -> VP -> VP
andVP np1 np2 = do
  np1' <- np1
  np2' <- np2
  return (\x -> np1' x ∧ np2' x)



-}

_TRUE :: Effect -> Prop
_TRUE e = foldr (∨) FALSE (allInterpretations e)

-- _ENV :: Effect -> Env
-- _ENV x = execState x assumed

------------------------
-- Fracas overrides

membersOfTheComittee :: NP
membersOfTheComittee = (detCN (detQuant (genNP (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "committee_N")))) (numPl)) (useN (lexemeN "member_N")))

chairman_etc :: NP
chairman_etc = detCN (detQuant (indefArt) (numSg)) (relCN (useN (lexemeN "chairman_N")) (relV2 implicitRP (lexemeV2 "appoint_V2") membersOfTheComittee))

s_122_4_h_ALT :: Phr
s_122_4_h_ALT = (sentence (useCl (present) (pPos) (predVP (detCN (every_Det) (useN (lexemeN "committee_N"))) (complSlash (slashV2a (lexemeV2 "have_V2")) chairman_etc ))))


s_155_2_p_ALT :: Phr
s_155_2_p_ALT = (sentence (useCl (present) (pPos) (predVP (usePN (lexemePN "bill_PN")) (complSlash (slashV2a (lexemeV2 "own_V2")) oneToo))))

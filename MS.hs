{-# LANGUAGE ViewPatterns #-}
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
import LogicB ()
import qualified Logic
import Data.List (intersect,nub)
-- import Control.Monad.Logic hiding (ap)
import Control.Applicative
import Control.Applicative.Alternative
import Dynamic
import Control.Monad.Reader (asks)
-------------------
-- "PureX"
genderedN :: String -> [Gender] -> CN
genderedN s gender =
  do modify (pushCN (genderedN s gender))
     return (mkCN s gender)

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

class IsAdj a where
  fromAdj :: String -> a

instance IsAdj A' where
  fromAdj a = (\cn obj -> appAdjArgs a [lam cn,obj])

newtype GradableA = GradableA String
instance IsAdj GradableA where
  fromAdj = GradableA

lexemeA :: IsAdj a => String -> Dynamic a
lexemeA a = return $ fromAdj a

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

type RP = ()
lexemeRP :: String -> RP
lexemeRP _ = ()

idRP :: RP
idRP = ()

implicitRP :: RP
implicitRP = ()

---------------------
-- Unimplemented categories

conditional,future,pastPerfect,past,present,presentPerfect :: Temp
past = Past
present = Present
presentPerfect = PresentPerfect
pastPerfect = PastPerfect
future = Future
conditional = Conditional

------------------
-- Pol

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

-- less_than_AdN :: AdN
-- less_than_AdN = LessThan

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


positA :: A -> A
positA = id

--------------
-- A2

type A2' = Object -> (Object -> Prop) -> Object -> S'
type A2 = Dynamic A2'

lexemeA2 :: String -> A2
lexemeA2 a = return $ \x cn y ExtraArgs{..} -> (Con a `apps` [x,lam cn,y],extraTime)

--------------------
-- AP


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
  return $ \cn x -> (np' (\y -> a2' x cn y))

adAP :: AdA -> AP -> AP
adAP ada a = do
  ada' <- ada
  a' <- a
  return $ ada' a'

comparA :: Dynamic GradableA -> NP -> AP
comparA a np = do
  GradableA a' <- a
  np' <- interpNP np Other
  return $ \cn' x -> np'
          (\ y ExtraArgs{..} -> (Con "compareGradableMore" `apps` [Con a',lam cn',x,y],extraTime))

comparAsAs :: Dynamic GradableA -> NP -> AP
comparAsAs a np = do
  GradableA a' <- a
  np' <- interpNP np Other
  return $ \cn' x -> np' (\ y ExtraArgs{..} -> (Con "compareGradableEqual" `apps` [Con a',lam cn',x,y],extraTime))

-- FIXME: very questionable that this should even be in the syntax.
useComparA_prefix :: A -> AP
useComparA_prefix a = do
  a' <- a
  return $ \cn' x -> a' cn' x


--------------------
-- Subjs
type Subj = Cl' -> Adv

lexemeSubj :: String -> Subj
lexemeSubj "before_Subj" s1 = do
  return $ \s2 extraObjs ->
      let (s1',t1) = s1 extraObjs
          (s2',t2) = s2 extraObjs
      in (s1' ∧ s2' ∧ (Con "LessThanTime" `apps` [temporalToLogic t1,temporalToLogic t2]), t2)
lexemeSubj s s1 = do
  return $ \s2 extraObjs -> 
    let (s1',_) = s1 extraObjs
        (s2',t2) = s2 extraObjs
    in (Con s `apps` [s1',s2'], t2)

--------------------
-- AdA

type AdA  = Dynamic (A' -> A')
 
lexemeAdA :: String -> AdA
lexemeAdA ada = return $ \a cn x extraObjs ->
  (Con ada `apps` [lam $ \cn2 -> lam $ \x2 -> snd (a (app cn2) x2 extraObjs),lam cn,x])

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
lexemeAdv "year_1996_Adv" = return $ usingTime (IntervalTime "(ATTIME Year_1996)")
lexemeAdv "since_1992_Adv" = return $ usingTime (IntervalTime "(SINCE Year_1992)")
lexemeAdv "in_1993_Adv" = return $ usingTime (IntervalTime "(ATTIME Year_1993)")
lexemeAdv adv = return $ sentenceApplyAdv (appAdverb adv)

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
  s' <- s
  subj s'


--------------------
-- CN

useN :: N -> CN
useN = id

combineGenders :: [Gender] -> [Gender] -> [Gender]
combineGenders g1 g2 = case intersect g1 g2 of
  [] -> [Neutral]
  i -> i

conjCN2 :: Conj -> CN -> CN -> CN
conjCN2 _c cn1 cn2 = do
  (c1,g1) <- cn1
  (c2,g2) <- cn2
  -- NOTE: the only meaningful conjuctions to use between CNs are 'and' or 'or'.
  -- However, both of them the same thing. ("Or"). See FraCas 87 -- 89.
  return (\x -> apConj2 or_Conj (c1 x) (c2 x),combineGenders g1 g2)

relCN :: CN->RS->CN
relCN cn rs = do
  (cn',gender) <- cn
  rs' <- rs
  return $ (\x eos -> (cn' x eos ∧ rs' x) , gender)
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
  return $ (\x eos -> (noExtraObjs (a' (flip cn' eos) x)),gendr)

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
  return $ (\x extraObjs -> (apps (Con "SentCN") [lam (fst . flip cn' extraObjs),lam (nos sc'),x],snd (cn' x extraObjs)),gender)

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
  (cn',gender) <- elliptic_CN
  return $ MkNP [] Singular indefArt cn' gender

interpNP :: NP -> Role -> Dynamic NP'
interpNP np role = do
  np' <- np
  evalNPData np' role

evalNPData :: NPData -> Role -> Dynamic NP'
evalNPData (MkNP pre n q c gender) = evalQuant pre q n (c,gender)

elliptic_NP_Sg :: NP
elliptic_NP_Sg = qPron $ all' [isSingular]

usePN ::  PN -> NP
usePN (o,g,n) = pureNP False (app (Con (parens ("PN2Class " ++ o)))) (Con (parens ("PN2object " ++ o))) g n Subject -- FIXME: role

pureNP :: Bool -> (Object -> Prop) -> Object -> [Gender] -> Num -> Role -> NP
pureNP dPluralizable cn o dGender dNum dRole = do
  modify (pushNP (Descriptor{..}) (pureNP dPluralizable cn o dGender dNum dRole))
  return $ MkNP [] dNum (ObjectQuant o) (\x _extraObjs -> cn x) dGender

massNP :: CN -> NP
massNP cn = do
  (cn',gender) <- cn
  return $ MkNP [] Singular some_Quant cn' gender

detCN :: Det -> CN -> NP
detCN (num,quant) cn = do
  (cn',gender) <- cn
  return (MkNP [] num quant cn' gender)

usePron :: Pron -> NP
usePron = id

advNP :: NP -> Adv -> NP
advNP np adv = do
  MkNP pre num1 q1 cn1 gender1 <- np
  adv' <- adv
  return $ MkNP pre num1
           (ObliviousQuant $ \num' (cn',gender) role -> do
               p1 <- evalQuant pre q1 num' (adv' . cn',gender) role
               return $ \vp -> p1 vp) 
           (cn1,gender1)

predetNP :: Predet -> NP -> NP
predetNP f np = do
  MkNP pre n q cn g <- np
  return $ MkNP (f:pre) n q cn g

-- FIXME: WTF?
detNP :: Det -> NP
detNP (number,quant) =
  return (MkNP [] number quant (const (const TRUE) {- fixme -}) [Male,Female,Neutral])


pPartNP :: NP -> V2 -> NP  -- Word of warning: in FraCas partitives always behave like intersection, which is probably not true in general
pPartNP np v2 = do
  MkNP pre num q cn gender <- np
  v2' <- v2
  subject <- getFresh
  return $ MkNP pre num q ((\x eos -> (cn x eos)  ∧ Exists subject true (noExtraObjs (v2' x (Var subject))))) gender

relNPa :: NP -> RS -> NP
relNPa np rs = do
  MkNP pre num q cn gender <- np
  rs' <- rs
  return $ MkNP pre num q (\x eos -> cn x eos ∧ rs' x) gender


conjNP2 :: Conj -> NP -> NP -> NP
conjNP2 c np1 np2 = do
  MkNP pre1 num1 q1 cn1 gender1 <- np1
  MkNP pre2 num2 q2 cn2 gender2 <- np2
  modify (pushNP (Descriptor False (nub (gender1 ++ gender2)) Plural Other) (conjNP2 c np1 np2))
  return $ MkNP [] (num1) {- FIXME add numbers? min? max? -}
                (ObliviousQuant $ \_num _cn role -> do
                    p1 <- evalQuant pre1 q1 num1 (cn1,gender1) role
                    p2 <- evalQuant pre2 q2 num2 (cn2,gender2) role
                    return $ \vp -> apConj2 c (p1 vp) (p2 vp))
                (\x eos -> cn1 x eos ∨ cn2 x eos)  -- FIXME: problem 128, etc.
                gender1

conjNP3 :: Conj -> NP -> NP -> NP -> NP
conjNP3 c np1 np2 np3 = do
  MkNP pre1 num1 q1 cn1 gender1 <- np1
  MkNP pre2 num2 q2 cn2 gender2 <- np2
  MkNP pre3 num3 q3 cn3 gender3 <- np3
  return $ MkNP [] (num1) {- FIXME add numbers? min? max? -}
                (ObliviousQuant $ \_num _cn role -> do
                    p1 <- evalQuant pre1 q1 num1 (cn1,gender1) role
                    p2 <- evalQuant pre2 q2 num2 (cn2,gender2) role
                    p3 <- evalQuant pre3 q3 num3 (cn3,gender3) role
                    return $ \vp -> apConj3 c (p1 vp) (p2 vp) (p3 vp))
                (\x eos -> cn1 x eos ∨ cn2 x eos ∨ cn3 x eos, gender1)


----------------------
-- Pron


qPron :: ObjQuery -> Pron
qPron q = do
  (isSloppy :: Bool) <- asks envSloppyFeatures
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
someone_Pron = return $ MkNP [] Singular indefArt (mkPred' "person_N") [Male,Female]

maximallySloppyPron :: Pron
maximallySloppyPron = qPron $ const True

everyone_Pron :: Pron
everyone_Pron = return $ MkNP [] Unspecified every_Quant (mkPred' "person_N") [Male,Female]

no_one_Pron :: Pron
no_one_Pron = return $ MkNP [] Unspecified none_Quant (mkPred' "person_N") [Male,Female]

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
one_or_more_Det = (Unspecified,BoundQuant Pos 1)

another_Det :: Det
another_Det = (Cardinal 1, ObliviousQuant anotherQuant')

detQuant :: Quant -> Num -> Det
detQuant q n = (n,q)

detQuantOrd :: Quant->Num->Ord->Det
detQuantOrd q n _o = (n,q) -- FIXME: do not ignore the ord


every_Det :: Det
every_Det = (Unspecified,every_Quant)

each_Det :: Det
each_Det = (Unspecified,every_Quant)

somePl_Det :: Det
somePl_Det = (Plural,ExistQuant)

someSg_Det :: Det
someSg_Det = (Singular,ExistQuant)

several_Det :: Det
several_Det = (Plural,several_Quant)

many_Det :: Det
many_Det = (Plural,ETypeQuant (Quant Many Pos))

few_Det :: Det
few_Det = (AFew,ETypeQuant (Quant Few Neg))

a_few_Det :: Det
a_few_Det = (AFew,ETypeQuant (Quant Few Pos))

a_lot_of_Det :: Det
a_lot_of_Det = (Plural,ETypeQuant (Quant Lots Pos))

both_Det :: Det
both_Det = (Cardinal 2, ObliviousQuant bothQuant')

neither_Det :: Det
neither_Det = (Cardinal 2, ObliviousQuant neitherQuant')

anySg_Det :: Det
anySg_Det = each_Det

----------------------------
-- Comp

type Comp' = (Object -> Prop) -> Object -> S'
type Comp = Dynamic Comp'

useComp :: Comp -> VP
useComp c = do
  c' <- c
  return $ \x extraObjs@ExtraArgs{..} ->
    case extraCompClass of
      Default -> c' (const TRUE) x extraObjs
      Explicit xClass -> c' (\y -> xClass y extraObjs) x extraObjs

-- | be a thing given by the CN
compCN :: CN -> Comp
compCN cn = do
  (cn',_gender) <- cn
  return (\_xClass x extraObjs ->  (cn' x extraObjs,now))

compAP :: AP -> Comp
compAP ap = do
  a' <- ap
  return $ \xClass x extraObjs -> (a' xClass x) extraObjs

compNP :: NP -> Comp
compNP np = do
  np' <- interpNP np Other
  return $ \_xClass x extraObjs -> (np' (\y -> (mkRel2 "EQUAL" x y))) extraObjs

(===) :: Exp -> Exp -> Exp
x === y = noExtraObjs (mkRel2 "EQUAL" x y)


compAdv :: Adv -> Comp
compAdv adv = do
  adv' <- adv
  return $ \_xClass x extraObjs -> adv' (beVerb x) extraObjs

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
  x <- getFresh
  return $ \object eos -> let (p,t) = (v2' object (Var x) eos) in (Exists x true p,t)  -- alternative with quantifier
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
advVP = advVPPush False -- FIXME! (Should be True but gives infinitely many interpretations for Fracas 267)

advVPPush :: Bool -> VP -> Adv -> VP
advVPPush doPush vp adv = do
  vp' <- vp
  adv' <- adv
  when doPush (modify (pushVP (advVPPush False vp adv))) -- attempt to avoid infinitely many interpretations
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
  MkNP pre n q cn gender <- np
  np' <- evalQuant pre q n (cn,gender) Subject
  vp' <- vp
  let p' = np' vp'
  tense <- asks envTense
  t <- case tense of
    Past -> do
      ts <- referenceTimesFor p' -- (1)
      -- fixme: this should happen at a lower level (lexical
      -- item). But we do not have dynamic access to arguments at that
      -- level at the moment so this will do temporarily.
      -- Why? Because events could refer to occurences inside a quantifier:
      -- Example "every boy climbed and fell after they climbed."
      case ts of
        [] -> ExactTime <$> freshTime (Con "Past" `app`)
        -- not a reference to a previous event. Allocate own
        -- time. This time MUST be overridable, otherwise we'll never
        -- be able to override it, to search for it when we reach
        -- point (1) at a later occurence of the same event.
        (t:_) -> return (ExactTime t)
    _ -> return now -- FIXME: other tenses
  modify (pushFact $ noExtraObjs (usingTime t p'))
  modify (pushS (predVP np vp))
  return $ usingCompClass cn (np' vp')

questCl :: Cl -> Cl
questCl = id


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
either7or_DConj = or_Conj -- this is what FraCas 346 seems to say. (And no other example contradicts it.)

comma_and_Conj :: Conj
comma_and_Conj = RightAssoc (∧)

if_comma_then_Conj :: Conj
if_comma_then_Conj = RightAssoc (-->)

apConj2 :: Conj -> S'' -> S'' -> S''
apConj2 conj p q extras = case conj of
  RightAssoc c -> c (p extras) (q extras)
  EitherOr -> (p extras ∧ not' (q extras)) ∨ (not' (p extras) ∧ (q extras))

apConj3 :: Conj -> S'' -> S''-> S''-> S''
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
then_PConj :: Conj
then_PConj = and_Conj


----------------------
-- RS

useRCl :: Temp->Pol->RCl->RS
useRCl _temp pol r = do
  r' <- r
  -- t <- interpTense temp -- FIXME: take tense into account
  -- FIXME: the polarity should apply to the vp depending on the wide/narrow character of the quantifier
  return $ \x ->  (pol (r' x))

--------------------
-- S

advS :: Adv -> S -> S
advS = extAdvS

extAdvS :: Adv -> S -> S
extAdvS adv s = do
  adv' <- adv
  s' <- s
  return $ (adv' s')


-- PROBLEM: this happens at the wrong level.
useCl :: Temp -> Pol -> Cl -> S
useCl temp pol cl = do
  -- FIXME: the polarity should apply to the vp depending on the wide/narrow character of the quantifier
  onS' pol <$>  withTense temp cl


useQCl :: Temp -> Pol -> QCl -> QS
useQCl = useCl

conjS2 :: Conj -> S -> S -> S
conjS2 c s1 s2 = do
  s1' <- s1
  s2' <- s2
  return $ \extraObjs -> (apConj2 c (fst . s1') (fst . s2') extraObjs, _) -- FIXME: join of times
  -- apConj2 c <$> s1 <*> s2

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
data Phr = Sentence (Dynamic S') | Adverbial Adv | PAdverbial Conj Adv | PNounPhrase Conj NP

sentence :: S -> Phr
sentence x = Sentence (x)

question :: S -> Phr
question s = Sentence $ do
  _ <- s
  (return $ \_ -> TRUE) -- not sure about "TRUE" (but we keep the effects! so we know what we're talking about)

pSentence :: PConj -> S -> Phr
pSentence _ x = sentence x

adverbial :: Adv -> Phr
adverbial = Adverbial

pAdverbial :: Conj -> Adv -> Phr
pAdverbial = PAdverbial

pNounphrase :: Conj -> NP -> Phr
pNounphrase = PNounPhrase

phrToS :: Phr -> Dynamic S'
phrToS p = case p of
  Sentence s -> s
  _ -> return $  \_ -> TRUE

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



possPron :: Pron -> Quant
possPron = PossQuant

-- | given a quantity θ of cn in the env, return, exactly θ cn
-- (In the example, "exactly θ orders")
elliptic_NP_Pl :: NP
elliptic_NP_Pl = do
  (amount,(cn',gender)) <- getQuantity
  return $ MkNP [ExactlyPredet] (Cardinal amount) IndefQuant cn' gender

-- Consider the example "ITEL won more orders than APCOM did"
-- f(x) = AtLeast (x+1)
-- cn = orders
-- s = APCOM <elliptic_VP>
relativeAmountQuant :: Logic.Pol -> (Nat -> Amount) -> CN -> Dynamic S' -> NP
relativeAmountQuant pol f cn s = do
  (cn',gender) <- cn
  threshold <- getFresh -- invent an abstract quantity.
  modify (pushQuantity threshold (cn',gender)) -- priming "ellptic_NP_Pl", so that we find the above quantity
  modify (pushVP (complSlash elliptic_VPSlash elliptic_NP_Pl)) -- in 's', there is an elliptic vp, referring to this
  s' <- s -- in our example: s evaluates to "APCOM <elliptic_VP>", then "APCOM (<elliptic_VPSlash> <elliptic_NP_Pl>)", then "APCOM won exactly θ orders"
  let q :: Quant'
      q _num _cn _role = do
        x <- getFresh
        return (\vp' extraObjs -> noExtraObjs s' ∧ -- "APCOM won exactly θ orders"
                                  Quant (f (Nat (Var threshold))) pol x (cn' (Var x) emptyObjs) (vp' (Var x) extraObjs)) -- Itel won at least θ+1 orders
      -- quantifier that implements "there exists (f threshold)"
  return $ MkNP [] Plural (ObliviousQuant q) cn' gender

moreThanQuant' :: CN -> Dynamic S' -> NP
moreThanQuant' = relativeAmountQuant Pos (\x -> AtLeast (1 + x))

moreThanQuant :: CN -> S -> NP
moreThanQuant = moreThanQuant'


moreThanNPQuant :: CN -> NP -> NP
moreThanNPQuant cn np = do
  cn'@(c,g) <- cn -- cities
  np' <- np -- JP or Athens
  let q :: Quant'
      q _num _cn role = do
        np1 <- evalNPData np' role
        np2 <- boundQuant' Pos (MoreThan (Cardinal 2)) cn' role
        return $ \vp' extraObjs -> np1 vp' extraObjs ∧ np2 vp' extraObjs
  moreThanQuant' (pure cn') (predVP (pure np') elliptic_VP) -- as in FraCas 230-235
          -- example for 1st reading:  Stergios visited more cities than JP.
    <|> return (MkNP [] Plural (ObliviousQuant q) c g)    -- as in FraCas 236-237
          -- example for second reading: Stergios visited more cities than Athens.


nMoreThanNPQuant :: Nat -> CN -> NP -> NP
nMoreThanNPQuant n cn np = do
  relativeAmountQuant Both (\x -> Exact (n + x)) cn (predVP np elliptic_VP)

twiceAsManyAs :: CN -> NP -> NP
twiceAsManyAs cn np = relativeAmountQuant Both (\x -> Exact (x + x)) cn (predVP np elliptic_VP)

no_Quant :: Quant
no_Quant = UniversalQuant not'

every_Quant :: Quant
every_Quant = UniversalQuant id

none_Quant :: Quant
none_Quant = UniversalQuant (not')

some_Quant :: Quant
some_Quant = ExistQuant

most_Quant :: Quant
most_Quant = ETypeQuant MOST

several_Quant :: Quant
several_Quant = ETypeQuant SEVERAL

indefArt :: Quant
indefArt = IndefQuant

defArt :: Quant
defArt = DefiniteQuant
-- | Definite which looks up in the environment.

genNP :: Pron -> Quant
genNP = PossQuant


the_other_Q :: Quant
the_other_Q = TheOtherQuant

-------------------------
-- Predet


just_Predet :: Predet
just_Predet = ExactlyPredet

most_of_Predet :: Predet
most_of_Predet = MostPredet

most_Predet :: Predet
most_Predet = MostPredet

at_least_Predet :: Predet
at_least_Predet = AtLeastPredet

at_most_Predet :: Predet
at_most_Predet = AtMostPredet

all_Predet :: Predet
all_Predet = AllPredet

only_Predet :: Predet
only_Predet = exactly_Predet

exactly_Predet :: Predet
exactly_Predet = ExactlyPredet

------------------------
-- QCl

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
  return $ mkRel2 "knowVQ" (noExtraObjs $ qs') -- stop prepositions from propagating: TODO: other VVs  (say, etc.)

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
_TRUE e = foldr (∨) FALSE (evalDynamic e)

-- _ENV :: Effect -> Env
-- _ENV x = execState x assumed


----------------------
-- Evaluation of (pre) determiners

evalQuant :: [Predet] -> Quant -> Num -> CN' -> Role -> Dynamic NP'
evalQuant _ (ObliviousQuant q) num cn role = q num cn role
evalQuant [AllPredet] (PossQuant pron) num cn role = genNP' Forall pron num cn role -- see FraCas 134
evalQuant [AllPredet] _ num cn role =  universal_Quant' id num cn role
evalQuant [ExactlyPredet] _ (Cardinal num) cn role = exactlyQuant' num cn role
evalQuant [AtLeastPredet] _ num cn role = boundQuant' Pos num cn role
evalQuant [AtMostPredet] _ num cn role = boundQuant' Neg num cn role
evalQuant [MostPredet] _ num cn role = evalQuant [] (ETypeQuant MOST) num cn role
evalQuant [] _ (Cardinal n) cn role = boundQuant' Pos (Cardinal n) cn role
evalQuant [] _ (MoreThan num) cn role = boundQuant' Pos (MoreThan num) cn role  -- FraCas 104
evalQuant [] (BoundQuant p n) _n cn role = boundQuant' p (Cardinal n) cn role
evalQuant [] (ObjectQuant x) _number _cn _role = return $ \vp -> vp x
evalQuant [] (UniversalQuant pol) num cn role = universal_Quant' pol num cn role
evalQuant [] (PossQuant pron) num cn role = genNP' Exists pron num cn role
evalQuant [] IndefQuant Plural cn role@Subject = bothQuant cn role   -- Bare plural, FraCas 097 -- 101
-- Note that the universal reading of a bare plural seem to happen only in subject position. See FraCas 040.
evalQuant [] IndefQuant  num cn role = some_Quant' num cn role
evalQuant [] ExistQuant  num cn role = some_Quant' num cn role
evalQuant [] (ETypeQuant q) num cn role = eTypeQuant q num cn role
evalQuant [] DefiniteQuant Plural cn role = universal_Quant' id Plural cn role
evalQuant [] DefiniteQuant num cn role = defArt' num cn role
evalQuant [] TheOtherQuant  num cn role = the_other_Q' num cn role
evalQuant p _q  num _cn _role = error $ "evalQuant: unsupported combination:" ++ show (p,num)

bothQuant :: CN' -> Role -> Dynamic NP'
bothQuant (cn',gender) role = do -- always Plural
  x <- getFresh
  let dPluralizable = False
  modify (pushNP (Descriptor dPluralizable gender Plural role) (pureVar x Plural (cn',gender)))
  modify (pushDefinite cn' x)
  return $ \vp' eos ->
    let (p,t) = vp' (Var x) eos
    in (Forall x (noExtraObjsCN'' cn' (Var x)) p ∧ Exists x (noExtraObjsCN'' cn' (Var x)) p,t)

universal_Quant' :: Pol -> Quant'
universal_Quant' pol number (cn',gender) role = do
  x <- getFresh
  dPluralizable <- gets envPluralizingQuantifier
  modify $ \Env {..} -> Env {envPluralizingQuantifier = True,..}
  modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
  modify (pushDefinite cn' x)
  return $ \vp' eos ->
    let (p,t) = vp' (Var x) eos
    in  (Forall x (noExtraObjsCN'' cn' (Var x)) (pol p), t)

eType :: LogicQuant -> Var -> Var -> CN'' -> (Object -> S') -> S'
eType quant x z cn' vp' eos =
  let (px,t) = vp' (Var x) eos
      (pz,_) = vp' (Var z) eos
  in (quant x (noExtraObjsCN'' cn' (Var x)) px ∧ Forall z ((noExtraObjsCN'' cn' (Var z)) ∧ pz) true,t)

-- nos :: (t -> S') -> t -> Prop
nos f a = noExtraObjs (f a)

eTypeQuant :: LogicQuant -> Quant'
eTypeQuant q number (cn',gender) role = do
  x <- getFresh
  z <- getFresh
  modify (pushNP (Descriptor False gender Plural role) (pureVar z number (cn',gender)))
  return (eType q x z cn') 

some_Quant' :: Quant'
some_Quant' = \number (cn',gender) role -> do
  x <- getFresh
  dPluralizable <- gets envPluralizingQuantifier
  modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
  modify (pushDefinite cn' x)
  return (\vp' eos -> let (p,t) = (vp' (Var x) eos)
                      in  (Exists x (cn' (Var x) emptyObjs) p,t))

defArt' :: Quant'
defArt' number (cn',gender) role = do
  it <- getDefinite (cn',gender) 
  -- note that here we push the actual object (it seems that the strict reading is preferred in this case)
  -- return (\vp' -> them $ \y -> Exists x (cn' (Var x) ∧ possess y (Var x)) (vp' (Var x))) -- Existence is another possibility (harder to work with)
  _ <- pureNP False (noExtraObjsCN'' cn') it gender number role
  return $ \vp' -> vp' it

genNP' :: (Var -> Type -> Exp -> Exp) -> NP -> Quant'
genNP' quant np _number (cn',_gender) _role = do
  them <- interpNP np Other -- only the direct arguments need to be referred by "self"
  x <- getFresh
  return (\vp' -> them $ \y extraObjects -> 
             let (p,t) = vp' (Var x) extraObjects
             in (quant x (possess y (Var x) ∧ noExtraObjsCN'' cn' (Var x)) p,t))

possess :: Object -> Object -> Prop
possess x y = noExtraObjs (mkRel2 "have_V2" y x) -- possesive is sometimes used in another sense, but it seems that Fracas expects this.

the_other_Q' :: Quant'
the_other_Q' _number _cn _role = return $ \vp eos -> apps (Con "theOtherQ") [lam $ \x -> vp x eos]

exactlyQuant' :: Nat -> (CN'', [Gender]) -> Role -> Dynamic NP'
exactlyQuant' n' (cn',gender) role = do
      x <- getFresh
      dPluralizable <- gets envPluralizingQuantifier
      modify (pushNP (Descriptor dPluralizable gender number role) (pureVar x number (cn',gender)))
      return $ \vp' extraObjs ->
                let (p,t) = vp' (Var x) extraObjs
                in (Quant (Exact n') Both x (noExtraObjsCN'' cn' (Var x)) p,t)
   where number = Cardinal n'

bothQuant' :: Quant'
bothQuant' _ (cn',_gender) _role = do
  x <- getFresh
  y <- getFresh
  -- FIXME: this interpretation is incoherent with anaphora.
  return $ \vp' extraObjs ->
    let (py,ty) = vp' (Var y) extraObjs
        (px,tx) = vp' (Var x) extraObjs
    in (Exists x (noExtraObjsCN'' cn' (Var x)) $ Exists y (noExtraObjsCN'' cn' (Var y)) $ px ∧ py ∧ not' (Var x === Var y),tx) -- FIXME: time???


neitherQuant' :: Quant'
neitherQuant' n cn role = do
  r <- bothQuant' n cn role
  return $ \vp -> r (\x -> not' . vp x)


boundQuant' :: Logic.Pol -> Quant'
boundQuant' pol number (cn',gender) role = do
      x <- getFresh
      modify (pushNP (Descriptor False gender Plural role) (pureVar x number (cn',gender)))
      -- modify (pushDefinite cn' x)
      return (\vp' extraObjs ->
        let (px,tx) = vp' (Var x) extraObjs
        in (Quant n' pol x (noExtraObjsCN'' cn' (Var x)) px,tx))
  where n' = case number of
          Cardinal n -> (AtLeast n)
          MoreThan (Cardinal n) -> (AtLeast (n+1))
          AFew -> Few
          _ -> error ("atLeastQuant: unexpected number: " ++ show number)

anotherQuant' :: Quant'
anotherQuant' number (cn',gender) role = do
          x <- getFresh
          y <- getDefinite (cn',gender)
          dPluralizable <- gets envPluralizingQuantifier
          modify (pushNP (Descriptor dPluralizable gender Plural role) (pureVar x number (cn',gender)))
          return $ \vp extraObjs ->
            let (px,tx) = vp (Var x) extraObjs
            in (Exists x (noExtraObjsCN'' cn' (Var x) ∧ not' (Var x === y)) px,tx)

------------------------



-- np (v2 (moreQuant cn)) `thanSubj` np' didSo
-- The LHS of thanSubj, we interpret as:
-- np (v2 (atLeastQuant (threshold+1))), for threshold fresh.
-- The RHS is interpreted as an elliptic VP:
-- np (v2 (exactlyQuant threshold))

-- moreQuant :: Quant'
-- moreQuant number cn role = do
--   isInRepeat <- gets envSloppyFeatures
--   if isInRepeat
--     then do
--       threshold <- getQuantity
--       exactlyQuant' threshold cn role
--     else do
--       threshold <- getFresh
--       modify (pushQuantity threshold)
--       boundQuant' Pos (MoreThan (Cardinal (Nat (Var threshold)))) cn role




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


s_086_2_h_ALT :: Phr
s_086_2_h_ALT = (sentence (useCl (past) (pPos) (predVP (detCN (detQuant (indefArt) (numCard (numNumeral (n_six)))) (useN (lexemeN "lawyer_N"))) (complSlash (slashV2a (lexemeV2 "sign_V2")) (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "contract_N")))))))

-- s_099_1_p_fixed :: Phr
-- s_099_1_p_fixed = sentence (useCl (past) (pPos) (predVP (detCN (detQuant (defArt) (numPl)) (advCN (useN (lexemeN "client_N")) (prepNP (lexemePrep "at_Prep") (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "demonstration_N")))))) (adVVP (lexemeAdv "all_Adv") (useComp (compAP (complA2 (lexemeA2 "impressed_by_A2") (detCN (detQuant (genNP (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "system_N")))) (numSg)) (useN (lexemeN "performance_N")))))))))

-- s_101_1_p_fixed :: Phr
-- s_101_1_p_fixed = sentence (useCl (present) (pPos) (predVP (detCN (detQuant (indefArt) (numPl)) (useN (lexemeN "university_graduate_N"))) (complSlash (slashV2a (lexemeV2 "make8become_V2")) (detCN (detQuant (indefArt) (numPl)) (adjCN (positA (lexemeA "poor8bad_A")) (useN (lexemeN "stockmarket_trader_N")))))))


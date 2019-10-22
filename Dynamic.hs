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

module Dynamic where

import Prelude hiding (pred,Ord,Num)
import Control.Monad.State hiding (ap)
import Logic hiding (Pol)
import LogicB ()
import qualified Logic
import Data.List (intersect,partition,nubBy,sortBy,find)
import Control.Monad.Logic hiding (ap)
import Control.Applicative
import Data.Function (on)
import Control.Arrow (first)
import Data.Maybe (catMaybes)
import Data.Monoid

type Object = Exp
type Prop = Exp

data Optional a = Default | Explicit a
instance Monoid (Optional a) where
  mempty = Default
  Default `mappend` x = x
  x `mappend` Default = x
  x `mappend` _ = x -- FIXME: issue some warning

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


data Num where
  Unspecified :: Num
  Singular :: Num
  Plural   :: Num
  AFew :: Num
  MoreThan :: Num -> Num
  Cardinal :: Nat -> Num
  deriving (Show,Eq)

onS' :: (Prop -> Prop) -> S' -> S'
onS' f p eos = f (p eos)

data Temporal = ExactTime Exp | IntervalTime String | UnspecifiedTime | TenseTime Temporal deriving Show

instance Monoid Temporal where
  mempty = UnspecifiedTime
  UnspecifiedTime `mappend` x = x
  x `mappend` UnspecifiedTime = x
  TenseTime _ `mappend` x = x -- time specification given by tense, this is overridden by specific times.
  x `mappend` TenseTime _ = x
  x `mappend` y = error ("`mappend Temporal:" ++ show x ++ " <> " ++ show y)

data ExtraArgs = ExtraArgs { extraPreps :: [(Var,Object)] -- prepositions
                           , extraAdvs :: (Object -> Prop) -> Object -> Prop -- adverbs
                           , extraCompClass :: Optional (Object -> S')
                           , extraTime :: Temporal
                           }

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
type VP' = (Object -> S')
-- type VP' = (({-subjectClass-} Object -> Prop) -> Object -> Prop) -- in Coq
type VP = Dynamic VP'

type Cl =  Dynamic S'
type Temp = Tense

data Tense = Conditional | Future | PastPerfect | Past | Present | PresentPerfect

type ClSlash  = Dynamic VP'
type RCl  = Dynamic RCl'
type RCl' = Object -> Prop
type RS  = Dynamic RCl'
type AP = Dynamic A'
type A = Dynamic A'
type A' = (Object -> Prop) -> Object -> S'


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
               ,quantityEnv :: [(Var,CN')] -- map from CN' to "default" quantity.
               ,envDefinites :: [(Exp,Object)] -- map from CN to pure objects
               ,envMissing :: [(Exp,Var)] -- definites that we could not find. A map from CN to missing variables
               ,envSloppyFeatures :: Bool
               ,envPluralizingQuantifier :: Bool
               ,envTimeVars :: [(Exp,Var)]
               ,envFacts :: [Prop]
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
  [] -> [return $ MkNP [] assumedNum (ObjectQuant (constant "assumedNP")) assumedCN]
  xs -> map snd xs

getNP :: ObjQuery -> Dynamic [NP]
getNP q = gets (getNP' q)

getDefinite :: CN' -> Dynamic Object
getDefinite (cn',_gender) = do
  things <- gets envDefinites
  let pred = lam (\x -> (noExtraObjs (cn' x)))
  case find (eqExp' pred . fst) things of
    Just (_,y) -> return y
    Nothing -> do
      y <- getFresh
      modify $ \Env {..} -> Env{envDefinites=(pred,Var y):envDefinites
                               ,envMissing=(pred,y):envMissing,..}
      return (Var y)

getQuantity :: Dynamic (Nat,CN')
getQuantity = do
  qs <- gets quantityEnv
  case qs of
    ((q,cn'):_) -> return (Nat (Var q),cn')

-------------------------------
-- Pushes


pushQuantity :: Var -> CN' -> Env -> Env
pushQuantity v cn Env{..} = Env{quantityEnv=(v,cn):quantityEnv,..}

pushDefinite :: (Object -> S') -> Var -> Env -> Env
pushDefinite source target Env{..} =
  Env{envDefinites = (lam (\x' -> noExtraObjs (source x')),Var target):envDefinites,..}

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

quantifyMany :: [(Exp,Var)] -> Exp -> Exp
quantifyMany [] e = e
quantifyMany ((dom,x):xs) e = Forall x (dom `app` (Var x)) (quantifyMany xs e)

evalDynamic :: Dynamic Exp -> [Exp]
evalDynamic (Dynamic x) = do
  (formula,Env {..}) <- observeAll (runStateT x assumed)
  return $
    quantifyMany [(Lam (\_ -> (Con "Time") :∧ constraint),t) | (constraint,t) <- envTimeVars] $
    quantifyMany [(Lam (\_ -> Con "Nat"),v) | (v,_cn) <- quantityEnv] $
    quantifyMany envMissing formula

newtype Dynamic a = Dynamic {fromDynamic :: StateT Env Logic a} deriving (Monad,Applicative,Functor,MonadState Env,Alternative,MonadPlus,MonadLogic)
instance Show (Dynamic a) where show _ = "<DYNAMIC>"

-- newtype Dynamic a = Dynamic {fromDynamic :: LogicT (State Env) a} deriving (Monad,Applicative,Functor,MonadState Env,Alternative,MonadPlus,MonadLogic)

type Effect = Dynamic Prop

filterKey :: Eq a => a -> [(a, b)] -> [(a, b)]
filterKey k = filter ((/= k) . fst)

mkPred :: String -> Object -> S'
mkPred p x extraObjs = appArgs p [x] extraObjs


mkRel2 :: String -> Object -> Object -> S'
mkRel2 p x y extraObjs = appArgs p [x,y] extraObjs


mkRel3 :: String -> Object -> Object -> Object -> S'
mkRel3 p x y z extraObjs = appArgs p [x,y,z] extraObjs

constant :: String -> Exp
constant x = Con x

pureObj :: Exp -> Num -> CN' -> NP
pureObj x number cn = return $ MkNP [] number (ObjectQuant x) cn

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
               ,quantityEnv = []
               ,cnEnv = []
               ,envDefinites = []
               ,envMissing = []
               ,envSloppyFeatures = False
               ,envPluralizingQuantifier = False
               ,envTimeVars = []
               ,envFacts = []
               ,freshVars = allVars}




numSg,numPl :: Num
numSg = Singular
numPl = Plural

data Predet = JustPredet | MostPredet | AtLeastPredet | AtMostPredet | AllPredet | ExactlyPredet deriving Show

data NPData where
  MkNP :: [Predet] -> Num -> Quant -> CN' -> NPData

type N = CN
type PN = (String,[Gender],Num)

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

any' :: [a -> Bool] -> a -> Bool
any' fs x = any ($ x) fs

instance Show (a -> b) where show _ = "<FUNCTION>"
type Quant' = (Num -> CN' -> Role -> Dynamic NP')
data Quant = PossQuant Pron | UniversalQuant Pol | IndefQuant | ExistQuant | ETypeQuant ([Char] -> Prop -> Exp -> Exp) | DefiniteQuant | TheOtherQuant | ObjectQuant Object | BoundQuant Logic.Pol Nat
  | ObliviousQuant Quant' -- ^ quantifier that ignores numbers and predeterminers.


type Pol = Prop -> Prop

type Pron = NP


--------------------------
-- Extra objects and S'

noExtraObjs :: S' -> Prop
noExtraObjs f = f (ExtraArgs {extraPreps = [], extraAdvs = id, extraTime = mempty, extraCompClass = mempty})

appArgs :: String -> [Object] -> ExtraArgs -> Prop
appArgs nm objs@(_:_) (ExtraArgs {..}) = extraAdvs (app (pAdverbs time'd)) subject
  where prep'd = Con (nm ++ concatMap fst prepositions) `apps` (map snd prepositions ++ indirectObjects)
        time'd = Con "appTime" `apps` [temporalToLogic extraTime,prep'd]
        indirectObjects = init objs
        subject = last objs
        cleanedPrepositions = sortBy (compare `on` fst) $ nubBy ((==) `on` fst) extraPreps
        (adverbialPrepositions,prepositions) = partition ((== "before") . fst) cleanedPrepositions
        pAdverbs x = foldr app x [Con (p ++ "_PREP") `app` arg | (p,arg) <- adverbialPrepositions]



appAdjArgs :: String -> [Object] -> ExtraArgs -> Prop
appAdjArgs nm [cn,obj] (ExtraArgs{..}) = extraAdvs  (\x -> apps prep'd [cn,x]) obj
  where prep'd = Con "appA" `app` (Con (nm ++ concatMap fst prepositions) `apps` ((map snd prepositions)))
        prepositions = nubBy ((==) `on` fst) extraPreps

modifyingPrep :: String -> Object -> S' -> S'
modifyingPrep aname x s (ExtraArgs{..}) = s (ExtraArgs {extraPreps = extraPreps++[(aname,x)],..})

usingCompClass :: (Object -> S') -> S' -> S'
usingCompClass cn s ExtraArgs {..} = s ExtraArgs {extraCompClass = Explicit cn,..}


sentenceApplyAdv :: ((Object -> Prop) -> Object -> Prop) -> S' -> S'
sentenceApplyAdv adv s' ExtraArgs{..} = s' ExtraArgs {extraAdvs = adv . extraAdvs,..}
--------------------------
-- Time

referenceTimeFor :: S -> Dynamic Exp
referenceTimeFor s = do
  tMeta <- getFresh
  s' <- s
  getTimeInEnv tMeta (noExtraObjs (usingTime (ExactTime (Var tMeta)) s'))

-- | Find the time t when Prop(t) happened, looking up true facts in environment.
getTimeInEnv :: Var -> (Prop) -> Dynamic Exp
getTimeInEnv meta prop = do
  facts <- gets envFacts
  let possibleTimes = catMaybes $ map (solveThe meta prop) facts
  case possibleTimes of
    [] -> freshTime (\_ -> Con "True") -- get a new time reference.
    [t] -> return t
    _ -> error "getTimeInEnv: multiple references not supported"

-- |
freshTime :: (Exp -> Exp) -> Dynamic Exp
freshTime constraint = do
  t <- getFresh
  modify (pushTimeConstraint t (constraint $ Var t))
  return (Var t)

pushTimeConstraint :: Var -> Exp -> Env -> Env
pushTimeConstraint t c Env{..} = Env{envTimeVars = (c,t):envTimeVars,..}

usingTime :: Temporal -> S' -> S'
usingTime e s' ExtraArgs{..} = s' ExtraArgs{extraTime = extraTime <> e, ..} 

-- freshTime (\x -> Con "Before" `apps` [Con "NOW",x])

temporalToLogic :: Temporal -> Exp
temporalToLogic t = case t  of
  ExactTime e -> e
  TenseTime t' -> temporalToLogic t'
  UnspecifiedTime -> Con "UnspecifiedTime"
  IntervalTime s -> Con ("interval" ++ s)

interpTense :: Tense -> Temporal
interpTense temp = TenseTime $ case temp of
    Past -> IntervalTime "Past"
    _ -> UnspecifiedTime

pushFact :: Prop -> Env -> Env
pushFact p Env{..} = Env{envFacts=p:envFacts,..}

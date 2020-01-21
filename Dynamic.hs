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

import Prelude hiding (pred,Num)
import Control.Monad.State hiding (ap)
import Control.Monad.Reader hiding (ap)
import Control.Monad.Fail
import Logic hiding (Pol)
import LogicB ()
import qualified Logic
import Data.List (intersect,partition,nubBy,sortBy,find)
import Control.Monad.Logic hiding (ap)
import Control.Applicative
import Data.Function (on)
-- import Data.Maybe (catMaybes)
import Data.Foldable (asum)
type Object = Exp
type Prop = Exp

data Optional a = Default | Explicit a
instance Semigroup (Optional a) where
  Default <> x = x
  x <> Default = x
  x <> _ = x -- FIXME: issue some warning

instance Monoid (Optional a) where
  mempty = Default

--------------------------------
-- Operators

-- | Run the argument, but restore the environment if it gets changed.
protected :: Dynamic a -> Dynamic a
protected a = do
  s <- get
  x <- a
  s' <- get
  put s {freshVars = freshVars s'}
  return x

sloppily :: Dynamic a -> Dynamic a
sloppily = local (\ReadEnv{..} -> ReadEnv{envSloppyFeatures = True,..})
-- sloppily = id

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

first :: (t2 -> t1) -> (t2, t) -> (t1, t)
first f (x,y) = (f x,y)
second :: forall t t1 t2. (t2 -> t1) -> (t, t2) -> (t, t1)
second f (x,y) = (x,f y)


data Num where
  Unspecified :: Num
  Singular :: Num
  Plural   :: Num
  Half :: Num
  AFew :: Num
  MoreThan :: Num -> Num
  LessThan :: Num -> Num
  Cardinal :: Nat -> Num
  deriving (Show,Eq)

onS' :: (Prop -> Prop) -> S' -> S'
onS' f s extra = first f (s extra)
  -- f (p eos)

data BoundKind = Inequal | Equal | Free | Ultra deriving Eq
type TimeBound = (BoundKind,Exp)
type TimeSpan = (Exp,Exp)
data Temporal = Temporal { startBound, stopBound :: TimeBound
                         , durationBound :: TimeBound } deriving Eq

exactInterval :: TimeSpan -> Temporal
exactInterval (t0,t1) = Temporal {startBound = (Equal,t0),
                                  stopBound = (Equal,t1),
                                  durationBound = freeDuration
                                 }
  -- ExactInterval TimeSpan | InInterval TimeSpan{- | ConstrainedInterval (TimeSpan -> Prop)-}  deriving Show
freeDuration = (Free,Con "Free")
temporalSpan :: Temporal -> TimeSpan
temporalSpan Temporal{..} = (snd startBound, snd stopBound)

timePoint :: b -> (b, b)
timePoint x = (x,x)

now :: Temporal
now = exactInterval nowSpan

nowSpan :: TimeSpan
nowSpan = (Con "NOW", Con "NOW")

data ExtraArgs = ExtraArgs { extraPreps :: [(Var,Object)] -- prepositions
                           , extraAdvs :: (Object -> Prop) -> Object -> Prop -- adverbs
                           , extraCompClass :: Optional CN''
                           , extraTime :: Temporal
                           }

type S'' = ExtraArgs -> Prop
type Cl' = S'
type S' = ExtraArgs -> (Prop,TimeSpan)
type S = Dynamic S'
type V2 = Dynamic (Object -> Object -> S') --  Object first, subject second.
type V3 = Dynamic (Object -> Object -> Object -> S')
type CN' = (CN'',[Gender])
type CN'' = Object -> S''
type CN = Dynamic CN'
type CN2 = Dynamic CN2'
type CN2' = (Object -> CN'',[Gender])
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

type Cl =  Dynamic Cl'
type Temp = Tense

data Tense = Conditional | Future | PastPerfect | Past | Present | PresentPerfect | FuturePerfect deriving (Ord,Eq)

type ClSlash  = Dynamic VP'
type RCl  = Dynamic RCl'
type RCl' = Object -> Prop
type RS  = Dynamic RCl'
type AP = Dynamic A'
type A = Dynamic A'
type A' = (Object -> Prop) -> CN''


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
               ,sEnv :: Dynamic S'
               ,quantityEnv :: [(Var,CN')] -- map from CN' to "default" quantity.
               ,envDefinites :: [(Exp,Object)] -- map from CN to pure objects
               ,envMissing :: [(Exp,Var)] -- definites that we could not find. A map from CN to missing variables
               ,envPluralizingQuantifier :: Bool
               ,envFacts :: [Prop]
               ,freshVars :: [String]
               }
         -- deriving Show

data ReadEnv = ReadEnv {envTense :: Tense -- tense of the enclosing clause
                       ,envSloppyFeatures :: Bool
                       }

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
  [] -> [return $ MkNP [] assumedNum (ObjectQuant (constant "assumedNP")) (fst assumedCN) (snd assumedCN)]
  xs -> map snd xs

getNP :: ObjQuery -> Dynamic [NP]
getNP q = gets (getNP' q)

getDefinite :: CN' -> Dynamic Object
getDefinite cn' = do
  things <- gets envDefinites
  let pred = lam (noExtraObjsCN' cn')
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
    [] -> error "getQuantity: panic"

-------------------------------
-- Pushes


pushQuantity :: Var -> CN' -> Env -> Env
pushQuantity v cn Env{..} = Env{quantityEnv=(v,cn):quantityEnv,..}

pushDefinite :: CN'' -> Var -> Env -> Env
pushDefinite source target Env{..} =
  Env{envDefinites = (lam (\x' -> source x' emptyObjs),Var target):envDefinites,..}

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

pushS :: Dynamic S' -> Env -> Env
pushS s Env{..} = Env{sEnv=s,..}

----------------------------------
-- Effects/Dynamic

allVars :: [String]
allVars = map (:[]) ['a'..'z'] ++ cycle (map (:[]) ['α'..'ω'])

quantifyMany :: [(Exp,Var)] -> Exp -> Exp
quantifyMany [] e = e
quantifyMany ((dom,x):xs) e = Forall x (dom `app` (Var x)) (quantifyMany xs e)

runDynamic :: Dynamic Exp -> [(Exp,Env)]
runDynamic (Dynamic x)= do
  (formula,env@Env {..}) <- observeAll (runStateT (runReaderT x assumedReadEnv) assumed)
  let e = quantifyMany [(Lam (\_ -> Con "Nat"),v) | (v,_cn) <- quantityEnv] $
          quantifyMany envMissing formula
  return (e,env)

evalDynamic :: Dynamic Exp -> [Exp]
evalDynamic d = fst <$> (runDynamic d)

newtype Dynamic a = Dynamic {fromDynamic :: ReaderT ReadEnv (StateT  Env Logic) a} deriving (Monad,Applicative,Functor,MonadState Env,Alternative,MonadPlus,MonadLogic,MonadReader ReadEnv)
instance Show (Dynamic a) where show _ = "<DYNAMIC>"

instance MonadFail Dynamic where
  fail = error

type Effect = Dynamic Prop

filterKey :: Eq a => a -> [(a, b)] -> [(a, b)]
filterKey k = filter ((/= k) . fst)

mkPred :: String -> Dynamic (Object -> S')
mkPred p = do
  f <- appArgs p
  return (\x -> f [x])

mkPred' :: String -> Object -> ExtraArgs -> Prop
mkPred' p x = appArgs' id p [x]

mkCN :: String -> [Gender] -> CN'
mkCN p  = (mkPred' p,)

mkRel2 :: String -> Dynamic (Object -> Object -> S')
mkRel2 p = do
  f <- appArgs p
  return (\x y -> f [x,y])

mkRel2' :: String -> Object -> Object -> S''
mkRel2' p x y = appArgs' id p [x,y]


mkRel3 :: String -> Dynamic (Object -> Object -> Object -> S')
mkRel3 p = do
  f <- appArgs p
  return (\x y z -> f [x,y,z])

constant :: String -> Exp
constant x = Con x

pureObj :: Exp -> Num -> CN' -> NP
pureObj x number (cn,gender) = return $ MkNP [] number (ObjectQuant x) cn gender

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
assumedPred = mkPred

assumedCN :: CN'
assumedCN = mkCN "assumedCN" [Male,Female,Neutral]

assumedNum :: Num
assumedNum = Singular

assumed :: Env
assumed = Env {vp2Env = (mkRel2 "assumedV2")
               , vpEnv = []
               -- ,apEnv = (pureIntersectiveAP (mkPred "assumedAP"))
               -- ,cn2Env = pureCN2 (mkPred "assumedCN2") Neutral Singular
               ,objEnv = []
               ,sEnv = return (\_ -> (constant "assumedCl",timePoint (Con "NOW")))
               ,quantityEnv = []
               ,cnEnv = []
               ,envDefinites = []
               ,envMissing = []
               ,envPluralizingQuantifier = False
               ,envFacts = []
               ,freshVars = allVars}

assumedReadEnv :: ReadEnv
assumedReadEnv = ReadEnv {envTense = Present
                         ,envSloppyFeatures = False
                         }


numSg,numPl :: Num
numSg = Singular
numPl = Plural

data Predet = JustPredet | MostPredet | AtLeastPredet | AtMostPredet | AllPredet | ExactlyPredet deriving Show

data NPData where
  MkNP :: [Predet] -> Num -> Quant -> (Object -> ExtraArgs -> Prop) -> [Gender] -> NPData

type N = CN
type PN = (String,[Gender],Num)

all' :: [a -> Bool] -> a -> Bool
all' fs x = all ($ x) fs

any' :: [a -> Bool] -> a -> Bool
any' fs x = any ($ x) fs

type LogicQuant = [Char] -> Prop -> Exp -> Exp
instance Show (a -> b) where show _ = "<FUNCTION>"
type Quant' = Num -> CN' -> Role -> Dynamic NP'
data Quant = PossQuant Pron | UniversalQuant Pol | IndefQuant | ExistQuant | ETypeQuant LogicQuant | DefiniteQuant | TheOtherQuant | ObjectQuant Object | BoundQuant Logic.Pol Nat
  | ObliviousQuant Quant' -- ^ quantifier that ignores numbers and predeterminers.


type Pol = Prop -> Prop

type Pron = NP


--------------------------
-- Extra objects and S'

emptyObjs :: ExtraArgs
emptyObjs = ExtraArgs {extraPreps = [], extraAdvs = id, extraTime = now, extraCompClass = mempty}

noExtraObjs :: S' -> Prop
noExtraObjs f = fst $ f emptyObjs

relaxTime :: S' -> S''
relaxTime s' extraObjs = fst (s' extraObjs)

noExtraObjsCN'' :: CN'' -> (Object -> Prop)
noExtraObjsCN'' f x = f x emptyObjs

noExtraObjsCN' :: CN' -> (Object -> Prop)
noExtraObjsCN' (f,_gender) = noExtraObjsCN'' f


data Aspect = Activity | Achievement deriving Eq

verbAspect :: [Char] -> Aspect
verbAspect "pay_V2on" = Activity
verbAspect "pay_V2" = Activity -- 319
verbAspect "expand_V" = Activity
verbAspect "make8do_V2" = Activity
verbAspect "swim_V" = Activity
verbAspect "write_V2" = Activity
verbAspect "_BE_in" = Activity
verbAspect "live_Vin" = Activity
verbAspect "run_V2" = Activity
verbAspect "use_VVTiming" = Activity
verbAspect "discover_V2" = Activity -- treated as such in FraCas 291
verbAspect "_BE_" = Activity -- mostly used for "it is now date"
verbAspect "finish_VVTiming" = Activity -- Because we can finish "within" an interval, see Coq code.
verbAspect _ = Achievement

appArgs' :: (Exp -> Exp) -> String -> [Object] -> S''
appArgs' modifier nm objs@(_:_) (ExtraArgs {..}) =  extraAdvs (app (pAdverbs (modifier prep'd))) subject
  where prep'd = Con nmPrep `apps` (map snd prepositions ++ indirectObjects)
        nmPrep = nm ++ concatMap fst prepositions
        indirectObjects = init objs
        subject = last objs
        cleanedPrepositions = sortBy (compare `on` fst) $ nubBy ((==) `on` fst) extraPreps
        (adverbialPrepositions,prepositions) = partition ((== "before") . fst) cleanedPrepositions
        pAdverbs x = foldr app x [Con (p ++ "_PREP") `app` arg | (p,arg) <- adverbialPrepositions]

appArgs :: String -> Dynamic ([Object] -> S')
appArgs nm  = do
  v0 <- getFresh
  v1 <- getFresh
  return $ \objs (eos@ExtraArgs {..}) ->
    let timing p = Con "appTime" `apps` ([t0,t1] ++ [p])
        body = appArgs' timing nm objs eos
        ((r0,r1),q) = quantInterval Exists v0 v1 extraTime body
        (t0,t1) = case verbAspect nmPrep of
          Activity -> (r0,r1)
          Achievement -> (r1,r1)
        nmPrep = nm ++ concatMap fst prepositions
        cleanedPrepositions = sortBy (compare `on` fst) $ nubBy ((==) `on` fst) extraPreps
        (_,prepositions) = partition ((== "before") . fst) cleanedPrepositions
    in (q ,(t0,t1))

-- normalizeTemporal (Temporal {startBound = (Equal,_), stopBound = (Equal,_), durationBound=(Equal,_)}) = error "normalizeTemporal: panic"
-- normalizeTemporal (Temporal {startBound = (Equal,_), stopBound = (Equal,_), durationBound=(Inequal,_)}) = error "normalizeTemporal: panic"
-- normalizeTemporal (Temporal {startBound = (_,_),     stopBound = (Equal,_), durationBound=(Equal,dt)}) =
--   Temporal {startBound=(Equal,t1-dt), stopBound = (Equal,t1)}
-- normalizeTemporal t = t
  
quantInterval :: (Var -> Exp -> Exp -> Exp) -> Var -> Var -> Temporal -> Exp -> (TimeSpan,Exp)
quantInterval q x0 x1 Temporal{startBound = (b0,t0), stopBound = (b1,t1), durationBound = (db,dt)} body =
  ((t0',t1'),q0 (q1 body))
  where [x0',x1'] = map Var [x0,x1]
        k0 = case b0 of
          Inequal -> isInterval t0 x0'
          Ultra -> isInterval x0' t0
          _->true -- constraint on the interval start
        k1 = case b1 of Inequal -> isInterval x1' t1;_->true -- constraint on the interval end
        (t0',q0) = case b0 of Equal -> (t0,id); _ -> (x0',q x0 (TimeDomain k0)) -- start quantifier/value
        (t1',q1) = case b1 of -- end quantifier/value
                     Equal -> (t1,id)
                     _ -> case db of
                       Equal -> (t0 `plusTime` dt,id)
                       _ -> (x1',q x1 (TimeDomain (k1 ∧ iCond)))
        iCond = case db of
              Free -> isInterval t0' t1'
              Inequal -> isInterval (t0' `plusTime` dt) t1'
              _ -> error "quantInterval: panic"

plusTime :: Exp -> Exp -> Exp
plusTime x y = Con "Plus" `apps` [x,y]

appAdjArgs :: String -> [Object] -> S''
appAdjArgs nm [cn,obj] (ExtraArgs{..}) = (extraAdvs  (\x -> apps prep'd [cn,x]) obj)
  where prep'd = Con "appA" `app` (Con (nm ++ concatMap fst prepositions) `apps` ((map snd prepositions)))
        prepositions = nubBy ((==) `on` fst) extraPreps

modifyingPrep :: String -> Object -> S' -> S'
modifyingPrep aname x s (ExtraArgs{..}) = s (ExtraArgs {extraPreps = extraPreps++[(aname,x)],..})

usingCompClass :: CN'' -> S' -> S'
usingCompClass cn s ExtraArgs {..} = s ExtraArgs {extraCompClass = Explicit cn,..}


sentenceApplyAdv :: ((Object -> Prop) -> Object -> Prop) -> S' -> S'
sentenceApplyAdv adv s' ExtraArgs{..} = s' ExtraArgs {extraAdvs = adv . extraAdvs,..}
--------------------------
-- Time

-- forceTime :: TimeSpan -> Cl' -> Prop
-- forceTime tMeta cl = noExtraObjs (useTime tMeta cl)
-- -- HACK: setting the time is at the "UseCl" level, which has to set a
-- -- time. But we need to override it from the level above (S), so we
-- -- use the "ForceTime" hack.

-- useTime :: TimeSpan -> Cl' -> S'
-- useTime t s ExtraArgs{..} = s ExtraArgs{extraTime = ForceTime t,..}

-- -- | Look in envFacts for the time at which s' happened.
-- -- That is: Find the times t when Prop(t) happened, looking up true facts in environment.
-- referenceTimesFor :: Cl' -> Dynamic [TimeSpan]
-- referenceTimesFor s' = do
--   tMeta0 <- getFresh
--   tMeta1 <- getFresh
--   facts <- gets envFacts
--   let e = forceTime (Var tMeta0, Var tMeta1) s'
--   return $ map mkSpan $ catMaybes $ map (solveThe [tMeta0,tMeta1] e) facts
--   where mkSpan [t0,t1] = (t0,t1)

-- referenceTimeFor :: Cl' -> Dynamic TimeSpan
-- referenceTimeFor s = do
--   ts <- referenceTimesFor s
--   case ts of
--     [] -> do
--       facts <- gets envFacts
--       error ("referenceTimesFor: no time for " ++ show (forceTime (Var "τ₀", Var "τ₁") s) ++ "\n facts:\n" ++ intercalate "\n" (map show facts))
--     (t:_) -> return t

-- | S' shall use the given time constraint
usingTime :: Temporal -> S' -> S'
usingTime e s' ExtraArgs{..} = s' ExtraArgs{extraTime = e, ..} 

modifyTime :: (Temporal -> Temporal) -> S' -> S'
modifyTime f s' ExtraArgs{..} = s' ExtraArgs{extraTime = f extraTime, ..} 

-- temporalToLogic :: Temporal -> TimeSpan
-- temporalToLogic t = case t  of
--   ExactTime e -> e
--   ForceTime e -> e
--   -- TenseTime t' -> temporalToLogic t'
--   UnspecifiedTime -> (Con "UnspecifiedTime",Con "UnspecifiedTime")

tempToArgs :: TimeSpan -> [Exp]
tempToArgs = pairToList --  . temporalToLogic

pairToList :: (t, t) -> [t]
pairToList (x,y) = [x,y]

-- pushFact :: Prop -> Env -> Env
-- pushFact (Quant _amount _pol _var _dom body) = pushFact body -- HACK to access atom
-- pushFact (p :∧ q)  = {-pushFact p . -} pushFact q  -- HACK to access atom (ATOM)
-- pushFact p = \Env{..} -> Env{envFacts=p:envFacts,..}

withTense :: Tense -> Dynamic a -> Dynamic a
withTense t = local $ \ReadEnv{..} -> ReadEnv {envTense=t,..}

joinTime :: TimeSpan -> TimeSpan -> TimeSpan
joinTime t1 t2 = t1 -- FIXME

quantTime :: (Var -> Exp -> Exp -> Exp) -> Var -> Exp -> Exp -> Exp
quantTime quantifier x constraint body = quantifier x (TimeDomain constraint) body

isInterval :: Exp -> Exp -> Exp
isInterval x y = Con "IS_INTERVAL" `apps` [x,y]


afromList :: Alternative f => [a] -> f a
afromList = asum . map pure

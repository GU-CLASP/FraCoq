import MS
import Bank
import LogicB
import Logic hiding (Exp(..),freeVars)
import Data.Foldable

handleProblem :: Int -> (Phr,Phr,x) -> IO ()
handleProblem n p = do
  putStrLn "=========="
  putStrLn ("== " ++ show n)
  debug (probToEff p)

probToEff (premise,h,_) = phrToEff premise ==> phrToEff h

debug :: Effect -> IO ()
debug e = do
  let ps = allInterpretations e
  forM_ ps $ \p0 -> do
    putStrLn "-----------------"
    let p = (fromHOAS' p0) :: Exp Zero
    forM_ (extendAllScopesTrace p) $ \(fvs,q) -> do
      putStrLn ("extendAllScopes Step. Freevars = " ++ show fvs)
      putStrLn ("expression = " ++ show q)


testIt :: Exp Zero
testIt = Op And [Op And [Quant One Pos "x" (Con "dom") (Con "body"), Var "x" ], Con "whatever"]

tt = extendAllScopes (testIt :: Exp Zero)

-- >>> tt
-- ((EXISTS (fun x=>dom) (fun x=>body /\ x)) /\ whatever)

main :: IO ()
main = do
  -- suite handleProblem >> putStrLn "----------"
  debug (phrToEff s_005_1_p)
  -- debug (probToEff p_189)
  -- handleProblem p

-- >>> main

-- Input the gender of PNs and CNs
-- Many: need to have multiple readings. Interpreted as disjunctions.

-- Many: new handling of adverbs, prepositions. See type VP'

-- ???: scope extension from domain of quantifiers: (remember that each quantifier comes with a domain, not a type but a logical formula)
   -- ∀x. (∃y. P(y) -> Q(x,y)) -> R(x,y)
   -- can be rewritten to:
   -- ∀y. P(y) -> ∀x. (TRUE -> Q(x,y)) -> R(x,y)

-- 116: Genders are given to PNs. One cannot assume that the context is empty and infer that Mary is female just from the example.

-- Analysis for 122. Conclusion (H) parse tree is wrong, it can't be fixed at the semantic level:

-- (Every committee) (has (((a chairman) appointed) (by (members of the committee))))

-- Instead, we should use:
-- (Every committee) (has (a (chairman (appointed (by (members of the committee))))))

-- The key constructions from the resource library are:
-- relA2 	RP -> A2 -> NP -> RCl    ... that is married to her
-- relCN         CN -> RS -> CN     person (married to her)

-- It appears that the omitted RP is not in GF, and that is what causes the parsing problem. (added as implicitRP below)
-- With explicit RP:
-- (Every committee) (has (a (chairman (that is (appointed (by (members of the committee)))))))

ouch122 :: IO ()
ouch122 = debug (phrToEff s_122_4_h)

-- >>> evalDbg p_122_ALT
-- ((FORALL (fun a=>committee_N a) (fun a=>(EXISTS (fun b=>chairman_N b) (fun b=>have_V2 b a)))) /\ (EXISTS (fun c=>True) (fun c=>appoint_V2by (THE (fun x1 => have_V2 a x1 /\ member_N x1)) b c)) -> (FORALL (fun d=>committee_N d) (fun d=>(EXISTS (fun e=>chairman_N e /\ appoint_V2 (THE (fun x1 => have_V2 d x1 /\ member_N x1)) e) (fun e=>have_V2 e d)))))

-- 124-126: At least, we need to change the syntax so that "Two out of
-- ten" is interpreted as a quantifier. At GF level: Both "two" and
-- "ten" introduce a quantifier. "They" can refer to either of the
-- bound variables. Unclear what to do about this.  Really this set of
-- examples should treat "two out of ten" as a quantifier. (Needs
-- another syntax)

-- 126: incorrect interpretation, but correct conclusion.

-- 127: We need "they" to refer to any disjunction of NPs introduced so -- far.

-- Analysis for 130:  FRACAS. Incompatible with 129. (It should be sufficent
-- that one reading allows to conclude.)

-- Analysis for 131.  In H2, a plural "they" is used to refer to a
-- singular object introduced with indefArt. When the scope of
-- "forall" is closed (when the sentence is finished), the singular
-- existential is transformed to plurals. Existentially quantified
-- variables are pushed with the "dPluralizable = True" flag if a
-- universal was introduced in the sentence. When the sentence is
-- closed, all dPluralizable entries in the environment are re-written
-- to be accessible by a plural. To know if we have a pluralizable
-- context, the envPluralizingQuantifier flag is used. It is set in
-- the dyn. semantics of universals.

-- 137.
-- a) "There are 100" --> should in general be interpreted as "at least", until we see in P4 the mention of "the other 99", implying an exact interpretation.
-- b) Difficulty to relate "THE company_N" to the set introduced in the first premise.
-- c) Difficult to interpret: (advNP (detNP (anySg_Det)) (prepNP (lexemePrep "part_Prep") (detCN (detQuant (possPron (itRefl_Pron)) (numPl)) (useN (lexemeN "computer_N")))))

-- 155. Incorrect syntax (fixed)

-- Analysis for 181. IMO it can be "yes" on some reading.

-- Analysis for 183. Strict identity not implemented.

-- Analysis for 190. Strict identity not implemented.

-- Analysis for 191-195.
-- a) I don't even understand the sentence
-- b) "They" could refer to any subset of object introduced in the environment. Potentially very expensive computationally.
--    (Potentially a lot of readings to deal with) --- see 127




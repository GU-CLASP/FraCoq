module Tests where

import MS
import Bank

main :: IO ()
main = do
  -- suite >> putStrLn "----------"
  evalDbg p_141

-- Input the gender of PNs and CNs
-- Many: need to have multiple readings. Interpreted as disjunctions.

-- Many: new handling of adverbs, prepositions. See type VP'

-- 121: Works now with "hack". The difficulty here is that the object is applied before the object.
-- Alternative is to make the vp "lazy", and wait for the last moment until the components are applied to it.


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
ouch122 = evalDbg (phrToEff s_122_4_h)

membersOfTheComittee :: NP
membersOfTheComittee = (detCN (detQuant (genNP (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "committee_N")))) (numPl)) (useN (lexemeN "member_N")))

chairman_etc :: NP
chairman_etc = detCN (detQuant (indefArt) (numSg)) (relCN (useN (lexemeN "chairman_N")) (relA2 implicitRP (lexemeV2 "appoint_V2") membersOfTheComittee))

s_122_4_h_ALT :: Phr
s_122_4_h_ALT = (sentence (useCl (present) (pPos) (predVP (detCN (every_Det) (useN (lexemeN "committee_N"))) (complSlash (slashV2a (lexemeV2 "have_V2")) chairman_etc ))))

p_122_ALT :: Effect
p_122_ALT = phrToEff (s_122_1_p ### s_122_2_p) ==> phrToEff s_122_4_h_ALT

-- >>> evalDbg p_122_ALT
-- ((forall a, committee_N a -> (exists b, chairman_N b /\ have_V2 b a)) /\ appoint_V2(by=(THE (fun x1 => have_V2 a x1 /\ member_N x1)),who=b)
-- -> (forall c, committee_N c -> (exists d, chairman_N d /\ appoint_V2(by=(THE (fun x1 => have_V2 c x1 /\ member_N x1)),who=d) /\ have_V2 d c)))


-- 125: GF: Both "two" and "ten" introduce a quantifier. "They" can refer
-- to either of the bound variables. Unclear what to do about this.
-- Really this set of examples should treat "two out of ten" as a
-- quantifier. (Needs another syntax) 

-- 126: incorrect interpretation, but correct conclusion.

-- 127: Two things are needed: 1. push "on_tuesday" down to the
-- verb. 2. "they" can refer to any disjunction of NPs introduced so
-- far.

-- Analysis for 130:  FRACAS. Incompatible with 129. (It should be sufficent
-- that one reading allows to conclude.)

-- Analysis for 131.  In H2, a plural "they" is used to refer to a
-- singular object introduced with indefArt. When the scope of
-- "forall" is closed (when the sentence is finished), the singular
-- existential should be transformed to plurals.

-- 137.
-- a) "There are 100" --> should in general be interpreted as "at least", until we see in P4 the mention of "the other 99", implying an exact interpretation.
-- b) Difficulty to relate "THE company_N" to the set introduced in the first premise.
-- c) Difficult to interpret: (advNP (detNP (anySg_Det)) (prepNP (lexemePrep "part_Prep") (detCN (detQuant (possPron (itRefl_Pron)) (numPl)) (useN (lexemeN "computer_N")))))

-- 

-- Analysis for 181. IMO it can be "yes" on some reading.

-- Analysis for 183. Strict identity not implemented.

-- Analysis for 190. Strict identity not implemented.




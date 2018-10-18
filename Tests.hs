module Tests where

import MS
import Bank

main :: IO ()
main = do
  -- suite >> putStrLn "----------"
  evalDbg (phrToEff s_122_4_h_ALT)

-- Many: need to have multiple readings. Interpreted as disjunctions.



-- 121: Works now with "hack". The difficulty here is that the object is applied before the object.
-- Alternative is to make the vp "lazy", and wait for the last moment until the components are applied to it.


-- Analysis for 122. Conclusion (H) parse tree is wrong, it can't be fixed at the semantic level:

-- (Every committee) (has (((a chairman) appointed) (by (members of the committee))))

-- Instead, we should use:
-- (Every committee) (has (a (chairman (appointed (by (members of the committee))))))

-- The key constructions from the resource library are:
-- mkAP 	A2 -> NP -> AP     married to her

-- This one appears to be missing (but we will add it anyway, and say so.)
-- mkCN         CN -> AP -> CN     person (married to her)

ouch122 :: IO ()
ouch122 = evalDbg (phrToEff s_122_4_h)

membersOfTheComittee :: NP
membersOfTheComittee = (detCN (detQuant (genNP (detCN (detQuant (defArt) (numSg)) (useN (lexemeN "committee_N")))) (numPl)) (useN (lexemeN "member_N")))

chairman_etc :: NP
chairman_etc = detCN (detQuant (indefArt) (numSg)) (cnap (useN (lexemeN "chairman_N")) (a2np (lexemeV2 "appoint_V2") membersOfTheComittee))

s_122_4_h_ALT :: Phr
s_122_4_h_ALT = (sentence (useCl (present) (pPos) (predVP (detCN (every_Det) (useN (lexemeN "committee_N"))) (complSlash (slashV2a (lexemeV2 "have_V2")) chairman_etc ))))

-- >>> evalDbg (phrToEff s_122_4_h_ALT)
-- (forall a, committee_N a -> (exists b, chairman_N b /\ appoint_V2(by=b,who=(THE (fun x1 => have_V2 a x1 /\ member_N x1))) /\ have_V2 b a))


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

-- Analysis for 181. IMO it can be "yes" on some reading.

-- Analysis for 183. Strict identity not implemented.

-- Analysis for 190. Strict identity not implemented.




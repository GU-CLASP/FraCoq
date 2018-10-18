module Tests where

import MS
import Bank

main :: IO ()
main = do
  -- suite >> putStrLn "----------"
  evalDbg (p_132)

-- All: need to have multiple readings. Interpreted as disjunctions.

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

-- 125: Both "two" and "ten" introduce a quantifier. "They" can refer
-- to either of the bound variables. Unclear what to do about this.

-- 126: incorrect interpretation, but correct conclusion.

-- 127: Two things are needed: 1. push "on_tuesday" down to the
-- verb. 2. "they" can refer to any disjunction of NPs introduced so
-- far.

-- Analysis for 130. Incompatible with 129. (It should be sufficent
-- that one reading allows to conclude.)

-- Analysis for 131.  In H2, a plural "they" is used to refer to a
-- singular object introduced with indefArt. When the scope of
-- "forall" is closed (when the sentence is finished), the singular
-- existential should be transformed to plurals.

-- Analysis for 181. IMO it can be "yes" on some reading.

-- Analysis for 183. Strict identity not implemented.

-- Analysis for 190. Strict identity not implemented.




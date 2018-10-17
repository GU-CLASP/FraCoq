module Tests where

import MS
import Bank

main :: IO ()
main = do
  suite >> putStrLn "----------"
  evalDbg (p_180)




-- Analysis for 122. Conclusion (H) parse tree is beyond idiotic,
-- can't be fixed at the semantic level:

-- (Every committee) (has (((a chairman) appointed) (by (members of the committee))))

ouch122 :: IO ()
ouch122 = evalDbg (phrToEff s_122_4_h)



-- Analysis for 132.  In h2, a plural they is used to refer to a
-- singular object introduced with indefArt. When the scope of
-- "forall" is closed (when the sentence is finished), the singular
-- existential should be transformed to plurals.


-- Analysis for 181. IMO it can be "yes" on some reading.

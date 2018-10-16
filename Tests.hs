module Tests where

import MS
import Bank

main :: IO ()
main = do
  suite
  print "----------"
  evalDbg p_129



-- >>> evalDbg (s_120_1_p ### s_120_2_p)
-- ((EXISTS a:(meeting_N a). (attend_V2 smith_PN a)) /\ (chair_V2 smith_PN a))


-- Analysis f;r 122
-- H1 : (forall a, committee_N a -> (exists b, chairman_N b /\ have_V2 a b))
-- H2 : (exists d, member_N d /\ have_V2 a d /\ by8agent_Prep d (fun x1 => (exists c, appoint_V2 x1 c)) b)
-- ---------------------------------------------------------------------------------------------------------
-- H  : (forall e, committee_N e -> (exists h, chairman_N h /\ (exists f, appoint_V2 f h) /\ (exists g, possess_Prep e member_N g /\ by8agent_Prep g (have_V2 e) h)))



-- com
-- H1 : (forall a, committee_N a -> (exists b, chairman_N b /\ have_V2 a b))
-- H2 : (exists d, member_N d /\ have_V2 a d /\ by8agent_Prep d (fun x1 => (exists c, appoint_V2 x1 c)) b)
-- he  : committee_N com
-- ---------------------------------------------------------------------------------------------------------
-- H  : (exists h, chairman_N h /\ (exists f, appoint_V2 f h) /\ (exists g, possess_Prep e member_N g /\ by8agent_Prep g (have_V2 e) h))



-- H1 : (exists b, chairman_N b /\ have_V2 com b)
-- H2 : (exists d, member_N d /\ have_V2 com d /\ by8agent_Prep d (fun x1 => (exists c, appoint_V2 x1 c)) b)
-- ---------------------------------------------------------------------------------------------------------
-- H  : (exists h, chairman_N h /\ (exists f, appoint_V2 f h) /\ (exists g, possess_Prep e member_N g /\ by8agent_Prep g (have_V2 e) h))


-- _ : committee_N com
-- _ : chairman_N b
-- _ : have_V2 com b
-- _ : member_N d
-- _ : have_V2 com d
-- _ : by8agent_Prep d (fun x1 => (exists c, appoint_V2 x1 c)) b
-- ---------------------------------------------------------------------------------------------------------
-- H  : (exists h, chairman_N h /\ (exists f, appoint_V2 f h) /\ (exists g, possess_Prep e member_N g /\ by8agent_Prep g (have_V2 e) h))


-- _ : committee_N com
-- _ : chairman_N b
-- _ : have_V2 com b
-- _ : member_N d
-- _ : have_V2 com d
-- _ : by8agent_Prep d (fun x1 => (exists c, appoint_V2 x1 c)) b
-- ---------------------------------------------------------------------------------------------------------
--     (exists f, appoint_V2 f b) /\ (exists g, possess_Prep e member_N g /\ by8agent_Prep g (have_V2 e) b))






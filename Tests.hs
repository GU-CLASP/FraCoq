module Tests where

import MS
import Bank

main :: IO ()
main = do
  suite
  print "----------"
  evalDbg p_122

-- >>> evalDbg (s_120_1_p ### s_120_2_p)
-- ((EXISTS a:(meeting_N a). (attend_V2 smith_PN a)) /\ (chair_V2 smith_PN a))


-- Analysis for 122


-- forall a, committee_N a -> (exists b, chairman_N b /\ have_V2 a b)
-- by8agent_Prep (THE (fun x1 => (have_V2 a x1 /\ member_N x1))) (fun x1 => (exists c, appoint_V2 x1 c)) b
----------------------------------------------------------------------------------------------------------------------------------------------------------------
-- forall d, committee_N d -> (exists g, chairman_N g /\ (exists e, appoint_V2 e g) /\ (exists f, possess_Prep d member_N f /\ by8agent_Prep f (have_V2 d) g))


-- committee_N d
-- forall a, committee_N a -> (exists b, chairman_N b /\ have_V2 a b)
-- by8agent_Prep (THE (fun x1 => (have_V2 a x1 /\ member_N x1))) (fun x1 => (exists c, appoint_V2 x1 c)) b
----------------------------------------------------------------------------------------------------------------------------------------------------------------
-- (exists g, chairman_N g /\ (exists e, appoint_V2 e g) /\ (exists f, possess_Prep d member_N f /\ by8agent_Prep f (have_V2 d) g))



-- d : indiv
-- committee_N d
-- exists b, chairman_N b /\ have_V2 d b
-- by8agent_Prep (THE (fun x1 => (have_V2 a x1 /\ member_N x1))) (fun x1 => (exists c, appoint_V2 x1 c)) b
----------------------------------------------------------------------------------------------------------------------------------------------------------------
-- (exists g, chairman_N g /\ (exists e, appoint_V2 e g) /\ (exists f, possess_Prep d member_N f /\ by8agent_Prep f (have_V2 d) g))


-- d : indiv
-- b : indiv
-- committee_N d
-- chairman_N b
-- have_V2 d b
-- by8agent_Prep (THE (fun x1 => (have_V2 a x1 /\ member_N x1))) (fun x1 => (exists c, appoint_V2 x1 c)) b
----------------------------------------------------------------------------------------------------------------------------------------------------------------
-- (exists g, chairman_N g /\ (exists e, appoint_V2 e g) /\ (exists f, possess_Prep d member_N f /\ by8agent_Prep f (have_V2 d) g))


-- d : indiv
-- b : indiv
-- committee_N d
-- chairman_N b
-- have_V2 d b
-- by8agent_Prep (THE (fun x1 => (have_V2 a x1 /\ member_N x1))) (fun x1 => (exists c, appoint_V2 x1 c)) b
----------------------------------------------------------------------------------------------------------------------------------------------------------------
-- (exists e, appoint_V2 e b) /\ (exists f, possess_Prep d member_N f /\ by8agent_Prep f (have_V2 d) b))







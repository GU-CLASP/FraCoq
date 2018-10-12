module Tests where

import MS
import Bank

main = do
  print 114
  evalDbg p_114
  print 120
  evalDbg p_120


-- >>> evalDbg (s_120_1_p ### s_120_2_p)
-- ((EXISTS a:(meeting_N a). (attend_V2 smith_PN a)) /\ (chair_V2 smith_PN a))


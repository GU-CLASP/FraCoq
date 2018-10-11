module Tests where

import MS
import Bank

main = do
  print 114
  evalDbg s_114_1_p
  print 120
  evalDbg (s_120_1_p ### s_120_2_p)

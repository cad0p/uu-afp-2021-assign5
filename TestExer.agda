module TestExer where

import Exercise
open Exercise


-- testPure : pure {1} {Bool} True
-- testPure = ?
{- Unable to test: see this error:
Vec Bool 1 should be a sort, but it isn't
when checking that the inferred type of an application
  Vec Bool 1
matches the expected type
  _0
-}

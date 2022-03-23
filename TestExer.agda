module TestExer where

import Exercise
open Exercise


testPure : pure {1} {Bool} True == Cons True Nil
testPure = Refl


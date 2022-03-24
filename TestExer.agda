module TestExer where

import Exercise
open Exercise


testPure : pure {1} {Bool} True == Cons True Nil
testPure = Refl

testPure2 : pure {2} {Bool} True == Cons True (Cons True Nil)
testPure2 = Refl

testZeroVec : zeroVec Zero == Nil
testZeroVec = Refl

testZeroVec2 : zeroVec 2 == Cons Zero (Cons Zero Nil)
testZeroVec2 = Refl

testIdVec : idVec {0} 0 == Just Nil
testIdVec = Refl

testIdVec1 : idVec {1} 1 == Just (Cons 1 Nil)
testIdVec1 = Refl

testIdVec2₀ : idVec {2} 0 == Nothing
testIdVec2₀ = Refl

testIdVec2₁ : idVec {2} 1 == Just (Cons 1 (Cons Zero Nil))
testIdVec2₁ = Refl

testIdVec2₂ : idVec {2} 2 == Just (Cons Zero (Cons 1 Nil))
testIdVec2₂ = Refl

testIdVec2₃ : idVec {2} 3 == Nothing
testIdVec2₃ = Refl
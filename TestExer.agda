module TestExer where

import Exercise
open Exercise


testPure : pure {1} {Bool} True == Cons True Nil
testPure = Refl

testPure2 : pure {2} {Bool} True == Cons True (Cons True Nil)
testPure2 = Refl

testMatrix : Matrix Bool 1 1
testMatrix = Cons (Cons True Nil) Nil

testMatrixEmpty : Matrix Bool 0 0
testMatrixEmpty = Nil

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

-- so this below is wrong, we need another function
-- testIdMatrix₀ : idMatrix {0} == Nil
-- testIdMatrix₀ = Refl

-- testIdMatrix₁ : idMatrix {1} == Cons (Cons 1 Nil) Nil
-- testIdMatrix₁ = Refl


-- testIdMatrix₂ : idMatrix {2} == 
--     Cons (Cons Zero (Cons 1 Nil)) (
--     Cons (Cons 1 (Cons Zero Nil)) 
--     Nil)
-- testIdMatrix₂ = Refl

testCompNat2₀ : compNat 2 0 == 2
testCompNat2₀ = Refl

testCompNat2₁ : compNat 2 1 == 1
testCompNat2₁ = Refl

testCompNat2₂ : compNat 2 2 == 0
testCompNat2₂ = Refl


testIdMatrix₀ : idMatrix {0} == Nil
testIdMatrix₀ = Refl

testIdMatrix₁ : idMatrix {1} == Cons (Cons 1 Nil) Nil
testIdMatrix₁ = Refl


testIdMatrix₂ : idMatrix {2} == 
    Cons (Cons 1 (Cons Zero Nil)) (
    Cons (Cons Zero (Cons 1 Nil)) 
    Nil)
testIdMatrix₂ = Refl

testIdMatrix₃ : idMatrix {3} == 
    Cons (Cons 1 (Cons Zero (Cons Zero Nil)))(
    Cons (Cons Zero (Cons 1 (Cons Zero Nil)))(
    Cons (Cons Zero (Cons Zero (Cons 1 Nil))) 
    Nil))
testIdMatrix₃ = Refl


matrix3₃ : Matrix Nat 3 3
matrix3₃ = 
    Cons (Cons 1 (Cons 2 (Cons 3 Nil)))(
    Cons (Cons 4 (Cons 5 (Cons 6 Nil)))(
    Cons (Cons 7 (Cons 8 (Cons 9 Nil))) 
    Nil))

matrix3₂ : Matrix Nat 3 2
matrix3₂ = 
    Cons (Cons 1 (Cons 2 (Cons 3 Nil)))(
    Cons (Cons 4 (Cons 5 (Cons 6 Nil))) 
    Nil)


testTranspose3₃-dumb : transpose-dumb matrix3₃ == 
    Cons (Cons 1 (Cons 4 (Cons 7 Nil))) (
    Cons (Cons 2 (Cons 5 (Cons 8 Nil))) (
    Cons (Cons 3 (Cons 6 (Cons 9 Nil))) 
    Nil))
testTranspose3₃-dumb = Refl


test-xs-!!v-i-st-p : (Cons 1 Nil !!v Zero st ≤-soundness) == 1
test-xs-!!v-i-st-p = Refl

-- this correctly fails with the wrong proof!
-- and it's also 1-indexed this way
test-!!v1₂ : (Cons 1 Nil !!v ≤-soundness {2}) == {!   !}
test-!!v1₂ = Refl

-- this correctly fails with the wrong proof!
-- and it's also 1-indexed this way
test-!!v1₁ : (Cons 1 Nil !!v ≤-soundness {1}) == 1
test-!!v1₁ = Refl

-- this correctly fails with the wrong proof!
-- and it's also 1-indexed this way
-- in fact this fails!
-- test-!!v1₀ : (Cons 1 Nil !!v ≤-soundness {0}) == 1
-- test-!!v1₀ = Refl

test-!!v2₁ : (Cons 1 (Cons 2 Nil) !!v ≤-soundness {1}) == 1
test-!!v2₁ = Refl

test-!!v2₂ : (Cons 1 (Cons 2 Nil) !!v ≤-soundness {2}) == 2
test-!!v2₂ = Refl

test-!!v2₃ : (Cons 1 (Cons 2 Nil) !!v ≤-soundness {3}) == {!   !}
test-!!v2₃ = Refl

testTranspose3₃ : transpose matrix3₃ == 
    Cons (Cons 1 (Cons 4 (Cons 7 Nil))) (
    Cons (Cons 2 (Cons 5 (Cons 8 Nil))) (
    Cons (Cons 3 (Cons 6 (Cons 9 Nil))) 
    Nil))
testTranspose3₃ = Refl

-- test that it works correctly on non-square matrices
testTranspose3₂ : transpose matrix3₂ == 
    Cons (Cons 1 (Cons 4 Nil)) (
    Cons (Cons 2 (Cons 5 Nil)) (
    Cons (Cons 3 (Cons 6 Nil)) 
    Nil))
testTranspose3₂ = Refl


----------------------
----- Exercise 3 -----
----------------------


testCraftFin1 : craftFin {1} {≤-soundness} == Fz
testCraftFin1 = Refl

testCraftFin2 : craftFin {2} {≤-soundness} == Fs Fz
testCraftFin2 = Refl

testCraftFin3 : craftFin {3} {≤-soundness} == Fs (Fs Fz)
testCraftFin3 = Refl


testPlan1 : plan {1} == Cons Fz Nil
testPlan1 = Refl

-- not sure if this is what we want though
testPlan2 : plan {2} == Cons (Fs Fz) (Cons (Fs Fz) Nil)
testPlan2 = Refl

testForget-difficult : forget-difficult {3} (Fs (Fs Fz)) == 3
testForget-difficult = Refl

testForget : forget (Fs (Fs Fz)) == 3
testForget = Refl


----------------------
----- Exercise 4 -----
----------------------


-- a mess, no tests
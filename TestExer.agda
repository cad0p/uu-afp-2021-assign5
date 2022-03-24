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


testTranspose3₃ : transpose matrix3₃ == 
    Cons (Cons 2 (Cons 5 (Cons 8 Nil))) (
    Cons (Cons 3 (Cons 6 (Cons 9 Nil))) (
    Cons (Cons 1 (Cons 4 (Cons 7 Nil))) 
    Nil))
testTranspose3₃ = Refl

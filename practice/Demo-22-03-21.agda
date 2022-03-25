module Demo-22-03-21 where

import Demo-22-03-14
open Demo-22-03-14

import Demo-22-03-16
open Demo-22-03-16

head : (default : a) → List a -> a
head d (cons x xs) = x
head d (nil) = d

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

maybeHead :  List a -> Maybe a
maybeHead nil         = nothing
maybeHead (cons x xs) = just x

vhead : Vec a (succ n) → a
vhead (cons x xs) = x

-- the element at index n index of the list
_!!_ : List a → ℕ → Maybe a
nil !! n = nothing
cons x xs !! zero = just x
cons x xs !! (succ n) = xs !! n

-- _≤_ : ℕ → ℕ → Set
-- _≤_ = {!   !}
-- actually he switched to a datatype:
data _≤_ : ℕ → ℕ → Set where
  base : {n : ℕ} → zero ≤ n
  -- suppose we know that 
  step : {n m : ℕ} → n ≤ m → succ n ≤ succ m


-- quick test: can I prove this inequality?
test3≤5 : 3 ≤ 5
test3≤5 = step (step (step base))
-- yes!

-- let's try to prove something wrong
test5≤3 : 5 ≤ 3
test5≤3 = step (step (step {! stuck!  !}))


length : List a → ℕ
length nil = zero
length (cons x xs) = succ (length xs)


-- ok here we got distracted trying to prove antiSym
antiSym : (n m : ℕ) → n ≤ m → m ≤ n → n ≡ m
-- here i know that p₁ is base because it's zero ≤ m
-- the dot is added by Agda because when you pattern match
-- on p₁ then the only way that that holds is if m is zero
-- so automatic substitution
antiSym zero .zero base base = refl
antiSym (succ n) (succ m) (step p₁) (step p₂) = 
  let ih = antiSym n m p₁ p₂ in cong succ ih

-- underscores is when Agda knows which numbers are there

-- proving that succ is not restrictive:
proof≤succ : {n m : ℕ} → n ≤ m → n ≤ succ m
proof≤succ {zero} {m} base = base
proof≤succ {succ n} {succ m} (step p) = 
  let ih = proof≤succ {n} {m} p in step ih


-- actually I need to prove that succ n ≤ m → n ≤ m
proofLower≤Same : {n m : ℕ} → succ n ≤ m → n ≤ m
proofLower≤Same {zero} {.(succ _)} (step p) = base
proofLower≤Same {succ n} {.(succ _)} (step p) = step (proofLower≤Same p)


-- better way to make this function total: lookup!
-- this will be the precondition to this function to succeed
-- pre is a precondition: an extra proof that we need to pass in
-- to guarantee that we are not calling any out of bounds lookup
-- coming back to this: we also have to say that it's strictly lower
lookup : (xs : List a) → (n : ℕ) → 1 ≤ n → n ≤ length xs → a
lookup nil  zero    ()   pre₂
lookup nil (succ n) pre₁ ()
lookup (cons x xs) (succ zero) (step base) (step base) = x
lookup (cons x xs) (succ (succ n)) (step pre₁) (step pre₂) = 
  lookup xs (succ (n)) (step base) pre₂
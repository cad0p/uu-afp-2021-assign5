module Demo-22-03-16 where

import Demo-22-03-14
open Demo-22-03-14

-- * More Agda
-- exploring Agda as a proof assistant

variable
    m : ℕ

-- here you don't typecheck and run, you do it at the same time
vappend : Vec a n → Vec a m → Vec a (n + m)
vappend nil ys = ys
vappend (cons x xs) ys = cons x (vappend xs ys)
-- Agda will use the definition of plus to simplify the type involved

-- I can show that they are β equal


-- type checker is doing evaluation for us
example : Vec Bool (succ (succ (zero)) + succ (zero))
example = cons true (cons true (cons true nil))

-- Agda doesn't usually ship with libraries and we are not going to use it

-- we can use this builtin though
{-# BUILTIN NATURAL ℕ #-}

-- it simplifies the natural numbers understanding
example2 : Vec Bool (2 + 1)
example2 = cons true (cons true (cons true nil))

-- quick example of proving stuff
data IsEven : ℕ → Set where
    IsZero : IsEven 0
    IsSS : IsEven n → IsEven (succ (succ (n)))

isEven4 : IsEven 4
isEven4 = IsSS (IsSS IsZero)

-- isEven1 : IsEven 1
-- isEven1 = {!   !}
-- No solution found

data _≡_ (x : a) : a → Set where
    refl : x ≡ x
    -- reflexivity

-- also easier definition:
-- data Equal : a → a → Set where
--     reflEqual : {x : a} → Equal x x

simpleProof : (1 + 2) ≡ 3
simpleProof = refl

even? : ℕ → Bool
even? 0 = true
even? 1 = false
even? (succ (succ n)) = even? n

-- it's a function that will construct 'IsEven n' for me
soundness : (n : ℕ) → even? n ≡ true → IsEven n
soundness zero refl = IsZero
-- () means that the argument at this position is impossible
soundness (succ zero) ()
soundness (succ (succ (n))) p = IsSS (soundness n p)

isEven1024 : IsEven 1024
isEven1024 = soundness 1024 refl

-- all kind of evaluation for type correctness
-- ASTs?

-- it's not unit testing though

-- basically the type system runs functions
unitTestPlusCommutes3-4 : (3 + 4) ≡ (4 + 3)
unitTestPlusCommutes3-4 = refl

data Empty : Set where

wrong : IsEven 1 → Empty
wrong = λ ()


-- Curry Howard Correspondence
-- rules for typing computer programs and for formal logic
-- they are very close

{-

-- the implication

A ⇒ B     A
-----------
    B


Γ ⊢ f : σ → τ   Γ ⊢ x : σ
---------------------------
   Γ ⊢ f x : τ



  A          B
--------------------
      A ∧ B

     A
--------------
    A ∨ B

     B
----------------
    A ∨ B
 
Logic          Programming Languages
 ⇒             →
 ∧             Pair (,) / Product
 ∨             Either / Sum 
 False         Empty
 ¬ P           P → Empty
  / P ⇒ False
 True          unit
 ∀x P(x)       (x : A) → P x ⇒ like in soundness example
 ∃x P(x)       
   data Σ (A : Set) (P : A → Set)
      _,_ : (x : A) -> P x -> Σ A P
    -- it's a dependent version of Pairs
    -- you have an x of type A and a proof that P holds for that x
 
  ¬ ¬ P -> P


  ...

you need quantifiers and dependent types

-}

data Either (a b : Set) : Set where
    inl : a → Either a b
    inr : b → Either a b

-- P could be anything, empty or proposition
-- constructive logic
-- you can't use p or not p is true, or not not p is true

-- in haskell you can do partial functions and errors
-- like head [] etc
-- in Agda:

data Pair (a b : Set) : Set where
    _,_ : a → b → Pair a b

swap : Pair a b → Pair b a
swap (x , x₁) = (x₁ , x)

-- you can't define head in Agda because it's partial

lemma1 : (n : ℕ) → (0 + n) ≡ n
lemma1 n = refl


-- before we prove lemma2, we need transitivity, symmetry and congruence

trans : {x y z : a} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {x y : a} → x ≡ y → y ≡ x
sym refl = refl
-- sym : (x y : a)
-- sym x .x refl
-- the only value that I can pass to y is x itself

cong : {x y : a} → (f : a → b) → x ≡ y → f x ≡ f y
cong f refl = refl

lemma2 : (n : ℕ) → (n + 0) ≡ n
lemma2 zero = refl
-- cong: it suffices to prove that x ≡ y to prove that succ x ≡ succ y
-- ih is induction hypothesis (lemma2 n)
lemma2 (succ n) = cong (λ x → succ x) (lemma2 n)

lemma3 : (n m : ℕ) → (n + m) ≡ (m + n)
lemma3 zero m = sym (lemma2 m)
lemma3 (succ n) m = sym {!  !}

-- cog have meta programs called tactics which will generate these proofs for you
-- the other useful thing
-- we could make a Domain Specific Language to do this 

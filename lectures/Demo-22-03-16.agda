module Demo-22-03-16 where

-- Ctrl-c Ctrl-l loads the file

data Bool : Set where
  true  : Bool
  false : Bool

-- Ctr-c Ctrl-, -- context information
-- Ctrl-c Ctrl-c
not : Bool → Bool
not true  = false
not false = true

if_then_else_ : {a : Set} → Bool → a  → a → a
if true then t else e = t
if false then t else e = e

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

data List (a : Set) : Set where
  nil : List a
  cons : a → List a → List a

append : {a : Set} → List a → List a → List a
append {a} nil ys = ys
append {a} (cons x xs) ys = cons x (append {a} xs ys)

id : {a : Set} → a → a
id x = x

variable
  a b : Set
  n m : ℕ
map : (a → b) → List a → List b
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

appendBool : List Bool → List Bool → List Bool
appendBool bs1 bs2 = append {Bool} bs1 bs2

data Vec (a : Set) : ℕ → Set where
  nil : Vec a zero
  cons : a → Vec a n → Vec a (succ n)

vmap : (a → b) → Vec a n → Vec b n
vmap f nil = nil
vmap f (cons x xs) = cons (f x) (vmap f xs)

-- _+_ : ℕ → ℕ → ℕ
-- zero + m = m
-- (succ n) + m = succ (n + m)

vappend : Vec a n → Vec a m → Vec a (n + m)
vappend nil ys = ys
vappend (cons x xs) ys = cons x (vappend xs ys)

{-# BUILTIN NATURAL ℕ #-}

example : Vec Bool (2 + 1)
example = cons true (cons true (cons false nil))

{-

 Γ ⊢ t : σ      σ ≡β τ
----------------------
   Γ ⊢ t : τ

-}

-- {-# TERMINATING #-}
-- loop : a
-- loop = loop

-- _+_ : ℕ → ℕ → ℕ

data _≡_ (x : a) : a → Set where
  refl : x ≡ x
  
simpleProof : (1 + 2) ≡ 3
simpleProof = refl

data IsEven : ℕ → Set where
  IsZero : IsEven 0 -- Zero is an even number
  IsSS : IsEven n → IsEven (succ (succ n)) -- if n is even, then so is (2 + n)

data ⊥ : Set where

wrong : IsEven 1 -> ⊥
wrong ()

even? : ℕ → Bool
even? zero = true
even? (succ zero) = false
even? (succ (succ n)) = even? n

soundness : (n : ℕ) → even? n ≡ true → IsEven n
soundness zero refl        = IsZero
soundness (succ zero) ()
soundness (succ (succ n)) p = IsSS (soundness n p) 

test5 = even? 5

isEven4 : IsEven 1024
isEven4 = soundness 1024 refl

isEven5 : IsEven 5
isEven5 = soundness 5 {!!}

unitTestPlusCommutes3-4 : (3 + 4) ≡ 7
unitTestPlusCommutes3-4 = refl

unitTestPlusCommutes5-6 : (5 + 6) ≡ 11
unitTestPlusCommutes5-6 = refl

-- Curry Howard Correspondence
{-

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
 ∧             Pair (,)
 ∨             Either / Sum 
 False         Empty
 ¬ P           P → Empty
  / P ⇒ False
 True          unit
 ∀x P(x)       (x : A) → P x
 ∃x P(x)       
   data Σ (A : Set) (P : A → Set)
      _,_ : (x : A) -> P x -> Σ A P
 
  ¬ ¬ P -> P


  ...

-}

data Either (a b : Set) : Set where
  inl : a -> Either a b
  inr : b -> Either a b

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

swap : Pair a b -> Pair b a
swap (x , y) = (y , x)

lemma1 : (n : ℕ) → (0 + n) ≡ n
lemma1 n = refl

sym : {x y : a} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : a} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {x y : a} → (f : a → b) → x ≡ y -> f x ≡ f y
cong f refl = refl

lemma2 : (n : ℕ) → (n + 0) ≡ n
lemma2 zero = refl
lemma2 (succ n) =
  let ih = lemma2 n in
  cong succ ih

lemma3 : (n m : ℕ) → (n + m) ≡ (m + n)
lemma3 zero m = sym (lemma2 m)
lemma3 (succ n) m = {!!}

_■ : (x : a) → x ≡ x
_■ x = refl

infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : a) {y z : a} → (x ≡ y) → (y ≡ z) → x ≡ z
x ⟨ p ⟩ q = trans p q 

proof : (n : ℕ) → (n + 0) ≡ n
proof zero = refl
proof (succ n) =
  let ih = proof n in 
  (succ n + 0)
    ⟨ refl ⟩ -- definition of plus
  succ (n + 0)
    ⟨ cong succ ih ⟩  
  succ n ■

proof2 : (x y z : ℕ) → ((x + y) + z) ≡ (x + (y + z))
proof2 zero y z = refl
proof2 (succ x) y z =
  let ih = proof2 x y z in
  (succ x + y) + z
    ⟨ cong succ ih ⟩
  (succ x + (y + z)) ■

postulate
  excludedMiddle : {P : Set} -> Either P (P → ⊥)
--   undefined : a

-- empty : Empty
-- empty = undefined

-- addingTwice : (n : ℕ) → IsEven (n + n)
-- addingTwice zero = IsZero
-- addingTwice (succ n) = let ih = addingTwice n in {!!}

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

_!!_ : List a → ℕ → Maybe a
nil !! n = nothing
cons x xs !! zero = just x
cons x xs !! (succ n) = xs !! n

data _≤_ : ℕ → ℕ → Set where
  base : {n : ℕ} → zero ≤ n
  step : {n m : ℕ} → n ≤ m →  succ n ≤ succ m

antiSym : (n m : ℕ) → n ≤ m → m ≤ n → n ≡ m
antiSym zero zero base base = refl
antiSym (succ n) (succ m) (step p1) (step p2) =
  let ih = antiSym n m p1 p2 in cong succ ih

antiSym' : (n m : ℕ) → n ≤ m → m ≤ n → n ≡ m
antiSym' zero zero base base = refl
antiSym' .(succ _) .(succ _) (step p1) (step p2) =
  let ih = (antiSym' _ _ p1 p2) in cong succ ih

test≤ : 3 ≤ 5
test≤ = step (step (step base))

test2 : 5 ≤ 3
test2 = step (step (step {!stuck!!}))

length : List a → ℕ
length nil = zero
length (cons x xs) = succ (length xs)

lookup : (xs : List a) → (n : ℕ) → succ n ≤ (length xs) → a
lookup nil n ()
lookup (cons x xs) zero pre = x
lookup (cons x xs) (succ n) (step pre) = lookup xs n pre

_≤?_ : ℕ -> ℕ -> Bool
zero ≤? m = true
succ n ≤? zero = false
succ n ≤? succ m = n ≤? m

record ⊤ : Set where
  constructor tt

So : Bool → Set
So true = ⊤
So false = ⊥

≤-soundness : {n m : ℕ} → {p : So (n ≤? m)} → n ≤ m
≤-soundness {zero} {m} = base
≤-soundness {succ n} {succ m} {b} = step (≤-soundness {n} {m} {b})

anotherTest = lookup (cons 23 (cons 243 (cons 5 (cons 33 nil)))) 2 (≤-soundness)

data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (succ n)
  fsucc : ∀ {n} → Fin n → Fin (succ n)

-- Fin 0: 
-- Fin 1: fzero
-- Fin 2: fzero, fsucc fzero
-- Fin 3: fzero, fsucc fzero, fsucc (fsucc fzero)

vlookup : Vec a n → Fin n →  a
vlookup (cons x xs) fzero = x
vlookup (cons x xs) (fsucc n) = vlookup xs n

filter : (a → Bool) → List a → List a
filter p nil = nil
filter p (cons x xs) = if p x then cons x (filter p xs) else filter p xs

-- filterCase : (a → Bool) → List a → List a
-- filterCase p nil = nil
-- filterCase p (cons x xs) with p x
-- ... | true = cons x (filter p xs)
-- ... | false = filter p xs

data _⊆_ {a : Set} : List a → List a → Set where
  Base : nil ⊆ nil
  Keep : {x : a} {xs ys : List a} → xs ⊆ ys → (cons x xs) ⊆ (cons x ys)
  Drop : {x : a} {xs ys : List a} → xs ⊆ ys → xs ⊆ (cons x ys)  

filter-lemma : (p : a → Bool) → (xs : List a) → filter p xs ⊆ xs
filter-lemma p nil = Base
filter-lemma p (cons x xs) with (p x)
... | true = Keep (filter-lemma p xs)
... | false = Drop (filter-lemma p xs)
  where
  -- Gets introduced under the hood
  helper : (b : Bool) → (if b then cons x (filter p xs) else filter p xs) ⊆ cons x xs
  helper true = Keep (filter-lemma p xs)
  helper false = Drop (filter-lemma p xs)

countTrues : (p : a → Bool) → (xs : Vec a n) → ℕ
countTrues p nil = zero
countTrues p (cons x xs) = if p x then succ (countTrues p xs) else countTrues p xs

filterVec : (p : a → Bool) → (xs : Vec a n) → Vec a (countTrues p xs)
filterVec p nil = nil
filterVec p (cons x xs) with p x
... | true = cons x (filterVec p xs)
... | false = filterVec p xs

-- revAppend : Vec a n -> Vec a m -> Vec a (m + n)
-- revAppend = {!!}

coerce : (n ≡ m) → Vec a n → Vec a m
coerce refl xs = xs

trans≡ : (x y z : ℕ) → x ≡ y → y ≡ z → x ≡ z
trans≡ x .x .x refl refl = refl

monoidVec : (xs : Vec a n) -> coerce {!!} (vappend xs nil) ≡ vappend nil xs
monoidVec xs = {!!}

-- C-c C-a


toFin : (n : ℕ) → (Fin {!succ n!})
toFin n = {!!}

{-# OPTIONS --allow-unsolved-metas #-}


module Exercise where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat 
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat -> Nat -> Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat} -> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

-- data Unit : Set where
--   unit : Unit
record Unit : Set where
  constructor unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

-- data Vec (a : Set) : Nat -> Set where
--   Nil : Vec a 0
--   Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

-- here I'm case splitting on n
-- after trying without case splitting and failing
-- the result is a vector with n xs, like {1,1,1,1} if n==4
pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} {a} x = Nil
pure {Succ n} {a} x = Cons x (pure {n} {a} x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> v??? = Nil
Cons x??? v??? <*> Cons x??? v??? = Cons (x??? x???) (v??? <*> v???)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x v) = Cons (f x) (vmap f v)

_+v_ : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
Nil +v ys = ys
(Cons x xs) +v (Cons y ys) = Cons (x + y) (xs +v ys)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
-- n columns, m rows
Matrix a n m = Vec (Vec a n) m 

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
-- there's nothing to add
madd Nil yss = yss
-- we have depleted the row
madd (Cons xss xss???) (Cons yss yss???) = Cons (xss +v yss) (madd xss??? yss???)


-- we need to define another function to create a vector of 
-- size n with all 0s
zeroVec : (n : Nat) -> Vec Nat n
zeroVec Zero = Nil
zeroVec (Succ n) = Cons 0 (zeroVec n)



-- we need to define function that creates
-- a vector of size n with a 1 in position i, 0 < i <= n
-- idVec {1} 1 == Cons 1 Nil
idVec : {n : Nat} -> Nat -> Maybe (Vec Nat n)
idVec {Zero} Zero = Just Nil
idVec {Zero} (Succ i) = Nothing
idVec {Succ n} Zero = Nothing
idVec {Succ n} 1 = Just (Cons 1 (zeroVec n))
idVec {Succ n} (Succ i) with idVec {n} i
... | Just x = Just (Cons 0 x)
... | Nothing = Nothing


-- now we get a reverse id matrix, with the diagonal from
-- lower left to upper right
-- to solve this we need a function that maps i to n - i
-- this evaluates to Zero if n < i
compNat : Nat -> Nat -> Nat
compNat (Succ n) (Succ i) = compNat n i
compNat n i = n


-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {n} = helper n where 
  -- r row is actually n - row
  -- which is compNat n r
  -- n is the number of columns
  helper : (r : Nat) -> Matrix Nat n r
  helper Zero = Nil
  helper (Succ r) with idVec {n} (compNat n r)
  ... | Just x = Cons x (helper r)
  -- the case below is actually unreachable
  -- ? why doesn't Agda tell us?
  ... | Nothing = Cons (zeroVec n) (helper r)




-- ? we need to define stuff before, cannot reference after?

-- ?v why can't we overload the plus?
-- we can with general typing


--- Start of matrix transposition --

-- to define matrix transposition you are faced with this:
{-
    Cons (Cons 1 (Cons 2 (Cons 2 Nil)))(
    Cons (Cons 4 (Cons 5 (Cons 6 Nil)))(
    Cons (Cons 7 (Cons 8 (Cons 9 Nil))) 
    Nil))

    which is basically this:
    1 2 3       1 4 7
    4 5 6   ->  2 5 8
    7 8 9       3 6 9

    of course it can also be rectangular, not square

    our helper function will have to read 
    Cons xs xss
    where xs = 1 2 3 and create 
    1 (f??? xss)
    2 (f??? xss)
    3 (f??? xss)


    so the initial case means that we have to take xs
    and depending on the row you are in (the parameter),
    the function will only act on that particular element
    for this we need the !! operator for vectors
    
    so this helper function will have to take
    the Matrix of length c r, a Nat for the index,
    and it will return a Vec of size r

    and it will recursively call itself with r - 1

    the problem here is that you have to call this function for each row
    so i guess you will have another function g that gets as input
    a matrix of size c r and returns a matrix of size r c,
    which is exactly transpose

    so we have to have a real function g that actually is recursive and
    gets as input the whole matrix and a decreasing index
    (which is initially the number of columns) and returns a
    matrix of size r c???, where c??? represents the old columns and the new rows

-}

-- Define !! for vectors to get the index
_!!v-dumb_ : {n : Nat} {a : Set} -> Vec a n -> Nat -> Maybe a
Nil !!v-dumb i = Nothing
Cons x xs !!v-dumb Zero = Just x
Cons x xs !!v-dumb Succ i = xs !!v-dumb i


-- Define matrix transposition
transpose-dumb : {c r : Nat} {a : Set} -> Matrix a c r -> Matrix a r c
transpose-dumb {c} {r} xss = g xss c where
  f : {c r : Nat} {a : Set} -> Matrix a c r -> Nat -> Vec a r
  f Nil i = Nil
  f (Cons xs xss) i 
   with xs !!v-dumb i 
  ... | Just x = Cons x (f xss i)
  -- ? why does Agda not realize it's unreachable
  ... | Nothing with xs
            -- no solution here
            -- haha it seems that it doesn't complain with leaving it like this
  ...              | Nil = Cons {!   !} {!   !}
            -- i guess just take the first element then
  ...              | Cons x??? xs??? = Cons x??? (f xss i)

  g : {c r : Nat} {a : Set} -> Matrix a c r -> (c??? : Nat) -> Matrix a r c??? 
  g {c} {r} xss Zero = Nil
  g {c} {r} xss (Succ c???) = Cons (f xss (compNat c (Succ c???))) (g xss c???)

-- ok so i tried with !! but
-- let's make it into a total function

-- first we need empty and unit constructors
-- edit: they were already defined, skipping
-- record ??? : Set where
--   constructor tt

-- data ??? : Set where


-- then we need to define ???
data _???_ : Nat -> Nat -> Set where
  Base : {m : Nat} -> Zero ??? m
  Step : {n m : Nat} -> n ??? m -> Succ n ??? Succ m


-- now the idea is to define a soundness function for ???

-- first we define a bool function
_????_ : Nat -> Nat -> Bool
Zero ???? m = True
Succ n ???? Zero = False
Succ n ???? Succ m = n ???? m

-- then we convert this to a Set
-- wanted to call this BoolToSet but so also works so so
so : Bool -> Set
so True = Unit
so False = Empty


-- then we can define the soundness!
-- that automatically constructs the proof..
???-soundness : {n m : Nat} -> {p : so (n ???? m)} -> n ??? m
???-soundness {Zero} {m} {p} = Base
???-soundness {Succ n} {Succ m} {p} = Step (???-soundness {n} {m} {p})

-- necessary for the new g in transpose
proof-n???n : {n : Nat} -> n ??? n
proof-n???n {Zero} = Base
proof-n???n {Succ n} = Step proof-n???n

-- also that n ??? m ??? n ??? Succ m
proof-n???Succm : {n m : Nat} -> n ??? m ??? n ??? Succ m
proof-n???Succm {Zero} {m} p = Base
proof-n???Succm {Succ n} {Succ m} (Step p) = Step (proof-n???Succm p)

-- last proof needed: n ??? m ??? compNat m n ??? m
proofCompNat : {n m : Nat} -> n ??? m -> compNat m n ??? m
proofCompNat {Zero} {Zero} Base = Base
proofCompNat {Zero} {Succ m} Base = Step proof-n???n
proofCompNat {Succ n} {.(Succ _)} (Step p) = 
  let ih = proofCompNat p in proof-n???Succm ih

-- so now we will redefine !!v
-- now taking a proof instead of the maybe construct
_!!v_st_ : {n : Nat} {a : Set} -> Vec a n -> (i : Nat) -> Succ i ??? n -> a 
-- st stands for such that
(Cons x xs) !!v Zero     st p        = x
(Cons x xs) !!v (Succ i) st (Step p) = xs !!v i st p

-- but can we do better?
_!!v_ : {n i : Nat} {a : Set} -> Vec a n -> Succ i ??? n -> a 
_!!v_ {.(Succ _)} {Zero} (Cons x xs) p = x
_!!v_ {.(Succ _)} {Succ i} (Cons x xs) (Step p) = xs !!v p

-- now we can define a better transpose
transpose : {c r : Nat} {a : Set} -> Matrix a c r -> Matrix a r c
transpose {Zero} xss = Nil
-- weird case
transpose {Succ c} Nil = Cons Nil (transpose {c} Nil)
transpose {Succ c} (Cons xs xss) = g (Cons xs xss) 
    (Step (proof-n???n {c})) where
  f : {c r i : Nat} {a : Set} -> Matrix a c r -> Succ i ??? c -> Vec a r
  f {i} Nil p = Nil
  f {i} (Cons xs xss) p = Cons (xs !!v p) (f xss p) 

  g : {c r c??? : Nat} {a : Set} -> Matrix a c r ->  c??? ??? c -> Matrix a r c??? 
  g {c} {r} {Zero} xss p = Nil
  g {.(Succ _)} {r} {Succ c???} xss (Step p) = 
    Cons (f xss (Step (proofCompNat p))) (g xss (proof-n???Succm p))
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.


-- ok so this needs an helper that crafts
-- Fs (Fs (Fs (Fz))) etc for us
-- actually we need one that allows for recursion
-- and that has type 
craftFin : {n : Nat} {p : 1 ??? n} -> Fin (n)
craftFin {Succ Zero} = Fz
craftFin {Succ (Succ n)} {Step p} = 
  Fs (craftFin {Succ n} {Step Base})

-- after this i need the helper function to be called

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = 
  f {Succ n} {Succ n} {???-soundness} {Step proof-n???n} where
  f : {n m : Nat} {p??? : 1 ??? n} {p??? : m ??? n}-> Vec (Fin n) m
  f {Succ n} {Zero} = Nil
  f {Succ n} {Succ m} {p???} {Step p???} = Cons 
    (craftFin {Succ n} {p???}) 
    (f {Succ n} {m} {p???} {proof-n???Succm p???})


-- for forget, we have to define a function that 
-- has one more parameter to keep track of the number
-- by counting upwards


-- Define a forgetful map, mapping Fin to Nat
forget-difficult : {n : Nat} -> Fin n -> Nat
forget-difficult {Succ n} fi = f (Succ n) 0 fi where
  f : (n i : Nat) -> Fin n -> Nat
  f (Succ n) i Fz = Succ i
  f (Succ n) i (Fs fi)= f n (Succ i) fi

-- also, more simply:
forget : {n : Nat} -> Fin n -> Nat
forget {Succ n} fi = Succ n


-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Succ n} fi = Fs fi

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {n} fi = {!   !}

-- here the goal is 'forget fi == Succ n'
-- but actually fi is a 'Fin n', so it should have 'n'
-- as result of 'forget fi'
-- so it's not correct, probably I have misunderstood Fin

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- for the covering function we need a helper function
-- that counts the iterative calls

-- Show that there is a 'covering function'
cmp-nonRec : (n m : Nat) -> Compare n m 
cmp-nonRec Zero Zero = Equal
cmp-nonRec Zero (Succ m) = LessThan m
cmp-nonRec (Succ n) Zero = GreaterThan n
cmp-nonRec (Succ n) (Succ m) = {! cmp n m  !}


n==n+0 : {n : Nat} -> n == (n + 0)
n==n+0 {Zero} = Refl
n==n+0 {Succ n} = cong Succ n==n+0

=reflexivity : {a : Set} {x y : a} -> x == y -> y == x
=reflexivity {a} {x} {.x} Refl = Refl

n+1==Succn : {n : Nat} -> (n + 1) == Succ n
n+1==Succn {Zero} = Refl
n+1==Succn {Succ n} = cong Succ n+1==Succn


-- now I need the proof that (n + Succ m) == Succ (n + m)
+associativity : {n m : Nat} -> (n + Succ m) == Succ (n + m)
+associativity {Zero} {m} = cong Succ Refl
+associativity {Succ n} {m} = 
  let ih = +associativity {n} {m} in 
    cong Succ ih


-- tried to apply it below with no luck
+assGet : {n m : Nat} -> (n + Succ m) == Succ (n + m) -> Nat
+assGet {n} {m} p = Succ (n + m)


n+Succm== : {n m : Nat} 
  -> (n + m) == (m + n) -> (n + Succ m) == (m + Succ n)
n+Succm== {Zero} {Zero} p = Refl
-- here I need to prove that n+1==Succm
n+Succm== {Zero} {Succ m} p = cong Succ (=reflexivity (n+1==Succn {m}))
n+Succm== {Succ n} {Zero} p = cong Succ n+1==Succn
n+Succm== {Succ n} {Succ m} p = 
  let ih = n+Succm== {n} {m} in 
    cong Succ {!   !}

commutes-n+m : {n m : Nat} -> (n + m) == (m + n)
commutes-n+m {Zero} {Zero} = Refl
commutes-n+m {Succ n} {Zero} = 
  cong Succ (=reflexivity (n==n+0 {n}))
commutes-n+m {Zero} {Succ m} = cong Succ (n==n+0 {m})
commutes-n+m {Succ n} {Succ m} = 
  -- here we need proof that:
  -- (n + m) == (m + n) -> (n + Succ m) == (m + Succ n)
  let ih = commutes-n+m {n} {m} in 
  cong Succ (n+Succm== ih)

cmp : (n m : Nat) -> Compare n m
cmp n m = f n m 0 (commutes-n+m {0} {m}) where
  -- here Agda being stupid, cannot put (n + i)
  -- because of how + is defined
  -- maybe reflexivity could help..
  f : (n m i : Nat) -> (i + m) == (m + i) -> Compare (i + n) (i + m)
  -- and now cannot put this because it shows
  -- now as Compare (i + 0) (i + 0)
  -- while it wants Compare i i
  f Zero Zero i p = {! Equal {i} !}
  f Zero (Succ m) i p = {! LessThan {m + i}  !}
  f (Succ n) Zero i p = {! GreaterThan {n + i}  !}
  -- haha error: (i + Succ m) != (Succ (i + m)) of type Nat
  f (Succ n) (Succ m) i p = {! f n m (Succ i) p  !}

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
... | LessThan k = k
... | Equal = 0
... | GreaterThan k = k

-- if only cmp worked..

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero n = sym n==n+0

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc n m = sym +associativity

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes n m = commutes-n+m {n} {m}

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) Zero Zero = distributivity n Zero Zero
distributivity (Succ n) Zero (Succ k) = 
  let ih = distributivity n Zero (Succ k) in 
  -- also here it differs by k
    {!  !}
distributivity (Succ n) (Succ m) Zero = 
  let ih = distributivity n (Succ m) Zero in 
    -- this one differs by -m (not sure how to prove here)
    cong Succ ({!   !})
distributivity (Succ n) (Succ m) (Succ k) = 
  let ih = distributivity n m k in 
    cong Succ {!   !}

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {a} {Nil} = Base
SubListRefl {a} {Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base sl??? = sl???
SubListTrans (Keep sl???) (Keep sl???) = Keep (SubListTrans sl??? sl???)
SubListTrans (Keep sl???) (Drop sl???) = Drop (SubListTrans (Keep sl???) sl???)
SubListTrans (Drop sl???) (Keep sl???) = Drop (SubListTrans sl??? sl???)
SubListTrans (Drop sl???) (Drop sl???) = 
  Drop (SubListTrans sl??? {! sl???  !})


-- ok we need also and:
-- _???_ : {a : Set} {x y : a} -> x == y -> Bool -> Bool
-- Refl ??? True   = True
-- Refl ??? False  = False



-- how do I prove that two list are equal?
-- I just check each element
_==?l_ : {a : Set} -> List a -> List a -> Bool
Nil ==?l Nil = True
Nil ==?l Cons x ys = False
Cons x xs ==?l Nil = False
Cons x xs ==?l Cons y ys =  {! (x == y) ??? (xs ==?l ys) !}


SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base sl??? = Refl
SubListAntiSym {a} {xs} {ys} (Keep sl???) (Keep sl???) = {!   !}
SubListAntiSym (Keep sl???) (Drop sl???) = {!   !}
SubListAntiSym (Drop sl???) sl??? = {!   !}

-- ok I can't do it in general because I can't prove the equality of x == y
-- for each set

_???_ : Bool -> Bool -> Bool
True ??? b??? = b???
False ??? b??? = False


_==?_ : Nat -> Nat -> Bool
Zero ==? Zero = True
Zero ==? Succ y = False
Succ x ==? y = x ==? y

-- but I can build a version that works for Nat
_==?lNat_ : List Nat -> List Nat -> Bool
Nil ==?lNat Nil = True
Nil ==?lNat Cons x ys = False
Cons x xs ==?lNat Nil = False
Cons x xs ==?lNat Cons y ys =  (x ==? y) ??? (xs ==?lNat ys)


_==lNat_ : (xs ys : List Nat) -> {p : so (xs ==?lNat ys)} -> xs == ys
(Nil ==lNat Nil) {p} = Refl
(Cons x xs ==lNat Cons y ys) {p} = {! (xs ==lNat ys) {p} !}



SubListAntiSymNat : {xs ys : List Nat} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSymNat Base sl??? = Refl
SubListAntiSymNat {xs} {ys} (Keep sl???) sl??? = {! xs ==?lNat ys  !}
SubListAntiSymNat (Drop sl???) sl??? = {!   !}

-- here I tried and I failed on doing it even only for Nat


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : {n : Nat} -> LEQ Zero n
  Step : {n m : Nat} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Step (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base ????????? = Base
leqTrans (Step ?????????) (Step ?????????) = 
  let ih = leqTrans ????????? ????????? in 
    Step ih

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Step ?????????) (Step ?????????) = cong Succ (leqAntiSym ????????? ?????????)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Base = Refl
leq<= (Step ?????????) = leq<= ?????????

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m Refl = Base
<=leq (Succ n) (Succ m) p = Step (<=leq n m p) 

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP = {!  !}

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle = {!!} 

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...


step1 : doubleNegation -> excludedMiddle
step1 dn = {!!} 

step2 : excludedMiddle -> impliesToOr
step2 = {!!}

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

----------------------
----- Exercise 9 -----
----------------------

-- Given the following data type for expressions

data Expr : Set where
  Add : Expr -> Expr -> Expr
  Val : Nat -> Expr

-- We can write a simple evaluator as follows
eval : Expr -> Nat
eval (Add l r) = eval l + eval r
eval (Val x) = x

-- We can also compile such expressions to stack machine code
-- data Cmd : Set where
--   -- stop execution and return the current stack
--   HALT : Cmd 
--   -- push a new number on the stack
--   PUSH : Nat -> Cmd -> Cmd 
--   -- replace the top two elements of the stack with their sum
--   ADD : Cmd -> Cmd

-- Stack : Set
-- Stack = List Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...


data Cmd : Nat -> Set where
  -- stop execution and return the current stack
  HALT : {n : Nat} -> Cmd n
  -- push a new number on the stack
  PUSH : {n : Nat} -> Nat -> Cmd n -> Cmd (Succ n)
  -- replace the top two elements of the stack with their sum
  ADD : {n : Nat} -> Cmd (Succ (Succ n)) -> Cmd (Succ n)

Stack : (n : Nat) -> Set
Stack n = Vec Nat n

-- so the n of the exec function is actually the return type
-- of HALT, PUSH, and ADD
-- but what we really want is to also have the original n
-- not knowing how to retrieve it, I'm going to build a function
-- that replicates the behavior described in the Cmd datatype.
oldStackSize : {n : Nat} -> Cmd n -> Nat
oldStackSize {n} HALT = n
oldStackSize {Succ n} (PUSH x c) = n
oldStackSize {n} (ADD c) = Succ n


-- I discovered through the correctness function how the
-- compiler should behave, and that it can have any stack
-- as input, not just a stack with a predefined size
-- so instead of bounding the input i have to bound the output!
-- previously it was:
-- exec : {n : Nat} -> (c : Cmd n) -> Stack (oldStackSize n) -> Stack n


-- this m is the old stack size
newStackSize : {n : Nat} -> (c : Cmd n) -> Nat -> Nat
newStackSize {Zero} HALT m = m
-- I don't know honestly if this case below is possible
newStackSize {Succ n} HALT m = {!   !}
-- let's say I want to push something to a compiler of size n - 1
-- then it becomes a compiler of size n
-- but I already have a stack of size m
-- so the result is just n + m
newStackSize {n} (PUSH x c) m = n + m
-- meanwhile here I want to add the top 2 of a compiler of size n + 1
-- I get a compiler of size n (n >= 1)
-- so basically it never consumes the existing stack
newStackSize {n} (ADD c) m = n + m
-- so we discovered that it's ac


-- this is bonkers
vecSuccAssoc : {a : Set} {n m : Nat} 
  -> Vec a (n + Succ m) -> Vec a (Succ (n + m))
vecSuccAssoc {a} {Zero} {m} v = v
vecSuccAssoc {a} {Succ n} {m} (Cons x v) = Cons x (vecSuccAssoc v)
-- same
vecSuccDistr : {a : Set} {n m : Nat} 
  -> Vec a (Succ (n + m)) -> Vec a (n + Succ m)
vecSuccDistr {a} {Zero} {m} v = v
vecSuccDistr {a} {Succ n} {m} (Cons x v) = Cons x (vecSuccDistr v)


-- Complete the following definition, executing a list of instructions
exec : {n m : Nat} -> (c : Cmd n) -> Stack m -> Stack (m + n)
-- for the same doubt explained above i'm mocking a vector.
exec {n} HALT s = append s (zeroVec n)
exec (PUSH x c) s = vecSuccDistr (Cons x (exec c s))
exec (ADD c) s = {! c  !}

------- this below is the previous attempt -----
-- not sure how to know the stack ending size
-- Complete the following definition, executing a list of instructions
-- exec : {n m : Nat} -> (c : Cmd n) -> Stack m -> Stack (newStackSize c m)
-- exec (HALT {n}) s = s
-- -- oh, interesting, even though the type is Stack n -> Stack n
-- -- here the goal is Stack (Succ n)
-- -- which is what I wanted!
-- -- actually, no, because also s now is of type Stack (Succ n)
-- -- solved with oldStackSize
-- exec (PUSH x c) s = Cons x s
-- exec (ADD c) (Cons x (Cons x??? s)) = Cons (x + x???) s


-- here I discovered that the add type is actually incorrect,
-- because ADD : {n : Nat} -> Cmd (Succ n) -> Cmd n
-- allows for the case in which you have a nil, and you will lose
-- the x information applying it
-- another alternative I explored was to allow ADD to be called 
-- even on Cons x Nil, but then I thought that the result would just
-- be the stack itself, and another constructor does this: HALT
-- so there is no need to define it for Vec Nat 1 :)
-- exec (ADD c) (Cons x Nil) = {!   !}
-- exec (ADD c) (Cons x (Cons x??? s)) = {!   !}

-- Define a compiler from expresions to instructions
compile : {n : Nat} -> Expr -> Cmd (Succ n)
compile (Add e e???) = ADD (PUSH (eval e???) (PUSH (eval e) HALT))
compile (Val x) = PUSH x HALT


-- And prove your compiler correct
-- correctness : (e : Expr)
--     (s : Stack (oldStackSize (compile e))) ->
--   Cons (eval e) s == exec (compile e) s
-- correctness e = {! !}

-- ok so the above I think doesn't work because == requires an
-- expression on the left side (this is my understanding)
-- ok no actually I don't know why it complains but I found
-- a workaround below:

-- And prove your compiler correct
-- this one has oldStackSize as yellow and exec as red
-- correctness : (e : Expr)
--     (s : Stack (oldStackSize (compile e))) ->
--     append Nil (Cons (eval e) s) == exec (compile e) s
-- correctness e = {! !}

-- this workaround is wrong though because it flips the result
-- I found in the tests..

-- so I'm defining a function that simply returns the vector
vreturn : {a : Set} {n : Nat} -> Vec a n -> Vec a n
vreturn v = v


--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
 
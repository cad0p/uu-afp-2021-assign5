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

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

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
Nil <*> v₂ = Nil
Cons x₁ v₁ <*> Cons x₂ v₂ = Cons (x₁ x₂) (v₁ <*> v₂)

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
madd (Cons xss xss₁) (Cons yss yss₁) = Cons (xss +v yss) (madd xss₁ yss₁)


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
    1 (f₁ xss)
    2 (f₂ xss)
    3 (f₃ xss)


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
    matrix of size r cᵢ, where cᵢ represents the old columns and the new rows

-}

-- Define !! for vectors to get the index
_!!v_ : {n : Nat} {a : Set} -> Vec a n -> Nat -> Maybe a
Nil !!v i = Nothing
Cons x xs !!v Zero = Just x
Cons x xs !!v Succ i = xs !!v i

-- -- apparently we have to define a mock vector for when
-- -- unreachable Nothing cases appear..
-- -- it will contain the first column, which we know it's there for sure..
-- mockVec {a : Set} -> Cons 


-- Define matrix transposition
transpose : {c r : Nat} {a : Set} -> Matrix a c r -> Matrix a r c
transpose {c} {r} xss =  g xss c where
  f : {c r : Nat} {a : Set} -> Matrix a c r -> Nat -> Vec a r
  f Nil i = Nil
  f (Cons xs xss) i 
   with xs !!v i 
  ... | Just x = Cons x (f xss i)
  -- ? why does Agda not realize it's unreachable
  ... | Nothing with xs
            -- no solution here
            -- haha it seems that it doesn't complain with leaving it like this
  ...              | Nil = Cons {!   !} {!   !}
            -- i guess just take the first element then
  ...              | Cons x₁ xs₁ = Cons x₁ (f xss i)

  g : {c r : Nat} {a : Set} -> Matrix a c r -> (cᵢ : Nat) -> Matrix a r cᵢ 
  g {c} {r} xss Zero = Nil
  g {c} {r} xss (Succ cᵢ) = Cons (f xss (compNat c (Succ cᵢ))) (g xss cᵢ)
  
  
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan = {!!}

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget = {!!}

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed = {!!}

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct = {!!}

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp = {!!}

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference = {!!}

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
plusZero = {!!}

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc = {!!}

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes = {!!}

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity = {!!}

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl = {!!}

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans = {!!}

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym = {!!}


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl = {!!}

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans = {!!}

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym = {!!}

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= = {!!}

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq = {!!} 

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP = {!!}

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
data Cmd : Set where
  -- stop execution and return the current stack
  HALT : Cmd 
  -- push a new number on the stack
  PUSH : Nat -> Cmd -> Cmd 
  -- replace the top two elements of the stack with their sum
  ADD : Cmd -> Cmd

Stack : Set
Stack = List Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total.  There are several
-- ways to fix this. One is to use vectors rather than lists to
-- represent stacks. To do so, however, you may also need to update
-- the Cmd datatype...

exec : Cmd -> Stack -> Stack
exec c = {!!}

-- Define a compiler from expresions to instructions
compile : Expr -> Cmd
compile e = {!!}

-- And prove your compiler correct
correctness : (e : Expr) (s : Stack) ->
  Cons (eval e) s == exec (compile e) s
correctness e = {!!}

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
 
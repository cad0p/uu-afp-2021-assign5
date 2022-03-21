module Demo-22-03-14 where

-- Ctrl-c Ctrl-l loads the file

-- set rather than *
data Bool : Set where
    true : Bool
    false : Bool

-- don't do pattern matching, but question mark
-- like in GHC writing an underscore, to say that
-- this is an unfinished part of my program
-- if i put cursor inside goal and do c-c,c-comma
-- i can see the goal that i need to prove, and the vars in scope
-- if I type not b = {b} ..
-- then c-c,c-c -> cases expansion
-- then you write the case (false or true), then c-c,c-a to transform it
-- or c-c,c-m when it doesn't work
not : Bool → Bool
not true  = false
not false = true

-- just put this: ifThenElse b t e = ?
-- and then load c-c,c-l
ifThenElse : Bool → Bool → Bool → Bool
ifThenElse true t e = t
ifThenElse false t e = e

-- operator language: underscores in positions where i have the parameter
if_then_else_ : Bool → Bool → Bool → Bool
if true then t else e = t
if false then t else e = e
-- so now this is just a function, rather than anything built in

-- constructors in Agda don't need to have a capital letter
-- nat is backslash b N
data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

data List (a : Set) : Set where
    nil : List a
    cons : a → List a → List a

-- scoping rules for types are different in Agda
-- the below fails, a not in scope
-- append : List a → List a → List a
-- so the first solution is to apply another argument 
-- so that it typechecks:
-- cons ? ? becomes with c-c,c-r the refinement
-- append : (a : Set) → List a → List a → List a
-- append a nil ys = ys
-- append a (cons x xs) ys = cons x (append a xs ys)

-- but the previous does not work nicely, Agda has "implicit arguments"
-- which means that it knows what a can be, at instance time
append : {a : Set} → List a → List a → List a
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)
-- append {a} (cons x xs) ys = cons x (append xs ys)
-- if you want to access the implicit argument

appendBool : List Bool → List Bool → List Bool
appendBool bs1 bs2 = append {Bool} bs1 bs2

-- map : {a : Set} {b : Set} → (a → b) → List a → List b
-- map f nil = nil
-- map f (cons x xs) = cons (f x) (map f xs)
-- map : {a b : Set} → (a → b) → List a → List b
-- you can also group the implicit arguments if they have the same signature

-- variable notation: introduces haskell convention of binding,
-- so that you can write this:

variable
    a b : Set
    n : ℕ

map : (a → b) → List a → List b
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)
-- sometime it's useful

-- the ℕ is index, a parameter
-- everything left is traditional style,
-- everything right is GADT style
data Vec (a : Set) : ℕ → Set where
    nil : Vec a zero
    cons : a → Vec a n -> Vec a (succ n)

-- here c-c,c-a works nicely to autocomplete, for some reason
vmap : (a → b) → Vec a n → Vec b n
vmap f nil = nil
vmap f (cons x xs) = cons (f x) (vmap f xs)
-- a lot of my thought goes into type signatures, it autocompletes the code nicely
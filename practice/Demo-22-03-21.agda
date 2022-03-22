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
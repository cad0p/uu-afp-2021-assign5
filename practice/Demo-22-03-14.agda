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
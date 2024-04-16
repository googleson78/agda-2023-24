{-# OPTIONS --no-unicode #-}

module Homework.Selections.Selections where

open import Lib.Nat
open import Lib.Vec
open import Lib.Sigma
open import Lib.Eq
open import Lib.Zero


{-
-- Implement less than or equal for nats, but in a different way,
-- which will also turn out to be convenient for selecting elements
-- from vectors, based on their indices
data _<S=_ : Nat -> Nat -> Set where
  -- zero should be <= zero, or alternatively,
  -- we can select the empty vec from the empty vec
  o-zero : {!!} <S= {!!}
  -- we should have some way to add sucs on the right, without making the
  -- left number bigger, so that we can prove stuff like 3 <S= 5, or alternatively
  -- we can skip selecting the head of a vector
  o-skip : {n m : Nat} -> {!!} -> ? <S= ?
  -- if n <= m, then suc n <= suc m, or alternatively,
  -- we select the head of the vector
  o-succ : {n m : Nat} -> {!!} -> ? <S= ?

-- TASK
-- some positive unit tests
_ : 1 <S= 1
_ = {!!}

_ : 1 <S= 3
_ = {!!}

_ : 3 <S= 5
_ = {!!}

-- TASK
-- In general there's more than one way in which n <S= m.
-- Prove it for n = 1 and m = 2
_ :
  (1 <S= 2) >< \p -> -- there's a proof p for 1 <S= 2
  (1 <S= 2) >< \q -> -- and a proof q for 1 <S= 2
  Not (p == q)       -- and they're different
_ = {!!}

-- It might be interesting to try to figure out how many proofs there are for n <S= m, for fixed n and m.
--
-- You can use -l in a hole for such a proof (e.g. _ : 1 <S= 4; _ = ?),
-- together with Agdas auto, to get it to list all of them.

-- TASK
-- Prove that 0 is <S= any number
-- Alternatively, this represents the "empty" selection - it selects nothing.
0<S= : (n : Nat) -> 0 <S= n
0<S= = {!!}


-- TASK
-- Prove that <S= is reflexive.
-- Alternatively, this is the selection that selects all the elements of a vector
-- similarly, we can have an "all" sub - it selects everything
-- or alternatively, a reflexivity proof
--
-- This is referred to as "the identity selection".
refl-<S= : (n : Nat) -> n <S= n
refl-<S= = {!!}

-- TASK
-- For any number, the proof that 0 is Leq to it is unique - and that's
-- the one you already implemented, i.e. 0<S=.
--
-- This may seem like a weird thing to prove, but it pops up
-- later on, when proving properties about vector selections
0<S=-unique : {n : Nat} (p : 0 <S= n) -> 0<S= n == p
0<S=-unique = {!!}

-- TASK
-- We can convert our usual <= to a selection
<=-<S= : {n m : Nat} -> n <= m -> n <S= m
<=-<S= = {!!}

-- TASK
-- and vice versa
<S=-<= : {n m : Nat} -> n <S= m -> n <= m
<S=-<= = {!!}


-- TASK
-- The actual function that does the selection.
-- The idea here is to use the proof of n <S= m to guide you on how to
-- carve out a vector of size n from the input vector of size m
select : {A : Set} {m n : Nat} -> n <S= m -> Vec A m -> Vec A n
select = {!!}


-- TASK
-- We can compose selections.
-- Alternatively, this is transitivity for _<S=_.
-- You should strive to make this as lazy as possible in its pattern matches (so as few matches as possible)
-- so that your later proofs are easier.
_S<<_ : {n m k : Nat} -> n <S= m -> m <S= k -> n <S= k
p S<< q = {!!}

-- TASK
-- Selecting a composition of selections is the same as composing invocations of the select function
select-S<< :
  {A : Set} {n m k : Nat}
  (p : n <S= m) (q : m <S= k) (xs : Vec A k) ->
  select (p S<< q) xs == select p (select q xs)
select-S<< = {!!}

-- TASK
-- Composing selections with the identity selection does nothing, i.e.
-- it's a left and right identity.
S<<-left-id : {n m : Nat} (p : n <S= m) -> (refl-<S= n S<< p) == p
S<<-left-id = {!!}

S<<-right-id : {n m : Nat} (p : n <S= m) -> (p S<< (refl-<S= m)) == p
S<<-right-id = {!!}


-- TASK
-- Selection composition is associative
S<<-assoc :
  {n m k v : Nat} (p : n <S= m) (q : m <S= k) (t : k <S= v) ->
  (p S<< q) S<< t == p S<< (q S<< t)
S<<-assoc = {!!}

-- TASK
-- We can use selections of a particular form to index into a vector
-- A selection with 1 on the left effectively means that there is only one place
-- in its construction that can have the o-succ constructor.
--
-- That's *exactly* the index of the item we want to get from the vector
-- There're som examples below that might be useful to look at.
vProject : {A : Set} {n : Nat} -> Vec A n -> 1 <S= n -> A
vProject = {!!}

-- Note the locations of the "up arrows"
_ : vProject (0 ,- 1 ,- 2 ,- []) (o-succ (o-skip (o-skip o-zero))) == 0
--            ^                   ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-succ (o-skip o-zero))) == 1
--                 ^                      ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-skip (o-succ o-zero))) == 2
--                      ^                         ^
_ = refl

-- TASK
-- We can also do the opposite.
-- If for every value of (1 <S= n) we can get back an A, we can use those values
-- to reconstruct back a vector
vTabulate : {A : Set} (n : Nat) -> (1 <S= n -> A) -> Vec A n
vTabulate = {!!}

-- TASK
-- Tabulating projections should result in the original vector
vTabulate-vProject : {A : Set} {n : Nat} -> (xs : Vec A n) -> vTabulate n (vProject xs) == xs
vTabulate-vProject = {!!}

-- TASK
-- Projecting a tabulation should result in the original tabulation
vProject-vTabulate :
  {A : Set} {n : Nat}
  (f : 1 <S= n -> A) (i : 1 <S= n) ->
  vProject (vTabulate n f) i == f i
vProject-vTabulate = {!!}

-}

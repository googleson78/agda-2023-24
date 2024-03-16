{-# OPTIONS --no-unicode #-}

module Lecture.ThreeStart where

open import Lib.Zero
open import Lib.One
open import Lib.Two

data Nat : Set where

-- examples for peanuts

-- builtin pragma with example
-- {-# BUILTIN NATURAL Nat #-}

-- indexed types
-- DrinkType
-- Drink ix by DrinkType
-- Alcohol
-- alcoholByVolume
--
-- mention homework after indexed types

-- recursive peano addition
-- _+N_ : Nat -> Nat -> Nat
-- _+N_ = ?

-- mention fixity
-- infixr 100 _+N_

-- Even as functions
-- Even as examples for an indexed data type
-- indexed vs function/calculated
-- easier to to prove vs easier to use
-- TODO: good example for easier to use

-- double : Nat -> Nat
-- and double-IsEven
-- use double to show lemma ideas and evaluation + recursive proofs
-- good motivation for == and +N-right-suc

-- NatEq

-- NatEq, TwoEq, motivation for generic Eq, requires indexed
-- _==_ with explicit arg

-- example for equality
-- A -> Zero as "not A"
-- example for "not equals"
-- the Not function

-- fixity, comparison with +N
-- infix 10 _==_

-- the _/=_ helper

-- infix 10 _/=_

-- trivial equality proof
-- +N-left-zero : (n : Nat) -> zero +N n == n
-- +N-left-zero = ?

-- matching on == proofs to reveal information (trigger unification)
-- ==-symm : {A : Set} {x y : A} -> x == y -> y == x

-- recursive equality proof as motivation for ap
-- requires application over equality ("functionality")
-- +N-right-zero : (n : Nat) -> n +N zero == n
-- +N-right-zero = ?

-- _$=_ as a helper
-- change +N-right-zero to use it instead as example

-- infixl 20 _$=_

{-
-- TASK
-- Define the set of throws you can make in "Rock paper scissors" (RPS)
data Throw : Set where

-- TASK
-- Define the relation of which throw loses to which other throw in RPS
data LosesTo : Throw -> Throw -> Set where

-- TASK
-- Prove that _==_ is transtivei
==-trans :
  {A : Set} {x y z : A} ->
  x == y ->
  y == z ->
  x == z
==-trans = {! !}

-- TASK
-- Prove that you can add a suc to the right of a _+N_
-- Note how this and +N-right-zero mirror the cases in the definition of +N
+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
+N-right-suc = {! !}

-- TASK
-- Prove +N commutative
-- Hint: you'll need to apply almost all of the tools we have about reasoning for +N and == here
+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut = {! !}

-- A definition of the relation for "less than or equal to" between naturals
data _<=_ : Nat -> Nat -> Set where
  -- We know that zero is ≤ anything else
  ozero : {x : Nat} -> zero <= x
  -- We know that if x <= y, then suc x <= suc y also
  osuc : {x y : Nat} -> x <= y -> suc x <= suc y

infix 90 _<=_

-- TASK
-- Prove that <= is reflexive
<=-refl : (n : Nat) -> n <= n
<=-refl = {! !}

-- TASK
-- Formulate and prove that for any number n, n <= 1 + n
<=-suc : {! !}
<=-suc = {! !}

-- TASK
-- Formulate and prove that <= is transitive
<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans = {! !}

-- TASK
-- Formulate and prove that <= is antisymmetric
<=-antisymm : {! !}
<=-antisymm = {! !}

-- TASK
-- Formulate and prove that it is not true that 1 + n <= n
-- This is primarily useful as a lemma
<=-refl-not-suc : ?
<=-refl-not-suc = ?

-- TASK
-- Prove that if 1 + n <= m, then n /= m
-- This is primarily useful as a lemma
<=-suc-not-eq : {n m : Nat} -> suc n <= m -> Not (n == m)
<=-suc-not-eq = ?

-- TASK
-- Similarly to how <= is defined, define "less than" for Nats
data _<_ : ? where

infix 90 _<_

-- TASK
-- Formulate and prove that n < m implies that n is not equal to m
-- Hint: You might need a lemma for == in the recursive case
<-implies-/= : ?
<-implies-/= = ?

-- TASK
-- Formulate and prove that n < m implies suc n <= m
<-implies-suc<= : ?
<-implies-suc<= = ?

-- TASK
-- Formulate and prove that n < m implies n <= m without recursion/induction.
<-implies-<= : ?
<-implies-<= = ?

-- TASK
-- Forumlate and prove that if n <= m and n is not m, then n < m
-- Hint: You'll likely need to match on the numbers and not only on the <=
-- Hint: You'll need a lemma about == in the recursive case.
<=-and-/=-implies-< : ?
<=-and-/=-implies-< = ?

-- TASK
-- Formulate and prove that < is transitive without recursion/induction.
-- You'll need to apply a lot of lemmas that we've proved thus far, and maybe
-- figure out some new ones as well.
<-trans : ?
<-trans = ?

-- TASK
-- Let's assume we have a "next" relation in the following sense:
--   x R y, iff "y" is the "next" value "after" x. An example of this is the LosesTo relation
-- Given a "next" relation, define a generalised version of the "LosesTo" relation with the following intuition:
--   In the original RPS game, rock loses to paper, and paper loses to scissors, "hence" scissors should lose to rock.
data GLosesTo {A : Set} (R : A -> A -> Set) : A -> A -> Set where

-- TASK
-- Write some unit tests for your new yummy GLosesTo
-- You'll probably need a new enum data type with more values in it to do so.
--
-- Are there any properties that hold for GLosesTo, based on the properties of R?
-}

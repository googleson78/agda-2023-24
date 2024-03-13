{-# OPTIONS --no-unicode #-}

module Lecture.ThreeLive where

open import Lib.Zero
open import Lib.One
open import Lib.Two

data Nat : Set where
  zero : Nat -- 0
  suc : Nat -> Nat -- 1+

_ : Nat
_ = suc (suc (suc zero))

-- examples for peanuts
-- builtin pragma with example

{-# BUILTIN NATURAL Nat #-}

_ : Nat
_ = 3 -- suc (suc (suc zero))

-- data Maybe a
--
-- Just 5
-- Just 'a'
-- Just True

data DrinkType : Set where
  beer milk : DrinkType

data Drink : DrinkType -> Set where
  верея : Drink milk
  duvel overflow : Drink beer

Alcohol : DrinkType -> Set
Alcohol beer = Nat
Alcohol milk = One

abv : {A : DrinkType} -> Drink A -> Alcohol A
abv верея = <> -- A ~ milk
abv duvel = 10
abv overflow = 6 -- A ~ beer

-- indexed types
-- DrinkType
-- Drink ix by DrinkType
-- Alcohol
-- alcoholByVolume
--
-- mention homework after indexed types

-- recursive peano addition
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)
-- suc
-- (1+ n) + m
-- 1+ (n + m)

-- mention fixity
infixr 100 _+N_

-- _*N_
-- infixr 110
-- 3 +N 5 *N 8
-- 3 +N (5 *N 8)
-- 100
-- right assoc
-- 3 +N 5 +N 8 +N 9
-- 3 +N (5 +N (8 +N 9))

-- isEven :: Integer -> Bool

-- TwoEq x y
-- IsEven n

isEven : Nat -> Two
isEven zero = tt
isEven (suc zero) = ff
isEven (suc (suc x)) = isEven x

data IsEven : Nat -> Set where
  e-zero : IsEven zero
  e-sucsuc :
    {n : Nat} ->
    IsEven n ->
    IsEven (suc (suc n))

-- IsEven' n
IsEven' : Nat -> Set
IsEven' zero = One
IsEven' (suc zero) = Zero
IsEven' (suc (suc x)) = IsEven' x

_ : IsEven' 16
_ = <>

_ : IsEven 16
_ = e-sucsuc (e-sucsuc (e-sucsuc (e-sucsuc (e-sucsuc (e-sucsuc (e-sucsuc (e-sucsuc e-zero)))))))

-- 2 + n - even
-- n - even

-- suc (suc n) ~ zero
-- zero /~ suc
-- (e-sucsuc n) : IsEven (suc (suc n))
-- ->
-- n : IsEven n
-- x : IsEven (suc (suc zero))
-- e-sucsuc x'
-- x' : IsEven zero
IsEven-desuc :
  {n : Nat} ->
  IsEven (suc (suc n)) ->
  IsEven n
IsEven-desuc (e-sucsuc p) = p

double : Nat -> Nat
double n = n +N n

double-IsEven : (n : Nat) -> IsEven (double n)
double-IsEven zero = e-zero
double-IsEven (suc n) =
  {! double-IsEven n !}

-- n +N (suc m) == suc (n +N m)
--
-- 1+ (n + (1+ n))
-- 1+ ((n + 1) + n)
-- 1+ ((1 + n) + n)
-- 1+ (1 + (n + n))
--
-- 1+ (1+ (n + n))
--
-- 2+ (n + n)

IsEven'-desuc :
  {n : Nat} ->
  IsEven' (suc (suc n)) ->
  IsEven' n
IsEven'-desuc x = x



-- Even and Odd as functions
-- Even and Odd as examples for an indexed data type
-- indexed vs function/calculated

-- NatEq

NatEq : Nat -> Nat -> Set
NatEq zero zero = One
NatEq zero (suc m) = Zero
NatEq (suc n) zero = Zero
NatEq (suc n) (suc m) = NatEq n m

data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

infix 10 _==_

_ : 3 +N 5 == 8
_ = refl 8

-- p : x == y
--
-- refl x : x == x
ap :
  {A B : Set} ->
  {x y : A} ->
  (f : A -> B) ->
  x == y ->
  f x == f y
ap {_} {_} {x} f (refl y) = refl (f x)

_$=_ :
  {A B : Set} ->
  {x y : A} ->
  (f : A -> B) ->
  x == y ->
  f x == f y
_$=_ = ap

infixr 20 _$=_
-- f $= g $= h $= p
-- f $= (g $= (h $= p))

-- trivial equality proof
-- +N
+N-left-zero : (n : Nat) -> zero +N n == n
+N-left-zero n = refl n

+N-right-zero : (n : Nat) -> n +N zero == n
+N-right-zero zero = refl zero
+N-right-zero (suc n) =
  suc $= +N-right-zero n


-- NatEq, TwoEq, motivation for generic Eq, requires indexed
-- _==_ with explicit arg


-- example for equality
-- A -> Zero as "not A"
-- example for "not equals"
-- the Not function

-- fixity, comparison with +N

-- the _/=_ helper

_/=_ : {A : Set} -> A -> A -> Set
x /= y = Not (x == y)

infix 10 _/=_

-- matching on == proofs to reveal information (trigger unification)
==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm (refl x) = refl x

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
  y == x ->
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
--   In the original RPS game, rock loses to paper, and paper loses to scissors, "hence" scissors should lose to paper.
data GLosesTo {A : Set} (R : A -> A -> Set) : A -> A -> Set where

-- TASK
-- Write some unit tests for your new yummy GLosesTo
-- You'll probably need a new enum data type with more values in it to do so.
--
-- Are there any properties that hold for GLosesTo, based on the properties of R?
-}

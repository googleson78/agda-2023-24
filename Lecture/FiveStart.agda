{-# OPTIONS --no-unicode #-}

module Lecture.FiveStart where

open import Lib.Nat
open import Lib.Zero
open import Lib.Eq
open import Lib.Sigma
open import Lib.Dec
open import Lib.List

-- TODO FOR NEXT YEAR: give intuit for >< being a sum
-- by showing how you can express _+_ with >< (and indeed any sum type)

-- mention lib changes
-- Lib.Nat
-- Lib.List
-- Lib.Sigma
-- Lib.Dec

-- show sigma
-- sigma as "exists"
-- sigma for unknown input
-- show Dec
-- show with
--   diff
--     full syntax
--     dots
--     we can still rewrite
--   decNat==
--     matching on the with value gives us more info
--   rewrite with with, +N-assoc, abstracting types over values
--     goal+original args types' are abstracted over the with value
-- show Fin
-- show Vec

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 20 _,-_

{-
data Even : Nat -> Set where
  e-zero : Even 0
  e-sucsuc : {n : Nat} -> Even n -> Even (suc (suc n))

-- TASK
-- Use _><_ to specify, and then implement division by two,
-- which guarantees that the result is twice as small as the input.
--
-- Note that we don't need an explicit n since Even already has enough
-- info to let Agda figure out what n should be
div2 : {n : Nat} -> Even n -> {! !}
div2 = {! !}

-- TASK
-- Express List by using Vec and _><_
ListAsVec : Set -> Set
ListAsVec A = {! !}

-- TASK
-- Convert from ListAsVec to List
ListAsVec-to-List : {A : Set} -> ListAsVec A -> List A
ListAsVec-to-List = {! !}

-- TASK
-- Convert from List to ListAsVec
List-to-ListAsVec : {A : Set} -> List A -> ListAsVec A
List-to-ListAsVec = {! !}

-- TASK
-- Formulate and prove that the ListAsVec conversions do not change their respective inputs

-- TASK
-- Formulate and implement "precise", List -> Vec conversion
-- in the sense that you can exactly specify what the length of the resulting vector will be
listToVec : {! !}
listToVec = {! !}

-- TASK
-- Specify and implement vector appending
_+V_ : ?
_+V_ = ?
infixr 25 _+V_

-- TASK
-- Specify and implement the map function for vectors
vMap : ?
vMap = {! !}

-- TASK
-- Specify and implement the cartesian product of two vectors
_*V_ : ?
_*V_ = {! !}

-- TASK
-- Use an input value of type n <= m to guide you on how to take a prefix of size n from an input Vector of size m.
vTake : ?
vTake = ?

-- TASK
-- Look at <=-refl.
-- Think about what property you can prove involving vTake and <=-refl.

-- TASK
-- Look at <=-trans
-- Formulate and prove the following property:
--
-- If you know n <= m and m <= k, and you have Vec A k,
-- then both of these operations should have the same result:
-- * doing two vTakes - one with n <= m, and another with m <= k,
-- * doing a single vTake - with the "composition" of n <= m and m <= k

-- TASK
-- Convert a Fin to a Nat
-- Essentially this "forgets" the upper bound for the input Fin
finToNat : {n : Nat} -> Fin n -> Nat
finToNat = {!!}

-- TASK
-- express < by using _<=_ without using _==_
_<_ : Nat -> Nat -> Set
n < m = {!!}

infix 90 _<_

-- TASK
<-suc : (n : Nat) -> n < suc n
<-suc = {!!}

-- TASK
-- Convert a Nat to a Fin
natToFin : ?
natToFin = ?

-- TASK
-- A generalised version of natToFin, which uses < to specify what the upper
-- bound for the resulting Fin is
natToFin< : {m : Nat} (n : Nat) -> n < m -> Fin m
natToFin< = ?

-- TASK
finToNat-natToFin-id : (n : Nat) -> n == finToNat (natToFin n)
finToNat-natToFin-id = {!!}

-- TASK
-- Write down the calculated version of <, i.e. instead of defining a data type
-- implement the function Lt which takes two Nats and returns what proof is required
-- to prove they are equal.
-- You can look at TwoEq in Lecture/TwoStart.agda for inspiration.
Lt : Nat -> Nat -> Set
Lt = {!!}

-- TASK
-- Prove that the calculated version of _<_ implies the regular on
Lt-< : (n m : Nat) -> Lt n m -> n < m
Lt-< = {!!}

-- TASK
-- "Weaken" the upper bound for a Fin.
-- "Weaken", because we allow *more* values in the new Fin,
-- meaning we have *less* information about what the result actually is.
weakenFin : {m n : Nat} -> Fin n -> n <= m -> Fin m
weakenFin = {!!}

-- TASK
-- Specialised version of weakenFin, might be useful some other day
-- look at <=-suc in Lib.Nat
weakenFinSuc : {n : Nat} -> Fin n -> Fin (suc n)
weakenFinSuc = {!!}

-- TASK
-- Prove that _<_ implies _<=_
<-<= : {n m : Nat} -> n < m -> n <= m
<-<= = {!!}

-- TASK
finToNat-< : {n : Nat} -> (x : Fin n) -> finToNat x < n
finToNat-< = {!!}

-- TASK
fromNat-toNat-id : {m n : Nat} (x : Fin n) (p : n <= m) -> x == natToFin (finToNat x) (finToNat-< x)
fromNat-toNat-id = {!!}

-- TASK
-- Implement an equality check for Fins
decEqFin : {n : Nat} -> (x y : Fin n) -> Dec (x == y)
decEqFin = {!!}
-}

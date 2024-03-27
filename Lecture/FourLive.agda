{-# OPTIONS --no-unicode #-}

module Lecture.FourLive where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Nat

module _ where
  open import Lib.EqExplicitRefl

  +N-right-zero-1 : (n : Nat) -> n +N zero == n
  +N-right-zero-1 zero = refl zero
  +N-right-zero-1 (suc n) =
    suc $= +N-right-zero-1 n

  +N-right-suc-1 : (n m : Nat) -> suc (n +N m) == n +N suc m
  +N-right-suc-1 zero m = refl (suc m)
  +N-right-suc-1 (suc n) m = suc $= +N-right-suc-1 n m

  +N-commut-1 : (n m : Nat) -> n +N m == m +N n
  +N-commut-1 zero m = ==-symm (+N-right-zero-1 m)
  +N-commut-1 (suc n) m = ==-trans (suc $= (+N-commut-1 n m)) (+N-right-suc-1 m n)

module _ where

  open import Lib.EqImplicitRefl

  +N-right-zero-2 : (n : Nat) -> n +N zero == n
  +N-right-zero-2 zero = refl
  +N-right-zero-2 (suc n) =
    suc $= +N-right-zero-2 n

  +N-right-suc-2 : (n m : Nat) -> suc (n +N m) == n +N suc m
  +N-right-suc-2 zero m = refl
  +N-right-suc-2 (suc n) m = suc $= +N-right-suc-2 n m

  +N-commut-2 : (n m : Nat) -> n +N m == m +N n
  +N-commut-2 zero m = ==-symm (+N-right-zero-2 m)
  +N-commut-2 (suc n) m = ==-trans (suc $= (+N-commut-2 n m)) (+N-right-suc-2 m n)

module _ where
  open import Lib.Eq

  +N-right-zero-3 : (n : Nat) -> n +N zero == n
  +N-right-zero-3 zero = refl
  +N-right-zero-3 (suc n) =
    suc $= +N-right-zero-3 n

  +N-right-suc-3 : (n m : Nat) -> suc (n +N m) == n +N suc m
  +N-right-suc-3 zero m = refl
  +N-right-suc-3 (suc n) m = suc $= +N-right-suc-3 n m

  +N-commut-3 : (n m : Nat) -> n +N m == m +N n
  +N-commut-3 zero m = ==-symm (+N-right-zero-3 m)
  +N-commut-3 (suc n) m = ==-trans (suc $= (+N-commut-3 n m)) (+N-right-suc-3 m n)

  +N-right-zero-4 : (n : Nat) -> n +N zero == n
  +N-right-zero-4 zero = refl
  +N-right-zero-4 (suc n)
    rewrite +N-right-zero-4 n = refl
  
  +N-right-suc-4 : (n m : Nat) -> suc (n +N m) == n +N suc m
  +N-right-suc-4 zero m = refl
  +N-right-suc-4 (suc n) m
    rewrite +N-right-suc-4 n m = refl

  +N-commut-4 : (n m : Nat) -> n +N m == m +N n
  +N-commut-4 zero m
    rewrite +N-right-zero-4 m = refl
  +N-commut-4 (suc n) m
    rewrite +N-commut-4 n m
    rewrite +N-right-suc-4 m n = refl

  +N-commut-5 : (n m : Nat) -> n +N m == m +N n
  +N-commut-5 zero m
    rewrite +N-right-zero-4 m = refl
  +N-commut-5 (suc n) m
    rewrite +N-right-suc-4 n m
    rewrite +N-commut-5 n (suc m)
    rewrite +N-right-suc-4 m n = refl

  _//==_ :
    {A : Set} {x y z : A} ->
    x == y ->
    y == z ->
    x == z
  _//==_ = ==-trans
  infixr 10 _//==_

  +N-commut-6 : (n m : Nat) -> n +N m == m +N n
  +N-commut-6 zero m
    rewrite +N-right-zero-4 m = refl
  +N-commut-6 (suc n) m =
    (suc $= (+N-commut-6 n m)) //== +N-right-suc-4 m n

  +N-commut-7 : (n m : Nat) -> n +N m == m +N n
  +N-commut-7 zero m =
    m =[ ==-symm (+N-right-zero m) ]
    m +N zero
    QED
  +N-commut-7 (suc n) m =
    suc n +N m 
    =[]
    suc (n +N m)
    =[ suc $= (+N-commut-7 n m) ]
    suc (m +N n)
    =[ +N-right-suc m n ]
    m +N suc n
    QED

{-
-- TASK
-- Implement a linear and constant space tail recursive version of Nat addition
addNat : Nat -> Nat -> Nat
addNat = ?

-- TASK
-- Prove that your addNat behaves like +N.
-- Think about what lemma you'll need to formulate for the recursive case.
addNat-==-+N : (n m : Nat) -> addNat n m == n +N m
addNat-==-+N = ?

-- Traditionally defined recursive lists, parametrised by the type of elements in them.
data List (a : Set) : Set where
  -- the empty list is a list
  [] : List a
  -- we can add a new element to the "head" of a list
  _,-_ : a -> List a -> List a

infixr 21 _,-_

-- concatenate two lists
_+L_ : {A : Set} -> List A -> List A -> List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

infixr 22 _+L_

-- TASK
-- Prove that +L is associative
+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L (ys +L zs)
+L-assoc = ?

-- TASK
-- Formulate and prove that [] is a right identity for +L
+L-right-id : ?
+L-right-id = ?

-- TASK
-- Implement a function which returns the length of a list as a natural number
length : {A : Set} -> List A -> Nat
length = ?

-- TASK
-- Formulate and prove that length is functorial/homomorphic over +L, i.e.
-- the length of the result of +L is the sum of the lengths of its inputs.
+L-length : ?
+L-length = ?

-- TASK
-- Reverse a list by appending to the end of it
reverse : {A : Set} -> List A -> List A
reverse = ?

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll (most likely) need a lemma which comes as a generalisation of an equality in the recursive case
reverse-reverse-id : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-reverse-id = ?

-- TASK
-- Implement multiplication using +N
_*N_  : Nat -> Nat -> Nat
_*N_ = ?
infixr 120 _*N_

-- verify that *N behaves normally with a unit test
_ : 5 *N 4 == 20
_ = refl

-- TASK
-- Prove that *N is commutative.
-- Look at your cases and think about what lemmas you needed in +N-commut, and try to mirror them here.
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut = ?

-- TASK
-- Reverse a list in linear time and constant space by using a helper function
-- The special form of where used below allows us to refer to the definitions inside the
-- where by using a qualified syntax, i.e. we can refer to the inner go with reverseLinear.go
-- Also note that the where bound definition lets us refer to any names bound in the
-- parent function definition, so if we want to refer to A in its signature, we need
-- to explicitly bind the A type argument.
reverseLinear : {A : Set} -> List A -> List A
reverseLinear {A} = ?
  module reverseLinear where
  go : List A -> List A -> List A
  go = ?

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll need to formulate a helper lemma for reverseLinear.go
-- Think about what the invariant that reverseLinear.go is trying to maintain is, and how we can extract
-- the correctness property of reverse from it.
reverseLinear-reverseLinear-id : {A : Set} (xs : List A) -> reverseLinear (reverseLinear xs) == xs
reverseLinear-reverseLinear-id {A} xs = ?
  where
    goLem : ?
    goLem = ?

-- TASK
-- Prove that *N distributes over +N on the left
*N-left-distrib-+N : (n m k : Nat) -> n *N (m +N k) == n *N m +N n *N k
*N-left-distrib-+N = ?

-- TASK
-- Prove that *N distributes over +N on the right, by using *N-left-distrib-+N and *N-commut
*N-right-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-right-distrib-+N n m k = ?

-- TASK
-- Prove *N associative
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc = ?

-- TASK
-- +L and +N are very similar - indeed, if we ignore the elements of the list,
-- they're practically the same function. +L-length which you proved earlier expressed
-- one of the directions of this correspondence.
-- Can you think of some property (with possibly extra definitions) to express the other direction -
-- from +N to +L - of this correspondence?

-- TASK
-- If +N and +L "correspond" with each other, then what would *N correspond with?
-- Implement a function, let's call it _*L_, which you think is *N generalised to lists, and then prove
-- some "functorial"/"homomorphism" properties linking *N and your new *L.

record _*_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _*_ public
infixr 90 _*_

-- TASK
-- Implement list zipping, i.e. combining list elements pointwise, with the longer lists extra elements
-- getting chopped off and dropped.
-- e.g. in Haskell zip [1,2,3,6] [3,4,5] == [(1,3), (2, 4), (3, 5)]
zip : {A B : Set} -> List A -> List B -> List (A * B)
zip = {! !}

-- TASK
-- Does this zip function have some analogue for Nats?
-- Can you prove any properties linking the two?
-- Are there some obvious properties for "the Nat version of zip" which you can transfer back to zip?
-}
  
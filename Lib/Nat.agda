{-# OPTIONS --no-unicode #-}

module Lib.Nat where

open import Lib.Zero
open import Lib.One
open import Lib.Eq

data Nat : Set where
  zero : Nat -- 0
  suc : Nat -> Nat -- 1+

{-# BUILTIN NATURAL Nat #-}

infixr 100 _+N_
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

+N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+N-assoc zero m k = refl
+N-assoc (suc n) m k = suc $= +N-assoc n m k

+N-right-zero : (n : Nat) -> n +N zero == n
+N-right-zero zero = refl
+N-right-zero (suc n) =
  suc $= +N-right-zero n

+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
+N-right-suc zero m = refl
+N-right-suc (suc x) m = suc $= +N-right-suc x m

+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut zero m = ==-symm (+N-right-zero m)
+N-commut (suc n) m
  rewrite +N-commut n m
  rewrite +N-right-suc m n =
  refl

data _<=_ : Nat -> Nat -> Set where
  -- We know that zero is ≤ anything else
  ozero : {x : Nat} -> zero <= x
  -- We know that if x <= y, then suc x <= suc y also
  osuc : {x y : Nat} -> x <= y -> suc x <= suc y

infix 90 _<=_

<=-refl : (n : Nat) -> n <= n
<=-refl zero = ozero
<=-refl (suc x) = osuc (<=-refl x)

<=-suc : (n : Nat) -> n <= suc n
<=-suc zero = ozero
<=-suc (suc x) = osuc (<=-suc x)

<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans ozero q = ozero
<=-trans (osuc p) (osuc q) = osuc (<=-trans p q)

<=-antisymm : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisymm ozero ozero = refl
<=-antisymm (osuc p) (osuc q) = suc $= <=-antisymm p q

<=-refl-not-suc : {n : Nat} -> Not (suc n <= n)
<=-refl-not-suc (osuc sucn<=m) = <=-refl-not-suc sucn<=m

<=-suc-not-eq : {n m : Nat} -> suc n <= m -> Not (n == m)
<=-suc-not-eq p refl = <=-refl-not-suc p

NatEq : Nat -> Nat -> Set
NatEq zero zero = One
NatEq zero (suc m) = Zero
NatEq (suc n) zero = Zero
NatEq (suc n) (suc m) = NatEq n m

_*N_  : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 120 _*N_

*N-right-zero : (n : Nat) -> n *N 0 == 0
*N-right-zero zero = refl
*N-right-zero (suc n) = *N-right-zero n

*N-right-suc : (n m : Nat) -> n *N suc m == n +N n *N m
*N-right-suc zero m = refl
*N-right-suc (suc n) m rewrite *N-right-suc n m = suc $=
  m +N n +N n *N m =[ ==-symm (+N-assoc m n (n *N m)) ]
  (m +N n) +N n *N m =[ _+N n *N m $= +N-commut m n ]
  (n +N m) +N n *N m =[ +N-assoc n m (n *N m) ]
  n +N m +N n *N m QED

*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut zero m rewrite *N-right-zero m = refl
*N-commut (suc n) m =
  m +N n *N m =[ m +N_ $= *N-commut n m ]
  m +N m *N n =[ ==-symm (*N-right-suc m n) ]
  m *N suc n QED

*N-left-distrib-+N : (n m k : Nat) -> n *N (m +N k) == n *N m +N n *N k
*N-left-distrib-+N zero m k = refl
*N-left-distrib-+N (suc n) m k =
  (m +N k) +N n *N (m +N k)
    =[ ap ((m +N k) +N_) (*N-left-distrib-+N n m k) ]
  (m +N k) +N (n *N m +N n *N k)
    =[ +N-assoc m k (n *N m +N n *N k) ]
  m +N (k +N ((n *N m) +N (n *N k)))
    =[ ap (m +N_) (==-symm (+N-assoc k (n *N m) (n *N k))) ]
  m +N ((k +N (n *N m)) +N (n *N k))
    =[ ap (m +N_) (ap (_+N n *N k) (+N-commut k (n *N m))) ]
  m +N (((n *N m) +N k) +N (n *N k))
    =[ ap (m +N_) (+N-assoc (n *N m) k (n *N k)) ]
  m +N ((n *N m) +N (k +N (n *N k)))
    =[ ==-symm (+N-assoc m (n *N m) (k +N n *N k)) ]
  (m +N n *N m) +N (k +N n *N k)
    QED

*N-right-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-right-distrib-+N n m k
  rewrite *N-commut (n +N m) k
  rewrite *N-left-distrib-+N k n m
  rewrite *N-commut k n
  rewrite *N-commut k m = refl

*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc zero m k = refl
*N-assoc (suc n) m k =
  (suc n *N m) *N k =[]
  (m +N n *N m) *N k =[ *N-right-distrib-+N m (n *N m) k ]
  m *N k +N (n *N m) *N k =[ (m *N k +N_)  $= *N-assoc n m k ]
  suc n *N m *N k QED

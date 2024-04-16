{-# OPTIONS --no-unicode #-}

module Lib.Vec where

open import Lib.Nat

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 20 _,-_

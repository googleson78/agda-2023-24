{-# OPTIONS --no-unicode #-}

module Lib.SnocList where

open import Lib.Nat

data SnocList (A : Set) : Set where
  [] : SnocList A
  _-,_ : SnocList A -> A -> SnocList A

infixl 20 _-,_

length : {A : Set} -> SnocList A -> Nat
length [] = 0
length (xs -, x) = suc (length xs)

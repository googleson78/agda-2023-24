{-# OPTIONS --no-unicode #-}

module Lib.Dec where

open import Lib.Zero

data Dec (A : Set) : Set where
  no : Not A -> Dec A
  yes : A -> Dec A

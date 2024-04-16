{-# OPTIONS --no-unicode #-}

module Lib.Fun where

flip : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
flip f y x = f x y

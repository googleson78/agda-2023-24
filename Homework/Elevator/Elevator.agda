{-# OPTIONS --no-unicode #-}
module Homework.Elevator.Elevator where

open import Lib.Zero
open import Lib.Two
open import Lib.One
open import Lib.Sum

data State : Set where

eqState : State -> State -> Two
eqState = ?

data Action : State -> Set where

transition : (s : State) -> Action s -> State
transition = ?

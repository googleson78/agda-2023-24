{-# OPTIONS --no-unicode #-}

module Lib.EqExplicitRefl where

open import Lib.Zero

data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

infix 10 _==_

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

==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm (refl x) = refl x

==-trans :
  {A : Set} {x y z : A} ->
  x == y ->
  y == z ->
  x == z
==-trans (refl _) x = x

_/=_ : {A : Set} -> A -> A -> Set
x /= y = Not (x == y)

infix 10 _/=_

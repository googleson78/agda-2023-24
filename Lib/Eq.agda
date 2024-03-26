{-# OPTIONS --no-unicode #-}

module Lib.Eq where

open import Lib.Zero

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

infix 10 _==_

ap :
  {A B : Set} ->
  {x y : A} ->
  (f : A -> B) ->
  x == y ->
  f x == f y
ap _ refl = refl

_$=_ :
  {A B : Set} ->
  {x y : A} ->
  (f : A -> B) ->
  x == y ->
  f x == f y
_$=_ = ap

infixr 5 _$=_

==-symm : {A : Set} {x y : A} -> x == y -> y == x
==-symm refl = refl

==-trans :
  {A : Set} {x y z : A} ->
  x == y ->
  y == z ->
  x == z
==-trans refl x = x

_/=_ : {A : Set} -> A -> A -> Set
x /= y = Not (x == y)

infix 10 _/=_

_=[]_ :
  {A : Set} {z : A}
  (x : A) ->
  x == z ->
  x == z
_ =[] q = q

infixr 10 _=[]_

_=[_]_ :
  {A : Set} {y z : A}
  (x : A) ->
  x == y ->
  y == z ->
  x == z
_ =[ p ] q = ==-trans p q

infixr 10 _=[_]_

_QED : {A : Set} (x : A) -> x == x
_ QED = refl

infix 11 _QED

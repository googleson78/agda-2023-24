{-# OPTIONS --no-unicode #-}
module Lecture.EightLive where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One
open import Lib.List
open import Lib.Sigma

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

-- weakenFinSuc : {n : Nat} -> Fin n -> Fin (suc n)
-- weakenFinSuc (3 :: горна граница 4) == (3 :: горна граница 5)

-- LECTURE:
-- https://learn.fmi.uni-sofia.bg/mod/url/view.php?id=312944

-- Fin 3
-- 0 1 2
-- zero
-- suc zero
-- suc (suc zero)
-- "тип с три обитателя"
-- Λₙ := "има по-малко от (1 + n) свободни променливи"
-- Fin n
--
-- Fin n
-- "тип с n обитателя"

{-
-- tl;dr we need some Fin and < machinery later down the line for lambda terms.
--
-- The tasks below concerning Fins and comparisons are necessary,
-- because when we're expressing nameless lambda terms, we'll want to be able to say
-- "at most n free variables", which is exactly the same as "the number of free variables being less than n".
-- At the same time, a term of Fin n is exactly the same as a number which is less than n,
-- which we'll use for constructing variables.

-- TASK
-- "Forget" the type information of the upper bound of a Fin, only leaving the number itself.
toNat : {n : Nat} -> Fin n -> Nat
toNat = {!!}

-- TASK
-- Express < using <=, without using _==_
_<_ : Nat -> Nat -> Set
n < m = {!!}

-- TASK
toNat-< : {n : Nat} -> (x : Fin n) -> toNat x < n
toNat-< = {!!}

-- TASk
_ : 3 < 5
_ = {!!}

-- TASK
3NotLessThan2 : 3 < 2 -> Zero
3NotLessThan2 = {!!}

-- TASK
<-suc : (n : Nat) -> n < suc n
<-suc = {!!}

-- TASK
-- Convert from a Nat to a Fin with an appropriate upper bound.
--
-- Note that (n : Nat) -> Fin n wouldn't work as a type, because, e.g.
-- we can't convert 0 to a Fin 0, because Fin 0 has no inhabitants.
--
-- We allow for an arbitrary m, instead of just Fin (suc n), because it's more convenient
-- (e.g. for fromNat-toNat-id)
fromNat : {m : Nat} -> (n : Nat) -> n < m -> Fin m
fromNat = {!!}

-- TASK
-- Prove that your conversions don't change the original Nat
toNat-fromNat-id : (n : Nat) -> n == toNat (fromNat n (<-suc n))
toNat-fromNat-id = {!!}

-- TASK
-- write down the calculated version of <
--
-- This is useful because later down the line we'll want to write Fins with as little boilerplate as possible.
-- If we combine Lt with fromNat, we'll get a function where Agda can figure out the proof itself - see the fin function.
-- Lt : Nat -> Nat -> Set
-- Lt = {!!}

-- TASK
-- Prove that the calculated version implies the regular one,
-- so that we may provide the regular proof to fromNat later.
Lt-< : (n m : Nat) -> Lt n m -> n < m
Lt-< = {!!}

-- TASK
-- This is the "smart constructor" for Fins, which allows us to much more easily write "Fin literals" in our program.
--
-- The idea here is that if n and m are both known, since Lt is a function, Agda can calculate the Lt down to a One
-- or a Zero, and it can figure out how to fill in the One automatically, meaning that we can leave the Lt argument to be implicit
-- You'll need to expose *all* the implicit arguments here.
-- See the examples below.
fin : {m : Nat} -> (n : Nat) -> {Lt n m} -> Fin m
fin = {!!}

_ : Fin 3
_ = fin 2
-- vs
_ : Fin 3
_ = fromNat 2 (osuc (osuc (osuc ozero)))
-- vs
_ : Fin 3
_ = suc (suc (zero))

-- doesn't work, as expected, because 2 is not a Fin 2
-- _ : Fin 2
-- _ = fin 2

_ : Fin 5
_ = fin 2

_ : Fin 5
_ = fin 3

-- TASK
-- Increase the upper bound on a Fin.
-- This function is called "weaken", because we allow *more* values in the new Fin,
-- meaning we have *less* information about what the result actually is.
weakenFin : {m n : Nat} -> Fin n -> n <= m -> Fin m
weakenFin = {!!}

-- TASK
-- A specialised version of weakenFin, it is sometimes more convenient than the more general one.
weakenFinSuc : {n : Nat} -> Fin n -> Fin (suc n)
weakenFinSuc = {!!}

-- TASK
<-<= : {n m : Nat} -> n < m -> n <= m
<-<= = {!!}

-- TASK
fromNat-toNat-id : {m n : Nat} (x : Fin n) (p : n <= m) -> x == fromNat (toNat x) (toNat-< x)
fromNat-toNat-id = {!!}

-- TASK
-- Implement an equality check for two Fins with the same upper bound
decEqFin : {n : Nat} -> (x y : Fin n) -> Dec (x == y)
decEqFin = {!!}

-- TASK
-- Implement the data type of nameless DeBruijn lambda terms,
-- parametrised by the number of variables in a particular term.
--
-- Some of the rest of the tasks rely on the names of these constructors, so don't change them.
data Lam (n : Nat) : Set where
  var : ?
  app : ?
  lam : ?

-- TASK
-- Construct a variable from a Nat directly.
-- You'll need to expose the implicit Lt argument.
--
-- This is a convenient prefix synonym for constructing nameless variables, allowing us to write
-- ` 4
-- instead of
-- var (fin 2)
-- or
-- var (suc (suc zero))
--
-- This, of course, only works when the m argument can be inferred.
` : {m : Nat} -> (n : Nat) -> {Lt n m} -> Lam m
` n {x} = ?

-- TASK
-- Define the id function using nameless terms
lamId : Lam 0
lamId = {!!}

-- TASK
-- Define the const function using nameless terms
-- taking two arguments, and always returning the first one.
lamK : Lam 0
lamK = {!!}

-- TASK
-- Implement the following function
s : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
s = {!!}

-- TASK
-- Translate the s function from above into Lam
lamS : Lam 0
lamS = {!!}

-- TASK
-- Write the following lambda term as a nameless lambda term
-- λx. λy. x (u z)
-- \x -> \y -> x (u z)
_ : Lam ?
_ = ?

-- NOTE
-- This withFree function is a syntactic "trick".
-- Oftentimes when we write a Lam term, we won't have the opportunity
-- to specify how many free variables it will have explicitly.
--
-- The result of this is that some of the constructors of lam, which have implicit arguments
-- based on the number of free variables, will not be able to infer these implicit arguments,
-- and we'll get some ambiguity errors.
--
-- As an example
-- lam (var zero)
-- could have as many free variables as we like - since the var zero is referring to the only
-- bound argument, this whole lambda term could have an arbitrary amount of free variables - even zero.
--
-- In order to resolve this, we'll be using withFree to be able to explicitly specify
-- the number of free variables on a function, by associating the first argument of withFree
-- as being the number of free varaibles in the second argument
--
-- Going back to the example from above
-- lam (var zero)
-- if we want to indicate taht this term will have 3 free variables, we would write
-- withFree 3 (lam (var zero))
-- Of course, we could also just explicitly specify one of the implicit arguments, i.e.
-- lam {3} (var zero)
-- but using withFree seems like a more consistent and clean approach.
withFree : (n : Nat) -> Lam n -> Lam n
withFree _ x = x

_ :
  withFree 3 (lam (var zero))
  ==
  lam (var zero)
_ = refl
-- vs
_ :
  lam {3} (var zero)
  ==
  lam (var zero)
_ = refl

_ :
  lam {3} (var zero)
  ==
  withFree 3 (lam (var zero))
_ = refl

-- An example of where Agda would get confused if we did not give it more type information
-- Uncomment this temporarily, to witness Agda's confusion:
-- _ :
--   lam (var zero)
--   ==
--   lam (var zero)
-- _ = refl

-- TASK
dec<= : (n m : Nat) -> Dec (n <= m)
dec<= = {!!}

-- TASK
dec< : (n m : Nat) -> Dec (n < m)
dec< = {!!}

-- TASK
-- We'll want to eventually shift all the free variables in a lambda term by one.
-- However, in order to implement this, we'll need a helper function, which
-- has an additional argument to keep track of how many lambdas we've "gone into" during
-- our recursion.
--
-- Otherwise, we would have no way of knowing which variables are free and which are
-- actually bound by some outer lambda.
shiftUp1 : {n : Nat} -> Nat -> Lam n -> Lam (suc n)
shiftUp1 c t = {!!}

-- TASK
-- Once we have shiftUp1, we can easily implement "shift all the free variables by one"
-- by using shiftUp1.
shiftUp10 : {n : Nat} -> Lam n -> Lam (suc n)
shiftUp10 = ?

-- TASK
-- what does shifting
-- λ 0
-- result in?
_ :
  withFree 1 (shiftUp10 (lam (` 0)))
  ==
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ 1
-- result in?
_ :
  shiftUp10 (withFree 2 (lam (lam (` 1))))
  ==
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ 3
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (` 3))))
  ==
  {!!}
_ = refl

-- TASK
-- what does shifting
-- λ λ (0 (0 2)
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (app (` 1) (app (` 0) (` 2))))))
  ==
  {!!}
_ = refl

-- TASK
-- Implement substitution, i.e.
-- t [ x => p ]
-- should be the result of replacing all x's in t with a p.
_[_=>_] : {n : Nat} -> Lam n -> Fin n -> Lam n -> Lam n
_[_=>_] = {!!}

-- TASK
-- What does substituting 2 for 3 in 1 result in?
--
-- note that we have to give our lambda term enough free vars
-- for the substitution to be applicable, even if we're not using them!
_ :
  withFree 4 ((` 1) [ fin 2 => ` 3 ])
  ==
  {!!}
_ = refl

-- TASK
-- What does substituting 2 for 3 in 2 result in?
_ :
  withFree 4 ((` 2) [ fin 2 => ` 3 ])
  ==
  {!!}
_ = refl

-- TASK
-- What does substituting 2 for 3 in λ0 result in?
_ :
  withFree 4 (lam (` 0) [ fin 2 => ` 3 ])
  ==
  {!!}
_ = refl

-- TASK
-- what does substituting 3 for 5 in λ3 result in?
_ :
  withFree 6 (lam (` 3)) [ fin 2 => ` 5 ]
  ==
  {!!}
_ = refl

-- TASK
-- what does substituting 0 for 01 in λ0 result in?
_ :
  withFree 4 (lam (` 0)) [ fin 0 => app (` 0) (` 1) ]
  ==
  {!!}
_ = refl

-- TASK
-- what does substituting 0 for λ01 in 0(λ01) result in?
_ :
  withFree 2 (app (` 0) (lam (app (` 0) (` 1)))) [ fin 0 => lam (app (` 0) (` 1)) ]
  ==
  {!!}
_ = refl

-- TASK
-- Define named lambda terms.
-- We could use strings here, for variable names, but instead we'll use Nats, in the sense that
-- 1 will "stand for" x1, 8 for x8, etc.
--
-- The only reason for doing this is so that we can avoid having to introduce strings.
data NamedLam : Set where
  var : Nat -> NamedLam
  app : NamedLam -> NamedLam -> NamedLam
  lam_>_ : Nat -> NamedLam -> NamedLam

-- TASK
-- Convert a nameless lambda term to a named one, using a context of
-- an appropriate type
name : ? -> Lam ? -> NamedLam
name ctxt t = {!!}
-}

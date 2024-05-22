{-# OPTIONS --no-unicode #-}
module Lecture.TenStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One
open import Lib.Dec
open import Lib.SnocList
open import Lecture.NineLive

-- TODO:
-- We have some unit tests for subst in this file

-- TODO
-- buggy _[_], delete it

-- TODO definitions
-- "closed term" - a term with no free variables
-- "beta reduction" - evaluating an expression
-- "beta redex" - a term we can reduce using beta reduction
-- "value", - functions, since we're in a pure lambda calculus. If we added e.g. chars/strings/nats to our language, those would be values as well

{-
-- TASK
-- A substitution that "performs one computation"
--
-- The idea here is that we'll encounter a situation like this one:
-- (λ N) M
-- translated to our syntax:
-- app (lam N) M
--
-- We have an application of a lambda function to another term, which
-- is the point at which we want to do a substitution, replacing all
-- variables occurences of the variable bound by the lambda with M.
--
-- We already have the function to do substitution (subst), so we only need
-- to build the appropriate Subst(itution) now.
--
-- Thankfully this is easy to do:
-- "Coincidentally", the lambda has just introduced a variable for us to use
-- with the M we have, and the types line up, because of how we made the lam and app constructors.
--
-- Note that we also need to shift down all our other free variables, which we're not currently substituting,
-- as we just got rid of a single lambda.
reduceSubst :
  {gamma : Context} {tau : Type} ->
  Lam gamma tau ->
  Subst (gamma -, tau) gamma
reduceSubst = ?

-- NOTE
-- A convenient synonym for substituting by reduceSubst
-- You can also make a non-operator version if you prefer to not have "operator soup"
_[0=>_] :
  {gamma : Context} {tau pi : Type} ->
  Lam (gamma -, pi) tau ->
  Lam gamma pi ->
  Lam gamma tau
x [0=> t ] = subst (reduceSubst t) x


infix 15 _[0=>_]

-- NOTE
-- Some unit tests for your substitution and reduceSubst

_ :
  withContext [ base 69 , base 42 ]
    (` 0 [0=> ` 1 ])
  ==
  (` 1)
_ = refl

_ :
  withContext [ base 1337 , base 42 ]
    (
      (lam {_} {base 69} (` 0))
        [0=>
          ` 1
        ]
    )
  ==
  lam (` 0)
_ = refl

foo0 : Lam [ base 0 => base 0 ] (base 0 => base 0)
foo0 = lam (app (` 1) (app (` 1) (` 0)))

foo1 : Lam [] (base 0 => base 0)
foo1 = lam (` 0)

foo2 : Lam [] (base 0 => base 0)
foo2 = lam (app (lam (` 0)) (app (lam (` 0)) (` 0)))

_ : foo0 [0=> foo1 ] == foo2
_ = refl

-- TASK
-- We want Val to be a predicate stating that a certain term is a Value.
--
-- We're working in a "pure" lambda calculus, meaning we only have variables, application, and lambdas.
--
-- In such a lambda calculus, the only fully closed terms are lambdas, so we need to have a single constructor here,
-- to expressing the fact that lam N is a value.
data Val : {ctx : Context} {ty : Type} -> Lam ctx ty -> Set where
  v-lam : ? -> Val ?

-- TASK
-- N ==> M is going to express the relation that N beta reduces to M.
-- You're going to define this relation by following the description I've given below for what we want to achieve.
--
-- We're going to have three rules/constructors here:
-- 1. red-beta
--
-- First, we clearly need to have a rule (the beta rule) that states "If you have (λN) M, you can reduce that to N [0=> M ]", as that's how our substitution works.
-- Furthermore, we'll restrict ourselves to only applying this rule when M is a value, to force us to first reduce our arguments before calling a function (strict/call by value semantics)
-- Taking all that into account, we need to add a constructor that states
-- If M is a value, then app (lam N) M reduces to N [0=> M ]
--
-- Apart from that, we'll also need two other rules, to allow reduction to "see past" applications.
--
-- 2. red-app-l
-- Imagine you have the following scenario
--
-- ((λ0) (λ0)) (λ0)
--
-- i.e.
-- app
--  (app
--    (lam (` 0))
--    (lam (` 0))
--  )
--  (lam (` 0))
-- Notice that in the left argument of the outermost app, there's a beta redex waiting to be evaluated, that being (λ0) (λ0)
--
-- However, if we only allow reducing terms of the form ((λN) M), we can't actually do that reduction, because
-- there's nothing us do an "inner" reduction first, i.e. one that is hidden behind an app.
--
-- In order to allow reduction to proceed in such a case, we need to add a constructor which states that
-- If we can reduce N to N', then we can also reduce app N M to app N' M
--
-- By using this constructor, we can now first do a reduction on the left of our application
--
-- 3. red-app-r
-- Mirroring 2. we can also imagine having the following scenario
-- (λ0) ((λ0) (λ0))
--
-- So by the same logic, we'll need a constructor to "see past" the right argument of an app.
--
-- We'll do something cheesy here, which is to restrict ourselves to only applying this to values.
-- We do this so that we always have only a single way we could proceed with reduction, which simplifies our proofs later.
--
-- So our third constructor should state the following:
-- If N is a value, and we can reduce M to M', then we can reduce app V M to app V M'
--
-- Note that if we instead drop the "If N is a value" part, we can then choose to apply either red-app-l or red-app-r in some terms, e.g. in
-- ((λ0) (λ0)) ((λ0) (λ0))
--
-- TODO drop constructors
data _==>_ {ctx : Context} {ty : Type} : Lam ctx ty -> Lam ctx ty -> Set where

infix 2 _==>_

-- TASK
-- In order to do chains of beta reductions, we'll need to make a reflexive and transitive version of _==>>
--
-- Add two constructors:
-- 1. Any term reduces to itself (reflexivity)
-- 2. If N ==> M and M ==>> L, then N ==>> L (transitivity)
data _==>>_ {ctx : Context} {ty : Type} : Lam ctx ty -> Lam ctx ty -> Set where

infix 2 _==>>_

-- NOTE
-- We'll now introduce the same utilities we used for equational reasoning, but for ==>> instead,
-- so that we can write proofs using them

-- TASK
-- Synonym for reflexivity, used to end our proofs, much like we used _QED
_BQED : {ctx : Context} {ty : Type} (N : Lam ctx ty) -> N ==>> N
N BQED = ?

infix 3 _BQED

-- TASK
-- Synonym for transitvity, to allow us to chain proofs, much like we used _=[_]_
_=>[_]_ :
  {ctx : Context} {ty : Type} ->
  {M L : Lam ctx ty} ->
  (N : Lam ctx ty) ->
  N ==> M ->
  M ==>> L ->
  N ==>> L
N =>[ p ] q = ?
infixr 2 _=>[_]_

-- TASK
-- write
-- (λ0)
-- as a Lam
idLam : ?
idLam = ?

-- TODO: delete some stuff from here (types? all the sigs?)
module Ex1 where

  -- TASK
  -- Write
  -- ((λ0) (λ0)) (λ0)
  -- as a Lam
  ex1 : ?
  ex1 = ?

  -- TASK
  -- Prove that ex1 reduces to idLam
  _ : ex1 ==>> idLam
  _ =
    ex1 =>[ {! !} ]
    idLam BQED

-- TODO: delete some stuff from here (types? all the sigs?)
module Ex2 where

  -- TASK
  -- Write
  -- (λ0) ((λ0) (λ0))
  -- as a Lam
  ex2 : ?
  ex2 = ?

  -- TASK
  -- Prove that ex1 reduces to idLam
  _ : ex2 ==>> idLam
  _ =
    ex2 =>[ {! !} ]
    idLam BQED

-- TASK
-- Formulate and prove that if a term is a value, then it cannot reduce.
-- TODO
Val-no-red : ?
Val-no-red = ?

-- TASK
-- Formulate and prove that if a term can reduce, then it is not a value
no-red-Val : ?
no-red-Val = ?

-- TASK
-- We'll want to formulate, prove, and use the following property:
-- "Progress property": If a term is closed, then it is either a Val, or it can make a reduction step.
--
-- Implement a data type which captures these two possibilities for a given term N.
data Progress {ty : Type} (N : Lam [] ty) : Set where

-- TASK
-- Prove the progress property, as stated above.
progress : {ty : Type} -> (N : Lam [] ty) -> Progress N
progress = ?

-- TASK
-- Implement a function which determines if a given term is a value by using progress.
decVal : {ty : Type} -> (N : Lam [] ty) -> Dec (Val N)
decVal = ?

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

-- NOTE
-- For any closed term, we know that it reduces to some M, which is also a Val.
-- This data type captures this property.
--
-- We use a Maybe (Val M) due to some termination issues described below in eval
data Steps {ty : Type} : Lam [] ty -> Set where
  steps :
    {N : Lam [] ty} ->
    (M : Lam [] ty) ->
    N ==>> M ->
    Maybe (Val M) ->
    Steps N

-- TASK
-- Implement an evaluator for closed lambda terms.
-- We take an extra Nat argument as a counter for how many reduction steps we're allowed to do.
--
-- Theoretically, we don't need to count steps, because we usually know that closed STLC terms
-- can always be evaluated to values, but I didn't have the time to figure out how to satisfy
-- Agda's termination checker, so instead we use this Nat to be the decreasing value for each
-- recursive call, guaranteeing that we won't loop forever and making Agda happy.
eval : {ty : Type} -> Nat -> (N : Lam [] ty) -> Steps N
eval = ?
-}

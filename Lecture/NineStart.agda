{-# OPTIONS --no-unicode #-}
module Lecture.NineStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One
open import Lib.Dec
open import Lib.SnocList

-- TODO: Lib.Nat has Lt
-- TODO: Lib.SnocList

{-
-- TODO: define Type

infixr 11 _=>_

-- TODO: add example base types for later usage
alpha : Type
alpha = base 0

beta : Type
beta = base 1

gamma : Type
gamma = base 2

delta : Type
delta = base 3

-- TODO: contexts are snoclists of types
Context : Set
Context = SnocList Type

-- TODO: example contexts?

-- TODO: In for lists
-- TODO: replacing debruijn indices by membership proofs
-- TODO: In for contexts

infixr 12 S_

infix 10 _In_

-- TODO: examples of In


-- TASK
-- Indexing a context with a number which is "in bounds" of the context
-- (i.e. the number used to index is less than the length of the context)
ix : (n : Nat) (ctxt : Context) -> (Lt n (length ctxt)) -> Type
ix = ?

-- TASK
--
-- This is not only useful as a standalone statement,
-- but we're also going to use it to allow us to more conveniently
-- write Nats instead of manually writing out variables for a lambda
-- term later on.
ixIn :
  -- for a given n
  (n : Nat)
  -- and a context
  (ctxt : Context)
  -- if we know that n is less than the length of the context
  (p : Lt n (length ctxt)) ->
  -- then we can not only fetch out the item at index n,
  -- but also get proof that it is In the context
  ix n ctxt p In ctxt
ixIn = ?

-- TASK
-- Use the lecture notes to guide you on implementing the data type for
-- simply typed nameless lambda terms.
--
-- Remember that we're using _In_ to express a typed debruijn index.
data Lam (gamma : Context) : Type -> Set where
  var : ?
  app : ?
  lam : ?

-- TASK
-- Write a term which is a single variable
_ : Lam ([] -, alpha) alpha
_ = {! !}

-- TASK
-- Write a term which is a single variable, in a context of two possibly variables.
_ : Lam {! !} {! !}
_ = {! !}

-- TASK
-- Write the identity function term, i.e. λx.x
_ : Lam {! !} {! !}
_ = {! !}

-- TASK
-- Write the "const" function, i.e. λx.λy.x
_ : Lam {! !} {! !}
_ = ?

-- TASK
-- Write the "s combinator", i.e. λf.λg.λx.f x (g x)
_ : Lam ? ?
_ = ?

-- TASK
-- This function will allow us to refer to variables by their "debruin indices",
-- by implicitly converting numbers to In proofs (via ixIn), and then injecting them as vars.
`_ : {ctxt : Context} (n : Nat) -> {p : Lt n (length ctxt)} -> Lam ctxt (ix n ctxt p)
`_ = ?

-- TASK
-- Repeat the examples from above, but with `_

-- NOTE
-- A renaming is a way for us to send any type in one context to another context.
--
-- Since our variables are membership proofs(In), this means that we're
-- effectively renaming each variable, hence the name of this type synonym.
Ren : Context -> Context -> Set
Ren gamma delta = {tau : Type} -> tau In gamma -> tau In delta

-- TASK
-- The identity renaming, does nothing.
idRename : {gamma : Context} -> Ren gamma gamma
idRename = ?

-- TASK
-- A renaming that "shifts" all the variables "up by one".
shift1Rename : {gamma : Context} {sigma : Type} -> Ren gamma (gamma -, sigma)
shift1Rename = ?

-- TASK
-- We can "extend" renamings
-- In other words, if we can rename n variables, we can also rename n+1 variables,
-- by not doing anything to the freshly introduced new variable (sigma)
--
-- We need this because when we're doing a renaming of a term and want to recurse under a lambda,
-- the lambda will introduce a new variable, while our renaming (up to that point) will
-- only deal with the existing variables, before the newly introduced one.
--
-- Note that we do indeed *want* to not rename the newly introduced variable, because
-- when we apply this for lambdas, the newly introduced variable will be a *bound* variable,
-- and we want our renaming to not affect it.
extRen :
  {sigma : Type} {gamma delta : Context} ->
  Ren gamma delta ->
  Ren (gamma -, sigma) (delta -, sigma)
extRen = ?

-- TASK
-- Applying/lifting a renaming to a term
rename :
  {gamma delta : Context} ->
  -- if we have a renaming ρ
  Ren gamma delta ->
  -- and we have a typed term in the domain of that ρ
  {tau : Type} -> Lam gamma tau ->
  -- then we can rename all the variables by using ρ while preserving the type of the term
  Lam delta tau
rename = ?

-- NOTE
-- tl;dr Again, as with untyped Lams, we need to explicitly specify what our context is
-- because a single term is valid in many contexts.
--
-- longer version:
-- This function helps us specify the free variables of a Lam,
-- because in our Lam definition, nothing is preventing us from adding as many free variables as we like.
-- For example, the term
-- var Z
-- is a valid term in
-- Lam (alpha -, []) alpha
-- but it is also a valid term in
-- Lam (beta -, beta -, beta -, alpha -, []) alpha
-- Agda does not like this, since it can't figure out what the context should be,
-- so we need to manually specify it.
withContext : {tau : Type} (gamma : Context) -> Lam gamma tau -> Lam gamma tau
withContext _ x = x

-- NOTE
-- Convenience synonyms for small contexts
pattern [_] x = [] -, x
pattern [_,_] x y = [] -, x -, y
pattern [_,_,_] x y z = [] -, x -, y -, z

-- for example
_ : Context
_ = [ base 1 ]

_ : Context
_ = [ base 2 , (base 1 => base 2) , base 1 ]

-- UNIT TESTS
-- Note that you might (unfortunately) also have to specify implicit args to internal lambdas here,
-- since if we write (var Z), it is, again, not clear which type we want this var Z to be
-- (it could be any base n, for whatever n you pick)
--
-- Our id renaming should do nothing
_ : withContext [ base 5 ] (rename idRename (` 0)) == ` 0
_ = refl

_ : withContext [] (rename idRename (lam {[]} {alpha} {alpha} (` 0))) == lam (` 0)
_ = refl

-- Our shift renaming should.. shift
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ] (` 0)))
  ==
  ` 1
_ = refl

-- but it should take care not to touch bound variables
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ]
        (app
          (lam {_} {base 42} (` 0))
          (` 0))))
  ==
  app (lam (` 0)) (` 1)
_ = refl

-- NOTE
-- Similarly to a Ren,
-- a substitution is a way to map all the variables in one context to terms in another context.
--
-- Since our variables are membership proofs(In), this means that we're
-- effectively substituting each variable for a term.
Subst : Context -> Context -> Set
Subst gamma delta = {tau : Type} -> tau In gamma -> Lam delta tau

-- TASK
-- The substitution that replaces all variables with themselves.
idSubst : {gamma : Context} -> Subst gamma gamma
idSubst = ?

-- TASK
-- Once again, as with renamings, we can "extend" substitutions
-- If we have a substitution for n variables, we can make a substitution for n+1 variables,
-- by not doing anything for the newly introduced variables.
--
-- Once again, this is useful when we encounter a lambda, and we need to somehow deal with
-- the newly introduced variable appropriatley.
--
-- Note that we do indeed *want* to not substitute the newly introduced variable, because
-- when we apply this for lambdas, the newly introduced variable will be a *bound* variable,
-- and we want our substitution to not affect it.
extSubst :
  {gamma delta : Context} {sigma : Type} ->
  Subst gamma delta ->
  Subst (gamma -, sigma) (delta -, sigma)
extSubst = ?

-- TASK
-- We can apply/extend substitutions to terms
subst :
  {gamma delta : Context} {tau : Type} ->
  -- if we have a substitution θ
  Subst gamma delta ->
  -- and we have a typed term whose variables are all in the domain of θ
  Lam gamma tau ->
  -- then we can apply θ to get a new term of the same type
  Lam delta tau
subst = ?

-- NOTE
-- A "pretty" synonym for subst, somewhat mimicking some usual mathematical syntax
-- for applying substitutions.
_[_] :
  {gamma delta : Context} {tau : Type} ->
  Lam gamma tau ->
  Subst gamma delta ->
  Lam delta tau
x [ th ] = subst th x

infix 10 _[_]

-- UNIT TESTS
-- Write some unit tests yourselves :P
-}

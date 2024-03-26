{-# OPTIONS --no-unicode #-}

module Lecture.FourStart where

open import Lib.Zero
open import Lib.One
open import Lib.Two
open import Lib.Nat
open import Lib.Eq

-- TODO: mention Bins homework

-- TODO: mention new additions to libs:
-- new lemmas in Nat, <= in nat + lemmas for <=

-- TODO: hide eq import for now, enable after finishing demonstrations
-- TODO: new eq definition
-- old:
-- data _==_ {A : Set} : A -> A -> Set where
--   refl : (x : A) -> x == x
-- 1. Note how often we don't need to give the arg to refl, as witnessed by students. TODO: example
--    This is because when you have the type x == x, agda can clearly already infer what the arg is
--    Hence, we can make it implicit.
-- data _==_ {A : Set} : A -> A -> Set where
--   refl : {x : A} -> x == x
-- TODO: example
-- 2. Note how because it is now implicit, and is present in all the constructors of _==_, we can also make it a param instead.
-- data _==_ {A : Set} {x : A} : A -> Set where
--   refl : x == x
-- Remind how params work.
-- TODO: example of new refl usage in a simple case, and in a recursive proof
-- Note that we only had an explicit Eq so far for simplicity and to make it clearer what's going on when we're writing refl.

-- Show +N-commut to serve as a motivating example:
-- +N-commut' : (n m : Nat) -> n +N m == m +N n
-- +N-commut' zero m = ==-symm (+N-right-zero m)
-- +N-commut' (suc n) m = ==-trans (suc $= +N-commut' n m) (+N-right-suc m n)
-- 1. Introduce rewrite as a construct which allows us to use an equality to "rewrite all occurences of the left side to the right side".
--    Give a step by step example on +N-commut', using rewrites instead.
--    Note how rewrite is not symmetric - it only "rewrites" the left side to the right side, and not vice versa.
--    A good example for this is the fact that we need to use
--      rewrite ==-symm (+N-right-suc m n)
--    and just
--      rewrite +N-right-suc m n
--    doesn't do anything
--    Show that you can stack multiple rewrites one after the other in the recursive case.
--    End goal:
--      +N-commut' : (n m : Nat) -> n +N m == m +N n
--      +N-commut' zero m rewrite +N-right-zero m = refl
--      +N-commut' (suc n) m rewrite ==-symm (+N-right-suc m n) rewrite +N-commut' n m = refl
-- 2. rewrite is very nice for proving, but it has the issue of being hard to decipher afterwards - it's not very clear
--    what the proof is. It has the issue of the order of transformations not being clear, and it not being clear what we're transforming.
--    We can fix both of these issues with some clever operators.
--    Recall the ==-trans definition.
--    Bring forth the suggestion of introducing an operator form for ==-trans, to allow for more readable chaining, e.g.:
--      _//==_ :
--        {A : Set} {x y z : A} ->
--        x == y ->
--        y == z ->
--        x == z
--      _//==_ = ==-trans
--      infixr 10 _//==_
--    Now add a new +N-commut which uses _//==_ instead of ==-trans
--    We can now easily chain a lot of ==-trans without caring about parens, but the intermediate steps of the proof are still not clear -
--    in the chain x == y, y == z, z == u, we only know what x and u are, due to the end goal, but we don't really know much about y and z.
--    To remedy this, we can make one of the params of _//==_ explicit, so that at each step, we can see what exactly the term we're transforming is.
--      _=[_]_ :
--        {A : Set} {y z : A}
--        (x : A) ->
--        x == y ->
--        y == z ->
--        x == z
--      _ =[ p ] q = ==-trans p q
--      infixr 10 _=[_]_
--    We'll also add an explicit version of refl, so that we can also explicitly mention our final term:
--      _QED : {A : Set} (x : A) -> x == x
--      _ QED = refl
--      infix 11 _QED
--    Use this definition to show +N-commut again, step by step. First, note how you can always start a proof by writing out one usage of _=[_]_ and _QED,
--    with your initial and final terms:
--      +N-commut''' zero m =
--        m =[ {! !} ]
--        m +N zero QED
--    Also note that if you leave the holes empty like so:
--      +N-commut''' zero m =
--        ? =[ {! !} ]
--        ? QED
--    You can almost always use the auto command to fill them in, because agda knows what they are.
--    Finish the proof for the base case.
--      +N-commut''' zero m =
--        m =[ ==-symm (+N-right-zero m) ]
--        m +N zero QED
--    Repeat the same initial steps for the recursive case:
--        +N-commut''' (suc n) m =
--          suc (n +N m) =[ {! !} ]
--          m +N suc n QED
--    Now we can demonstrate how we can easily add additional _=[_]_ calls to extend our proof.
--      +N-commut''' (suc n) m =
--        suc (n +N m) =[ {! !} ]
--        {! !} =[ {! !} ]
--        m +N suc n QED
--    Note how we can either choose to
--    1. first fill in the first hole if we know what lemma we're using
--    2. or we can choose to first fill in the second hole, if we know what term we want to achieve
--    3. or we can even choose to fill in the last hole, if we know what lemma we want to use at the end.
--    Note how, again, if we fill in one of the lemmas, agda can once again automatically fill in the term hole.
--    Proceed to write the finished version:
--      +N-commut''' (suc n) m =
--        suc (n +N m) =[ suc $= +N-commut''' n m ]
--        suc (m +N n) =[ +N-right-suc m n ]
--        m +N suc n QED
--    Stop at this moment, and make sure that students understand how exactly the fixities work. A good idea is to
--    explicitly put all the parens on all the expressions, so that it's very clear what each operator is applied to.
--    Explicitly mention how _QED is a postfix operator which binds more tightly compared to _=[_], so we don't need to put parens there.
--    Explicitly mention _=[]_ which we can use for our own convenience to write two terms which are definitionally equal.
--


{-
-- TASK
-- Implement a linear and constant space tail recursive version of Nat addition
addNat : Nat -> Nat -> Nat
addNat = ?

-- TASK
-- Prove that your addNat behaves like +N.
-- Think about what lemma you'll need to formulate for the recursive case.
addNat-==-+N : (n m : Nat) -> addNat n m == n +N m
addNat-==-+N = ?

-- Traditionally defined recursive lists, parametrised by the type of elements in them.
data List (a : Set) : Set where
  -- the empty list is a list
  [] : List a
  -- we can add a new element to the "head" of a list
  _,-_ : a -> List a -> List a

infixr 21 _,-_

-- concatenate two lists
_+L_ : {A : Set} -> List A -> List A -> List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

infixr 22 _+L_

-- TASK
-- Prove that +L is associative
+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L (ys +L zs)
+L-assoc = ?

-- TASK
-- Formulate and prove that [] is a right identity for +L
+L-right-id : ?
+L-right-id = ?

-- TASK
-- Implement a function which returns the length of a list as a natural number
length : {A : Set} -> List A -> Nat
length = ?

-- TASK
-- Formulate and prove that length is functorial/homomorphic over +L, i.e.
-- the length of the result of +L is the sum of the lengths of its inputs.
+L-length : ?
+L-length = ?

-- TASK
-- Reverse a list by appending to the end of it
reverse : {A : Set} -> List A -> List A
reverse = ?

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll (most likely) need a lemma which comes as a generalisation of an equality in the recursive case
reverse-reverse-id : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-reverse-id = ?

-- TASK
-- Implement multiplication using +N
_*N_  : Nat -> Nat -> Nat
_*N_ = ?
infixr 120 _*N_

-- verify that *N behaves normally with a unit test
_ : 5 *N 4 == 20
_ = refl

-- TASK
-- Prove that *N is commutative.
-- Look at your cases and think about what lemmas you needed in +N-commut, and try to mirror them here.
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut = ?

-- TASK
-- Reverse a list in linear time and constant space by using a helper function
-- The special form of where used below allows us to refer to the definitions inside the
-- where by using a qualified syntax, i.e. we can refer to the inner go with reverseLinear.go
-- Also note that the where bound definition lets us refer to any names bound in the
-- parent function definition, so if we want to refer to A in its signature, we need
-- to explicitly bind the A type argument.
reverseLinear : {A : Set} -> List A -> List A
reverseLinear {A} = ?
  module reverseLinear where
  go : List A -> List A -> List A
  go = ?

-- TASK
-- Prove that reversing twice is the same as not doing anything
-- You'll need to formulate a helper lemma for reverseLinear.go
-- Think about what the invariant that reverseLinear.go is trying to maintain is, and how we can extract
-- the correctness property of reverse from it.
reverseLinear-reverseLinear-id : {A : Set} (xs : List A) -> reverseLinear (reverseLinear xs) == xs
reverseLinear-reverseLinear-id {A} xs = ?
  where
    goLem : ?
    goLem = ?

-- TASK
-- Prove that *N distributes over +N on the left
*N-left-distrib-+N : (n m k : Nat) -> n *N (m +N k) == n *N m +N n *N k
*N-left-distrib-+N = ?

-- TASK
-- Prove that *N distributes over +N on the right, by using *N-left-distrib-+N and *N-commut
*N-right-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-right-distrib-+N n m k = ?

-- TASK
-- Prove *N associative
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc = ?

-- TASK
-- +L and +N are very similar - indeed, if we ignore the elements of the list,
-- they're practically the same function. +L-length which you proved earlier expressed
-- one of the directions of this correspondence.
-- Can you think of some property (with possibly extra definitions) to express the other direction -
-- from +N to +L - of this correspondence?

-- TASK
-- If +N and +L "correspond" with each other, then what would *N correspond with?
-- Implement a function, let's call it _*L_, which you think is *N generalised to lists, and then prove
-- some "functorial"/"homomorphism" properties linking *N and your new *L.

record _*_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _*_ public
infixr 90 _*_

-- TASK
-- Implement list zipping, i.e. combining list elements pointwise, with the longer lists extra elements
-- getting chopped off and dropped.
-- e.g. in Haskell zip [1,2,3,6] [3,4,5] == [(1,3), (2, 4), (3, 5)]
zip : {A B : Set} -> List A -> List B -> List (A * B)
zip = {! !}

-- TASK
-- Does this zip function have some analogue for Nats?
-- Can you prove any properties linking the two?
-- Are there some obvious properties for "the Nat version of zip" which you can transfer back to zip?
-}

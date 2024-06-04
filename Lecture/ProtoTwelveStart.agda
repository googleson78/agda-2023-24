{-# OPTIONS --no-unicode #-}
{-# OPTIONS --type-in-type #-}

module Lecture.ProtoTwelveStart where

open import Lib.Sigma
open import Lib.Dec
open import Lib.List
open import Lib.Nat
open import Lib.Fin
open import Lib.Two
open import Lib.One
open import Lib.Zero
open import Lib.Eq

postulate
  ext :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) ->
    f == g

-- NOTE
-- Let's take a look at the number 3 and a 3 element list
-- suc    (suc    (suc    zero))
-- _,-_ x (_,-_ y (_,-_ z []))
-- Note how these are remarkably similar. It is also true that a lot of the functions on them are also remarkably similar,
-- e.g. +L and +N are almost identical.
--
-- Thanks to the fact that we're allowed to manipulate types as "normal values", it turns out that we can express a very great
-- deal of meta programs directly in Agda, so that we can actually only write "one" single function to implement bot +N and +L.
--
-- We'll take a look at one approach here, although I didn't have the time to flesh all of this out.
-- If you're interested, you should also take a look at indexed containers, polynomial functors, and descriptions (and more?), which
-- are all either alternative approaches or upgrades of Containers.
--
-- A Container is the "description" of something like what we usually imagine a "container" to be.
-- Concretely, a Container describes what the "shape" of something is, and given a shape,
-- what positions it may have items at.
record Container : Set where
  field
    -- We have a type describing all the possible shapes that our container can take.
    -- In order to get some understanding and intuition, it's good to keep in mind the following end goal:
    -- For both natural numbers and lists, this shape will be the natural numbers themselves, so Shape = Nat,
    -- with the intuition being that we describe a list by "the number of slots it has"
    Shape : Set
    -- Positions are indexed by shapes, because each shape may have different positions
    -- Since our shapes are Nats indicating how many slots we need to fill, we need to be able
    -- to say that if our shape is n : Nat, then we have n slots to fill.
    --
    -- This is exactly what Fin does, so we'll use Fin as our Position type for our running example.
    Position : Shape -> Set

open Container public

-- NOTE
-- Once we have a container description, we need to be able to turn that description into an
-- "actual" container. So if we assume that we have ListContainer, then [| ListContainer |] : Set -> Set
-- will be our notion of a list and correspond to our currently existing List type.
--
-- Do note that this is "just"
-- Shape C >< \shape -> Position C shape -> A
--
-- However, we choose to avoid _><_, so we can give better names to the fields, as we'll use them a lot.
record [|_|] (C : Container) (A : Set) : Set where
  constructor [|_|>_|]
  field
    -- In order to construct an element of a particular container, we need to pick what the shape will for this element
    -- If we want to represent the initial example here, we'll pick (suc (suc (suc zero))) to be the concrete shape.
    shape : Shape C
    -- and we also need to say, for each position for the chosen shape, what element is in that shape.
    -- In our running example, we've picked out the shape to be (suc (suc (suc zero))), hence
    -- our specialised
    -- elem : Fin 3 -> A
    -- will require us to provide three different As for the three different members of Fin 3.
    elem : Position C shape -> A

open [|_|] public

{-
-- TASK
-- Implement the Nat container, as previously discussed.
NatC : Container
NatC = ?

CNat : Set
CNat = [| NatC |] One

-- TASK
-- Implement "zero" via CNat
czero : CNat
czero = ?

-- TASK
-- Implmeent the suc function via CNat
csuc : CNat -> CNat
csuc = ?

-- TASK
-- Implement nat addition for CNat
addCNat : CNat -> CNat -> CNat
addCNat = ?

-- TASK
-- For a rough smoke test, prove that addCNat behaves the same way as +N

-- TASK
-- Implement the List container, as previously discussed.
ListC : Container
ListC = ?

CList : Set -> Set
CList = [| ListC |]

-- TASK
-- Implement a generic mapping function that works for any container
cmap : {C : Container} {X Y : Set} -> (X -> Y) -> [| C |] X -> [| C |] Y
cmap = ?

-- OPTIONAL TASK (untested)
-- Prove that for any Container C, [| C |] induces a functor in the AGDA category.

-- TASK
-- Convert an indexing function to a list.
-- It might already be obvious, but this will be useful when working with the positions of a list.
conv : {A : Set} (n : Nat) -> (Fin n -> A) -> List A
conv = ?

-- TASK
-- Think about what arguments/callbacks you'll need to provide so that you can convert
-- an arbitrary container to a list.
ctoList :
  {C : Container} {X : Set} ->
  (shapeToNat : Shape C -> Nat) ->
  ({shape : Shape C} -> (Position C shape -> X) -> Fin (shapeToNat shape) -> X) ->
  [| C |] X -> List X
ctoList = ?

-- TASK
-- Implement a generic "all" predicate on containers, i.e. All cx P should be inhabited iff
-- all of the elements of of cx satisfy P
CAll : {C : Container} {X : Set} -> (cx : [| C |] X) -> (P : X -> Set) -> Set
CAll = ?

-- TASK
-- Implement a generic "any" predicate on containers, i.e. All cx P should be inhabited iff
-- any of the elements of of cx satisfy P
CAny : {C : Container} {X : Set} -> (cx : [| C |] X) -> (P : X -> Set) -> Set
CAny = ?

-- TASK
-- Define a "membership relation" over arbitrary containers
CIn : {C : Container} {X : Set} -> X -> [| C |] X -> Set
CIn = ?

-- OPTIONAL TASK (untested)
-- Think about how to define a function, such that given
-- (x : X) -> Dec (P x)
-- we can implement
-- ... -> Dec (CAll P cx)
-- and
-- ... -> Dec (CAny P cx)
--
-- I didn't actually have the time to figure this out, so it's unclear how difficult this is.

-- TASK
-- Implement list append on CLists
appendCList : {X : Set} -> CList X -> CList X -> CList X
appendCList = ?

-- TASK
-- Implement a generic appendContainer which takes suitables HOFs/callbacks, so that you can "append"
-- any two containers.
--
-- Afterwards, reimplement appendCNat and appendCList using the new generic function

-- TASK
-- Implement binary trees via a container description.
--
-- More untested tasks:
-- Try to use ctoList to flatten a binary tree.
-- What can appendContainer do for binary trees?

-- TASK (untested)
-- We saw that containers automatically induce functors in AGDA.
-- It is not too far of a reach to then start thinking about transforming containers themselves, which would correspond to natural transformations.
-- While the container induced convert from [| C |] X to [| C |] Y, can we figure out some data type which represents a transformation/morphism
-- from a container description C1 to a container description C2?
--
record CMorph (C1 C2 : Container) : Set where

-- TASK (untested)
-- You should then, given a CMorph C1 C2, be able to transform one container to another.
<|_|> : {X : Set} {C1 C2 : Container} -> CMorph C1 C2 -> [| C1 |] X -> [| C2 |] X
<|_|> = ?

-- TASK (untested)
-- Can you give container morphisms between the existing example containers you've looked at thus far?

-- TASK (untested)
-- Prove that containers form a category, with the arrows being morphisms between containers.
-}

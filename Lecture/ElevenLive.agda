{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-unicode #-}

module Lecture.ElevenLive where

open import Lib.Eq
open import Lib.List
open import Lib.Vec
open import Lib.Nat
open import Lib.One
open import Lib.Two
open import Lib.Zero
open import Lib.Sigma

-- TODO:
-- discuss levels briefly
-- example: list of types
-- example: record containing Sets
--
-- TODO: {-# OPTIONS --type-in-type #-}
--
-- TODO: postulate

-- "тип"
-- data Nat : Set where
-- data List (A : Set) : Set where
-- data List {l : Level} (A : Set l) : Set (l + 1) where
--
-- List : ?????
-- Set : ?????

-- Set : Set

-- Set0 : Set1
-- Set1 : Set2
-- Set2 : ...
-- Set_n : Set_(n+1)

-- Set : Set

--record Foo : Set where
--  field
--    bar : Set


-- TODO: categories as an abstraction for compositions
-- TODO: reminder on copatterns, going to be useful again
-- TODO: AGDA as an example
-- TODO: THREE as an example

-- TODO: monoids in general
-- TODO: monoids as single object categories
-- "all of the info is in the arrows"
-- TODO: +N as example

-- TODO: preorders
-- "all of the info is in the objects"/"it doesn't matter how you get from object A to object B"
-- TODO: _<=_ as example

-- TODO: functors as an abstraction for homomorphisms
-- TODO: Maybe as an example

-- TODO: extensionality
-- example: addNat defined on its two args
-- example: linear search vs binary search

record Category : Set where
  field
    Obj : Set
    Arr : (x : Obj) -> (y : Obj) -> Set
    idArr : {x : Obj} -> Arr x x
    comp :
      {x y z : Obj} ->
      (f : Arr x y) ->
      (g : Arr y z) ->
      Arr x z
    idArr-comp :
      {x y : Obj}
      (f : Arr x y) ->
      comp (idArr {x}) f == f
    comp-idArr :
      {x y : Obj}
      (f : Arr x y) ->
      comp f (idArr {y}) == f
    assoc :
      {x y z w : Obj}
      (f : Arr x y) (g : Arr y z) (h : Arr z w) ->
      comp (comp f g) h == comp f (comp g h)

open Category public

id : {A : Set} -> A -> A
id x = x

-- NOTE
-- Function composition
_>>_ : {S R T : Set} -> (S -> R) -> (R -> T) -> S -> T
_>>_ f g x = g (f x)

-- C-c C-c
AGDA : Category
Obj AGDA = Set
Arr AGDA A B = A -> B
idArr AGDA = id
comp AGDA = _>>_
idArr-comp AGDA f = refl
-- comp idArr f
-- _>>_ idArr f
-- _>>_ id f
-- _>>_ (\x -> x) f
-- (\y -> _>>_ (\x -> x) f y)
-- (\y -> f ((\x -> x) y))
-- (\y -> f y)
comp-idArr AGDA f = refl
assoc AGDA f g h = refl
-- comp (comp f g) h == comp f (comp g h)
-- (f >> g) >> h == f >> (g >> h)

-- * --> *
--  \    |
--   \   |
--    \  |
--     \ |
--      \|
--       v
--       *
module Three where
  data Three : Set where
    -- zero : Three
    -- one : Three
    -- two : Three
    zero one two : Three

  data Arrow : Three -> Three -> Set where
    idArrThree : {x : Three} -> Arrow x x
    zero-one : Arrow zero one
    one-two : Arrow one two
    zero-two : Arrow zero two


  THREE : Category
  Obj THREE = Three
  Arr THREE = Arrow
  idArr THREE = idArrThree
  comp THREE idArrThree g = g
  comp THREE f idArrThree = f
  comp THREE zero-one one-two = zero-two
  idArr-comp THREE f = refl
  comp-idArr THREE idArrThree = refl
  comp-idArr THREE zero-one = refl
  comp-idArr THREE one-two = refl
  comp-idArr THREE zero-two = refl
  assoc THREE idArrThree idArrThree idArrThree = refl
  assoc THREE idArrThree idArrThree zero-one = refl
  assoc THREE idArrThree idArrThree one-two = refl
  assoc THREE idArrThree idArrThree zero-two = refl
  assoc THREE idArrThree zero-one idArrThree = refl
  assoc THREE idArrThree zero-one one-two = refl
  assoc THREE idArrThree one-two idArrThree = refl
  assoc THREE idArrThree zero-two idArrThree = refl
  assoc THREE zero-one idArrThree idArrThree = refl
  assoc THREE zero-one idArrThree one-two = refl
  assoc THREE zero-one one-two idArrThree = refl
  assoc THREE one-two idArrThree idArrThree = refl
  assoc THREE zero-two idArrThree idArrThree = refl

-- NOTE
-- "All of the info is in the objects", since there's at most one arrow between any two objects.
-- Effectively this means that with preorders we don't care how exactly we get from an arrow A to B,
-- just that there is one
record Preorder : Set where
  field
    cat : Category
    one-arrow :
      {x y : Obj cat} ->
      (f g : Arr cat x y) ->
      f == g


<=-unique : {n m : Nat} (p q : n <= m) -> p == q
<=-unique ozero ozero = refl
<=-unique (osuc p) (osuc q) = ap osuc (<=-unique p q)

-- TASK
<=-Cat : Category
Obj <=-Cat = Nat
Arr <=-Cat = _<=_
idArr <=-Cat = {! !}
comp <=-Cat = {! !}
idArr-comp <=-Cat = {! !}
comp-idArr <=-Cat = {! !}
assoc <=-Cat = {! !}

-- TASK
<=-Preorder : Preorder
<=-Preorder = ?

-- NOTE
-- "All of the info is in the arrows", since we only have one object.
-- Effectively this means that we only care about the arrows, and the case is usually that we have some operations as arrows.
record Monoid : Set where
  field
    cat : Category
    Obj-is-One : Obj cat == One

-- TASK
Nat+N-Cat : Category
Obj Nat+N-Cat = One
Arr Nat+N-Cat _ _ = Nat
idArr Nat+N-Cat = zero
comp Nat+N-Cat = _+N_
idArr-comp Nat+N-Cat = {! !}
comp-idArr Nat+N-Cat = {! !}
assoc Nat+N-Cat = {! !}

Nat+N-Monoid : Monoid
Nat+N-Monoid = ?

-- f : G -> H
-- f (eps_G) == eps_H
-- f (x <G> y) == f (x) <H> f (y)
-- F ((f >> g)) == F f >> F g

-- Functor
record _=>_ (C D : Category) : Set where
  field
    F-Obj : Obj C -> Obj D
    F-map :
      {x y : Obj C} ->
      (f : Arr C x y) ->
      Arr D (F-Obj x) (F-Obj y)

    F-map-id :
      (x : Obj C) ->
      F-map (idArr C {x}) == idArr D {F-Obj x}

    F-map-comp :
      {x y z : Obj C}
      (f : Arr C x y) (g : Arr C y z) ->
      F-map (comp C f g) == comp D (F-map f) (F-map g)

open _=>_ public

data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing : Maybe A

-- има аксиома ext
postulate
  ext :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) ->
    f == g

-- linear search
-- binary search

{-
-- TASK
-- A category with one object
-- *
ONE : Category
ONE = ?

-- TASK
-- A category with two objects, with an arrow between them
-- * --> *
module TwoCat where
  data ArrTwo : Two -> Two -> Set where

  TWO : Category
  TWO = ?

-- TASK
-- Similarly to Nat+N-Cat, +L induces a category which is also a monoid.
-- The objects will be One, since it's a monoid, and the arrows will be given by the
-- list append operation (_+L_).
List-+L-Cat : Set -> Category
List-+L-Cat = {!!}

-- TASK
List-+L-Monoid : Set -> Monoid
List-+L-Monoid = {!!}

-- TASK
-- A Discrete category is one in which the only arrows are the identity arrows
-- An example of such a category is the one formed with an arbitrary type, and _==_ as arrows
-- Implement the discrete category where the objects are elements of the type X, and
-- the arrows are the equalities between those elements.
module DiscreteEq (X : Set) where
  Discrete== : Category
  Discrete== = ?

-- TASK
-- We can make a category with whatever arrows we like if our objects are Zero.
module EmptyCat (Arrows : Set) where
  EMPTY : Category
  EMPTY = ?

-- TASK
-- We can always flip the directions of arrows in a category to form the "opposite" category.
-- This actually turns out to be a very useful concept in general.
Op : Category -> Category
Op = ?

-- TASK
-- Given two categories, we can form their product, by having objects which are tuples of objects
-- of our original categories, and lifting everything from our original categories pointwise for those tuples.
-- _*_ is your friend.
Product : Category -> Category -> Category
Product = ?
-}

{-

-- TASK
-- "Doing nothing" is a functor, i.e. we don't change the objects and we don't change the arrows.
ID : (C : Category) -> C => C
ID = {!!}

fmapMaybe :
  {A B : Set} ->
  (A -> B) ->
  Maybe A ->
  Maybe B
fmapMaybe f (just x) = just (f x)
fmapMaybe f nothing = nothing

fmapMaybe-id :
  {A : Set}
  (x : Maybe A) ->
  fmapMaybe id x == x
fmapMaybe-id (just x) = refl
fmapMaybe-id nothing = refl

-- TASK
MAYBE : AGDA => AGDA
F-Obj MAYBE A = Maybe A
F-map MAYBE = fmapMaybe
F-map-id MAYBE a =
  ext fmapMaybe-id
F-map-comp MAYBE = {! !}

-- TASK
map : {A B : Set} -> (A -> B) -> List A -> List B
map = {!!}

-- TASK
-- Mapping with the identity function does nothing
map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id = {!!}

-- TASK
-- Mapping with a composition of functions is the same as mapping with
-- one function, and then mapping with the other function.
map-compose :
  {A B C : Set} (f : A -> B) (g : B -> C) (xs : List A) ->
  map (f >> g) xs == map g (map f xs)
map-compose = {!!}

-- TASK
-- The List type constructor is a functor, in the same way that Maybe is a functor.
LIST : SET => SET
LIST = ?

-- TASK
-- Addition with the constant k forms a functor over the preorder Nat category
ADD : Nat -> <=-Cat => <=-Cat
ADD k = {!!}

-- TASK
-- Mapping with a function (f : X -> Y) over a list induces a functor between the monoid
-- categories of lists over X and Y respectively.
LIST+L : {X Y : Set} (f : X -> Y) -> List-+L-Cat X => List-+L-Cat Y
LIST+L f = {!!}

-- TASK
-- Define the "is prefix of" relation between lists
data _<=L_ {A : Set} : List A -> List A -> Set where

infix 15 _<=L_

module <=L-Cats {A : Set} where
  -- TASK
  -- Prove that lists of A equipped with _<=L_ form a category
  <=L-Cat : Category
  <=L-Cat = ?

  -- TASK
  -- Prove that that category is a preorder
  <=L-Preorder : Preorder
  <=L-Preorder = ?

  -- TASK
  -- We can form a functor from list prefixes to _<=_.
  -- Implement it.
  Drop-Elems : <=L-Cat => <=-Cat
  Drop-Elems = ?

-- TASK
-- Implement the function which takes a prefix of n elements from a Vector of size m,
-- by using the proof that n <= m to allow us to do so
-- We've already implement this previously, so feel free to copy it if you'd like
vTake : {A : Set} {n m : Nat} -> n <= m -> Vec A m -> Vec A n
vTake = {!!}

-- TASK
-- vTake gives rise to a functor, sending _<=_ functions over Vec A
-- If we look at vTakes signature, we'll notice that n <= m is transformed into (Vec A m -> Vec A n) -
-- note how the places of n and m are swapped.
-- As a consequence, we need to use the opposite cateogry of <=-Cat here, to make things line up.
VTAKE : Set -> Op <=-Cat => SET
VTAKE = {!!}

module FreeCat (X : Set) (R : X -> X -> Set) where
  -- TASK
  -- Given a type X and a binary relation R over X, we can form a "free category" based on X and R in the usual sense of "free algebraic structure".
  -- That is, we will force all the properties required of a category to hold synthetically, by introducing a new relation Free R : X -> X -> Set,
  -- such that X and Free R form a category.
  --
  -- Essentially, this means that we want to add some additional properties to R to get Free R, so that we can then prove our Category laws
  --
  -- Implement the datatype Free which adds those properties to R. It might be helpful to first try implementing the FREE
  -- category, to figure out what exactly you need.
  data Free : ? -> Set where

  -- TASK
  -- Since Free will form the arrows for our category, we will of course also need a way to compose Frees
  compFree : {x y z : X} -> Free x y -> Free y z -> Free x z
  compFree = {!!}

  -- TASK
  -- Implement hte free category over X and R by using Free and compFree
  FREE : Category
  FREE = {!!}

module Finite where
  -- TASK
  -- We've seen a few finite categories - ZERO, TWO, THREE
  -- We can take advantage of Fin n to define a generalised finite category, mimicking THREE.
  -- If we want a category "of size n", we'll take Fin n to be the objects.
  --
  -- The arrows will roughly be defined as
  -- n ~> m iff n <= m
  --
  -- Think about how to define all of these and implement the FINITE category.

  FINITE : Nat -> Category
  FINITE = ?
-}

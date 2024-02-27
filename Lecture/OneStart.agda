{-# OPTIONS --no-unicode #-}

module OneStart where

-- Bool
-- традиционен булев тип данни
-- can also write on the same line
-- живее в Lib.Two
data Two : Set where
  ff : Two
  tt : Two

not : Two -> Two
not ff = tt
not tt = ff

_&&_ : Two -> Two -> Two
ff && ff = ff
ff && tt = ff
tt && ff = ff
tt && tt = tt

-- празен тип
-- изразява логическо противоречие/"лъжа"
-- живее в Lib.Zero
data Zero : Set where

-- type signature:
-- dependent types
-- implicit params
zero-elim : {A : Set} -> Zero -> A
zero-elim ()

-- struct TwoTuple {bool fst; bool snd};
record TwoTuple : Set where
  field
    fstTwo : Two
    sndTwo : Two


open TwoTuple public

_ : TwoTuple
_ =
  record
    {
    fstTwo = tt ;
    sndTwo = ff
    }

swapTwoTuple : TwoTuple -> TwoTuple
swapTwoTuple
  record { fstTwo = pesho ; sndTwo = gosho } =
    record { fstTwo = gosho ; sndTwo = pesho }

-- One
-- trivial truth
-- constructor
-- живее в Lib.One

-- Zero and One
-- vs
-- ff and tt

-- DrinkType
-- MilkType
-- BeerType
-- Drink

-- TwoEq
-- examples
-- not-not-eq
-- explain with reductions
-- _&&_ assoc
-- explain stuckness

-- go back and change _&&_ to be lazier, show assoc again

-- Is
-- TwoEq via Is
-- TwoEq-implies-TwoEq'

-- _+_
-- sum
-- infixr 80 _+_
-- живее в Lib.Sum
-- swap

-- prod
-- open _*_ public
-- infixr 90 _*_
-- constructor
-- swap

-- explain uncommenting

{-
-- TASK
-- Prove assocativity of proposoitioanl "or"
+-assoc : {A B C : Set} -> A + (B + C) -> (A + B) + C
+-assoc = ?

-- TASK
-- Prove assocativity of proposoitioanl "and"
*-assoc : {A B C : Set} -> A * (B * C) -> (A * B) * C
*-assoc = ?

-- TASK
-- Prove distributivity of * over +
*-distrib-+ : {A B C : Set} -> A * (B + C) -> A * B + A * C
*-distrib-+ = ?

-- TASK
-- Prove _&&_ commutative
&&-commut : (b1 b2 : Two) -> TwoEq (b1 && b2) (b2 && b1)
&&-commut = ?

-- TASK
-- Implement "or" over boolean values
-- try to make the definition as "lazy" as possible, to make proofs easier!
_||_ : Two -> Two -> Two
_||_ = ?

-- TASK
-- prove || commutative
||-commut : (b1 b2 : Two) -> TwoEq (b1 || b2) (b2 || b1)
||-commut = {! !}

-- TASK
-- State assocativity of || and prove it
||-assoc : {! !}
||-assoc = {! !}

-- TASK
-- Define the NAND operation over bools
nandTwo : Two -> Two -> Two
nandTwo = ?

-- TASK
-- Define ff using tt and NAND
nandff : Two
nandff = ?

-- TASK
-- Formulate and prove that nandff is the same thing as ff

-- TASK
-- Define negation using only nandTwo and any previously defined operations involving nand.
nandNot : Two -> Two
nandNot = ?

-- TASK
-- Formulate and prove that nandNot behaves the same way as not

-- TASK
-- Define _&&_ using only nandTwo and any previously defined operations involving nand.
nandAnd : Two -> Two -> Two
nandAnd = ?

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _&&_

-- TASK
-- Define _||_ using only nandTwo and any previously defined operations involving nand.
nandOr : Two -> Two -> Two
nandOr = ?

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _||_

-- TASK
-- Define the structure of simple propositional expressions.
-- We want to support
--  1. a "false" value
--  2. a "true" value
--  3. "negating" a PropExpr
--  4. "or-ing" two PropExprs
--  5. "and-ing" two PropExprs
data PropExpr : Set where

-- TASK
-- You should be able to "convert" a boolean to a PropExpr
Two-to-PropExpr : Two -> PropExpr
Two-to-PropExpr = ?

-- TASK
-- Execute a PropExpr by using the boolean operations that the constructors are named after
interpProp : PropExpr -> Two
interpProp = ?

-- TASK
-- Formulate and prove that if you take two Twos, Two-to-Propexpr them, combine them with your "and" constructor, and interpret them,
-- the result is the same as just simply _&&_-ing the original Twos

-- TASK
-- Formulate and prove that TwoEq is
--  1. reflexive
--  2. symmetric
--  3. transitive
--  4. stable under function application, meaning TwoEq x y implies TwoEq (f x) (f y)
-}

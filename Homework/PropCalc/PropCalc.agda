module Homework.PropCalc.PropCalc where

open import Lib.EqExplicitRefl
open import Lib.Two


-- TASK
-- Prove _&&_ commutative
&&-commut : (b1 b2 : Two) -> b1 && b2 == b2 && b1
&&-commut = {! !}

-- TASK
-- Prove _&&_ associative
&&-assoc : (b1 b2 b3 : Two) -> (b1 && b2) && b3 == b1 && (b2 && b3)
&&-assoc = {! !}

-- TASK
-- Formulate and prove the fact that _||_ is commutative
||-commut : {! !}
||-commut = {! !}

-- TASK
-- State assocativity of || and prove it
||-assoc : {! !}
||-assoc = {! !}

-- TASK
-- Formulate and prove De Morgan's laws

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
Two-to-PropExpr = {! !}

-- TASK
-- Execute a PropExpr by using the boolean operations that the constructors are named after
interpProp : PropExpr -> Two
interpProp = {! !}

-- TASK
-- Formulate and prove that if you take two Twos, Two-to-Propexpr them, combine them with your "and" constructor, and interpret them,
-- the result is the same as just simply _&&_-ing the original Twos

-- TASK
-- Define the NAND operation over bools
nandTwo : Two -> Two -> Two
nandTwo = {! !}

-- TASK
-- Define ff using tt and NAND
nandff : Two
nandff = {! !}

-- TASK
-- Formulate and prove that nandff is the same thing as ff

-- TASK
-- Define negation using only nandTwo and any previously defined operations involving nand.
nandNot : Two -> Two
nandNot = {! !}

-- TASK
-- Formulate and prove that nandNot behaves the same way as not

-- TASK
-- Define _&&_ using only nandTwo and any previously defined operations involving nand.
nandAnd : Two -> Two -> Two
nandAnd = {! !}

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _&&_

-- TASK
-- Define _||_ using only nandTwo and any previously defined operations involving nand.
nandOr : Two -> Two -> Two
nandOr = {! !}

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _||_

-- TASK
-- Define the structure of "nand expressions", meaning minimal boolean expressions expresed purely via NAND.
-- We want to support
--   1. a "true" value
--   2. the NAND of two NandExprs
data NandExpr : Set where

-- TASK
-- Execute a NandExpr
interpNand : NandExpr -> Two
interpNand = {! !}

-- TASK
-- Transpile a PropExpr to a NandExpr
Prop-to-Nand : PropExpr -> NandExpr
Prop-to-Nand = {! !}

-- TASK
-- Formulate and prove that your Prop-to-Nand transpilation is correct in terms of interpProp and interpNand,
-- i.e. if you take a PropExpr, translate it to a NandExpr, and then interpNand it,
-- the result should be the same as interpProp-ing the original expression

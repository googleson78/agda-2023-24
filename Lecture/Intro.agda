{-# OPTIONS --no-unicode #-}
{-# OPTIONS --type-in-type #-}
-- interactive editting
--
-- editor?
-- * vscode
-- * emacs/vim
--
-- installation instructions will be posted
--
-- everyone done haskell?

-- x :: Bool
-- x = True

-- data Bool = Ff | Tt

-- Type
data Bool : Set where
  ff : Bool -- False
  tt : Bool -- True

_ : Bool
_ = tt

_ : Bool
_ = ff

-- load file:
-- space l
-- c-c c-l

-- not :: Bool -> Bool
-- not True = False
-- not False = True
--
-- not = _

-- space c
-- case split
not : Bool -> Bool
not ff = tt
not tt = ff

_&&_ : Bool -> Bool -> Bool
tt && tt = tt
x && y = ff

_ : Bool
_ = ff && tt

if_then_else_ :
  {A : Set} ->
  Bool ->
  A ->
  A ->
  A
if ff then x1 else x2 = x2
if tt then x1 else x2 = x1

_ : Bool
_ = if tt then ff else tt

record BoolTuple : Set where
  field
    fst : Bool
    snd : Bool

-- struct {bool fst; bool snd};

open BoolTuple public

-- refine
-- space r
_ : BoolTuple
_ =
  record
    {
    fst = tt ;
    snd = ff
    }

swapBoolTuple : BoolTuple -> BoolTuple
swapBoolTuple
  record { fst = pesho ; snd = gosho } =
    record { fst = gosho ; snd = pesho }

-- противоречие
data Zero : Set where


-- case on x
zero-elim : {A : Set} -> Zero -> A
zero-elim ()

-- zero-elim ????????

contr : Zero
contr = {! !}


_ : Zero
_ = {! !}

можеЛиДаИмаКнижка : Bool -> Set
можеЛиДаИмаКнижка ff = Zero
можеЛиДаИмаКнижка tt = Bool

record Person : Set where
  field
    над18ЛиЕ : Bool
    имаЛиШофьорскаКнижка :
      можеЛиДаИмаКнижка над18ЛиЕ

_ : Person
_ = record {
  над18ЛиЕ = ff ;
  имаЛиШофьорскаКнижка = {!zero-elim !}
  }
  -- tt е конструктор Bool



-- pesho = x.fst
-- gosho = x.snd

--
-- syntax examples:
-- * `:` instead of `::`
-- * data (Bool?)
-- * Set?
-- * functions (over Bool)
-- * holes
-- * cmd - load
-- * cmd - case split to intro variable
-- * cmd - case split to split variable
--     * asks
--     * or if in hole, directly splits
-- * give
-- * mixfix
--     * remember spaces!
-- * records (of Bools)
--     * matching on records
--     * refine to introduce function call
--     * introducing records via copatterns
--
-- types:
-- * Zero
--     * why? express "not possible"
--     * vs Haskell
--     * totality
--     * webservers, exceptions
--     * zero-elim
--     * "polymorphism"
--
-- * One
--     * why? express "trivially true"
--     * constructor
--
-- * booleans vs propositions
-- * BoolEq
--     * how to implement via Zero and One?
--     * examples
--     * Set = "relation"
--     * proving falsehood from falsehood
--
-- * &&-commut
--     * how to express?
--     * cmd - ask for context
--     * cmd - ask for type of thing in hole

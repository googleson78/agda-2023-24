module Lib.Two where

open import Lib.Zero
open import Lib.One

-- булеви стойности
data Two : Set where
  ff tt : Two

not : Two -> Two
not ff = tt
not tt = ff

-- създаване на "твърдение" от булева стойност,
-- или другояче казано "повишаване" на булеви стойности
-- позволява ни да изискваме доказателство базирано на резултата на булева операция
-- т.е. например Is (not (tt && ff)) изисква доказателство че tt && ff не е "истина"
Is : Two -> Set
Is ff = Zero
Is tt = One

_&&_ : Two -> Two -> Two
ff && y = ff
tt && y = y

infixr 70 _&&_

_||_ : Two -> Two -> Two
tt || y = tt
ff || y = y

infixr 60 _||_

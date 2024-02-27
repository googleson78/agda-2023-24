module Lib.Zero where

-- празният тип данни, не можем да създадем стойност от него
--
-- заради това изразява логическо противоречие и се използва когато искаме да изразим,
-- че нещо е невъзможно или би довело до противоречие
data Zero : Set where

-- ако имаме противоречие под формата на стойност от тип Zero, можем да докажем каквото и да е/
-- произведе, стойност от какъвто си тип искаме
zero-elim : {A : Set} -> Zero -> A
zero-elim ()
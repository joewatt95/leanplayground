namespace Utils

-- instance : Repr <| Std.PersistentArray α where
--   reprPrec := sorry

section macros
-- Racket-style hygienic macros.

-- Turn a binary operator into an infix one.
macro:65 arg1:term "<:" op:term ":>" arg2:term : term =>
  `($op $arg1 $arg2)

macro arg1:term "<=>?" arg2:term : term =>
  `(Ord.compare $arg1 $arg2)

macro:65 fun1:term "∘>" fun2:term : term =>
  `($fun2 ∘ $fun1)

macro "thunk" t:term : term =>
  `(Thunk.mk <| λ _ => $t)

macro "defthunk" id:ident ":" ty:term ":=" body:term : command =>
  `(def $id : Thunk $ty := thunk $body)

macro "defthunk" id:ident ":=" body:term : command =>
  `(def $id := thunk $body)

end macros

end Utils

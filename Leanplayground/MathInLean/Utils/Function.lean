import Mathlib.Data.Set.Function

namespace Function

universe u v
variable {α : Type u} {β : Type v}

open Function

lemma surj_of_isEmpty
  [IsEmpty β] {f : α → β}
  : Surjective f :=
  (. |> IsEmpty.false |>.elim)

end Function

import Mathlib.Data.Set.Basic

namespace Utils

variable {T : Type u}

@[simp]
lemma nonempty_iff_exists : Nonempty T ↔ ∃ _ : T, True :=
  ⟨h1, h2⟩
  where
    h1 := λ ⟨x⟩ => show ∃ _, True from ⟨x, trivial⟩
    h2 := λ ⟨x, _⟩ => show Nonempty T from ⟨x⟩

@[simp]
lemma nonempty_subtype_iff_exists {X : Set T} : Nonempty X ↔ ∃ a, a ∈ X :=
  ⟨h1, h2⟩
  where
    h1 := λ ⟨⟨a, a_in_X⟩⟩ => ⟨a, a_in_X⟩
    h2 := λ ⟨a, a_in_X⟩ => ⟨⟨a, a_in_X⟩⟩

end Utils
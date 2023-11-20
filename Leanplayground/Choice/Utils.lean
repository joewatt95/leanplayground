import Mathlib.Data.Set.Basic

namespace Utils

@[simp]
lemma nonempty_iff_exists : Nonempty α ↔ ∃ _ : α, True :=
  ⟨h1, h2⟩
  where
    h1 := λ ⟨x⟩ => show ∃ _, True from ⟨x, trivial⟩
    h2 := λ ⟨x, _⟩ => show Nonempty α from ⟨x⟩

@[simp]
lemma nonempty_subtype_iff_exists {X : Set α} : Nonempty X ↔ ∃ a, a ∈ X :=
  ⟨h1, h2⟩
  where
    h1 := λ ⟨⟨a, a_in_X⟩⟩ => ⟨a, a_in_X⟩
    h2 := λ ⟨a, a_in_X⟩ => ⟨⟨a, a_in_X⟩⟩

end Utils

import Mathlib.Data.Set.Basic

namespace Sets

universe u
variable {α : Type u} (s t u : Set α)

-- open Set

example : s ∩ t = t ∩ s := by
  ext _; exact ⟨mp, mpr⟩
  where
    mp {x} : x ∈ s ∧ x ∈ t → x ∈ t ∧ x ∈ s
      | ⟨x_in_s, x_in_t⟩ => ⟨x_in_t, x_in_s⟩

    mpr {x} : x ∈ t ∧ x ∈ s → x ∈ s ∧ x ∈ t
      | ⟨x_in_t, x_in_s⟩ => ⟨x_in_s, x_in_t⟩

example (_ : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  λ x ⟨(_ : x ∈ s), (_ : x ∈ u)⟩ ↦
    have : x ∈ t := ‹s ⊆ t› ‹x ∈ s›
    show x ∈ t ∧ x ∈ u by aesop

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u :=
  λ x ⟨(_ : x ∈ s), (_ : x ∈ t ∪ u)⟩ ↦
    match ‹x ∈ t ∪ u› with
    | .inl (_ : x ∈ t) => .inl ⟨‹x ∈ s›, ‹x ∈ t›⟩
    | .inr (_ : x ∈ u) => .inr ⟨‹x ∈ s›, ‹x ∈ u›⟩

example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  λ x ⟨(x_in_s : x ∈ s), (_ : x ∉ t ∪ u)⟩ ↦
    have : x ∉ t := λ _ : x ∈ t ↦ ‹x ∈ t› |> .inl |> ‹x ∉ t ∪ u›
    have : x ∉ u := λ _ : x ∈ u ↦ ‹x ∈ u› |> .inr |> ‹x ∉ t ∪ u›
    show (x ∈ s ∧ x ∉ t) ∧ x ∉ u from ⟨⟨‹x ∈ s›, ‹x ∉ t›⟩, ‹x ∉ u›⟩

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v
where
  mp (_ : f '' s ⊆ v) x (_ : x ∈ s) :=
    suffices f x ∈ v by aesop
    have : f x ∈ f '' s := by aesop
    show f x ∈ v from ‹f '' s ⊆ v› this

  mpr (_ : s ⊆ f ⁻¹' v) y (_ : y ∈ f '' s) :=
    have : ∀ x ∈ s, f x ∈ v
    | x, (_ : x ∈ s) =>
      have : x ∈ f ⁻¹' v := ‹s ⊆ f ⁻¹' v› ‹x ∈ s›
      by aesop
    have : ∃ x ∈ s, f x = y := by aesop
    show y ∈ v by aesop

end Sets

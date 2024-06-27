import Mathlib.Data.Real.Basic

import Leanplayground.MathInLean.Utils.Tactic

namespace Hierarchies

universe u

class One₁ (α : Type u) where
  /-- The element one -/
  one : α

class Inv₁ (α : Type u) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
notation "𝟙" => One₁.one

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Dia₁ (α : Type u) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia

class Semigroup₁ (α : Type u) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ {a b c : α}, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

class OneDia (α : Type u) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ {a : α}, 𝟙 ⋄ a = a

class DiaOne (α : Type u) extends One₁ α, Dia₁ α where
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ {a : α}, a ⋄ 𝟙 = a

class DiaComm (α : Type u) extends Dia₁ α where
  dia_comm : ∀ {a b : α}, a ⋄ b = b ⋄ a

class Monoid₁ (α : Type u) extends Semigroup₁ α, OneDia α, DiaOne α

class InvDia (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  inv_dia : ∀ {a : α}, a⁻¹ ⋄ a = 𝟙

class DiaInv (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  dia_inv : ∀ {a : α}, a ⋄ a⁻¹ = 𝟙

class Group₁ (α : Type u) extends Monoid₁ α, InvDia α, DiaInv α where

export Semigroup₁ (dia_assoc)

export DiaOne (dia_one)
export OneDia (one_dia)

export DiaInv (dia_inv)
export InvDia (inv_dia)

lemma inv_eq_of_dia [Group₁ G] {a b : G} (_ : a ⋄ b = 𝟙) : a⁻¹ = b := by
  egg [*, one_dia, dia_one, inv_dia, dia_assoc]

lemma dia_inv [Group₁ G] {a : G} : a ⋄ a⁻¹ = 𝟙 := by
  duper [one_dia, dia_one, inv_dia, dia_assoc]

class CommMonoid₁ (α : Type u) extends Semigroup₁ α, DiaOne α, OneDia α where
  dia_comm : ∀ {a b : α}, a ⋄ b = b ⋄ a
  dia_one {a} := show a ⋄ 𝟙 = a by egg [dia_comm, one_dia]
  one_dia {a} := show 𝟙 ⋄ a = a by egg [dia_comm, dia_one]

class CommGroup₁ (α : Type u) extends CommMonoid₁ α, DiaInv α, InvDia α where
  dia_inv {a} := show a ⋄ a⁻¹ = 𝟙 by rw [dia_comm, inv_dia]
  -- inv_dia {a} := show a⁻¹ ⋄ a = 𝟙 by rw [dia_comm]; exact dia_inv

export CommMonoid₁ (dia_comm)

instance [inst : CommMonoid₁ α] : Monoid₁ α := { inst with }
instance [inst : CommGroup₁ α] : Group₁ α := { inst with }

noncomputable instance : CommGroup₁ ℝ where
  dia x y := x * y
  inv x := x⁻¹
  one := 1
  dia_assoc {a b c} := show a * b * c = a * (b * c) by ring
  dia_comm {a b} := show a * b = b * a by ring
  one_dia {a} := show 1 * a = a by ring
  -- dia_one {a} := show a * 1 = a by ring
  inv_dia := sorry
  dia_inv := sorry

-- #check (inferInstance : Monoid₁ ℝ)

end Hierarchies

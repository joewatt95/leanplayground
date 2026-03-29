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

class DiaOne (α : Type u) extends Dia₁ α, One₁ α where
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ {a : α}, a ⋄ 𝟙 = a

class OneDia (α : Type u) extends Dia₁ α, One₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ {a : α}, 𝟙 ⋄ a = a

class Monoid₁ (α : Type u) extends Semigroup₁ α, DiaOne α, OneDia α

-- class Group₁ (α : Type u) extends Monoid₁ α, Inv α where
--   inv_dia : ∀ {a : α}, a⁻¹ ⋄ a = 𝟙
--   dia_inv : ∀ {a : α}, a ⋄ a⁻¹ = 𝟙

class DiaComm (α : Type u) extends Dia₁ α where
  dia_comm : ∀ {a b : α}, a ⋄ b = b ⋄ a

class InvDia (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  inv_dia : ∀ {a : α}, a⁻¹ ⋄ a = 𝟙

class DiaInv (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  dia_inv : ∀ {a : α}, a ⋄ a⁻¹ = 𝟙

export Semigroup₁ (dia_assoc)

export DiaOne (dia_one)
export OneDia (one_dia)

export DiaInv (dia_inv)
export InvDia (inv_dia)

export DiaComm (dia_comm)

class Group₁ (α : Type u) extends DiaInv α, Monoid₁ α, InvDia α where
  inv_dia {a} :=
    show a⁻¹ ⋄ a = 𝟙 by
      duper [dia_one, dia_inv, dia_assoc] {portfolioInstance := 1}

  one_dia {a} :=
    have : 𝟙 ⋄ a = a ⋄ 𝟙 := by
      duper [dia_one, dia_inv, dia_assoc] {portfolioInstance := 1}
    show 𝟙 ⋄ a = a by duper [this, dia_one] {portfolioInstance := 1}

class Group₁' (α : Type u) extends InvDia α, Monoid₁ α, DiaInv α where
  dia_inv {a} :=
    show a ⋄ a⁻¹ = 𝟙 by
      duper [one_dia, inv_dia, dia_assoc] {portfolioInstance := 1}

  dia_one {a} :=
    have : 𝟙 ⋄ a = a ⋄ 𝟙 := by
      duper [one_dia, inv_dia, dia_assoc] {portfolioInstance := 1}
    show a ⋄ 𝟙 = a by duper [this, one_dia] {portfolioInstance := 1}

instance [inst : Group₁' α] : Group₁ α := { inst with }

lemma inv_eq_of_dia [Group₁ G] {a b : G} (_ : a ⋄ b = 𝟙) : a⁻¹ = b := by
  duper [‹a ⋄ b = 𝟙›, one_dia, dia_one, inv_dia, dia_assoc]
    {portfolioInstance := 1}

class CommMonoid₁ (α : Type u) extends DiaComm α, Monoid₁ α where
  dia_one {a : α} :=
    show a ⋄ 𝟙 = a by duper [dia_comm, one_dia] {portfolioInstance := 1}

class CommGroup₁ (α : Type u) extends Group₁ α, CommMonoid₁ α

-- instance [inst : CommMonoid₁ α] : Monoid₁ α := { inst with }

instance : CommGroup₁ ℝˣ :=
  have {a b : ℝˣ} : a * b = b * a := mul_comm _ _
  -- have {a : ℝˣ} : 1 * a = a := one_mul _
  have {a : ℝˣ} : a⁻¹ * a = 1 := inv_mul_cancel _
  { dia := (. * .)
    inv := λ x ↦ x⁻¹
    one := 1
    dia_assoc := λ {a b c} ↦ show a * b * c = a * (b * c) from mul_assoc _ _ _
    dia_comm := ‹_›
    dia_inv := λ {a} ↦ show a * a⁻¹ = 1 by duper [*]
    dia_one := λ {a} ↦ show a * 1 = a from mul_one _
  }

instance : CommMonoid₁ ℤ :=
  have {a b : ℤ} : a * b = b * a := Int.mul_comm _ _
  have {a : ℤ} : a * 1 = a := Int.mul_one _
  { dia := (. * .)
    one := 1
    dia_assoc := Int.mul_assoc _ _ _
    dia_comm := ‹_›
    one_dia := λ {a} ↦ show 1 * a = a by duper [*] }

-- #check (inferInstance : Monoid₁ ℝˣ)

end Hierarchies

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

class DiaAssoc (α : Type u) extends Dia₁ α where
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

class InvDia (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  inv_dia : ∀ {a : α}, a⁻¹ ⋄ a = 𝟙

class DiaInv (α : Type u) extends Dia₁ α, One₁ α, Inv₁ α where
  dia_inv : ∀ {a : α}, a ⋄ a⁻¹ = 𝟙

export DiaAssoc (dia_assoc)

export DiaOne (dia_one)
export OneDia (one_dia)

export DiaInv (dia_inv)
export InvDia (inv_dia)

export DiaComm (dia_comm)

class Semigroup₁ (α : Type u) extends DiaAssoc α

class Monoid₁ (α : Type u) extends Semigroup₁ α, OneDia α, DiaOne α

class Group₁ (α : Type u) extends Monoid₁ α, InvDia α, DiaInv α where
  dia_inv {a} :=
    show a ⋄ a⁻¹ = 𝟙 by
      duper [one_dia, inv_dia, dia_assoc] {portfolioInstance := 1}
  inv_dia {a} :=
    show a⁻¹ ⋄ a = 𝟙 by
      duper [dia_one, dia_inv, dia_assoc] {portfolioInstance := 1}

lemma inv_eq_of_dia [Group₁ G] {a b : G} (_ : a ⋄ b = 𝟙) : a⁻¹ = b := by
  egg [*, one_dia, dia_one, inv_dia, dia_assoc]

class CommMonoid₁ (α : Type u)
extends Semigroup₁ α, DiaOne α, OneDia α, DiaComm α
where
  dia_one {a} := show a ⋄ 𝟙 = a by egg [dia_comm, one_dia]
  one_dia {a} := show 𝟙 ⋄ a = a by egg [dia_comm, dia_one]

class CommGroup₁ (α : Type u)
extends CommMonoid₁ α, Group₁ α, DiaInv α, InvDia α

instance [inst : CommMonoid₁ α] : Monoid₁ α := { inst with }
-- instance [inst : CommGroup₁ α] : Group₁ α := { inst with }

instance : CommGroup₁ ℝˣ where
  dia x y := x * y
  inv x := x⁻¹
  one := 1
  dia_assoc {a b c} := show a * b * c = a * (b * c) from mul_assoc _ _ _
  dia_comm {a b} := show a * b = b * a from mul_comm _ _
  one_dia {a} := show 1 * a = a from one_mul _
  -- dia_one {a} := show a * 1 = a from mul_one _
  inv_dia {a} := show a⁻¹ * a = 1 from inv_mul_self _
  dia_inv {a} := show a * a⁻¹ = 1 from mul_inv_self _

-- #check (inferInstance : Monoid₁ ℝ)

end Hierarchies

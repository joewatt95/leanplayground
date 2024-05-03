import Duper
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

namespace Sets

-- set_option autoImplicit false

open Set Function

variable
  {f : α → β} {g : β → α}
  (f_inj : Injective f)
  (g_inj : Injective g)

private def F : Set α →o Set α
where
  toFun X := (g '' (f '' X)ᶜ)ᶜ
  monotone'
    | X, Y, X_leq_Y, Z, Z_in_phi_X => by aesop

private abbrev Lfp : Set α := OrderHom.lfp (@F α β f g)

#check F.map_lfp

-- private lemma h :
--   g '' (f '' (@Lfp α β f g))ᶜ = (@Lfp α β f g)ᶜ :=
--   have : F (@Lfp α β f g) = (@Lfp α β f g) := F.map_lfp
--   have : F (@Lfp α β f g) = (g '' (f '' (@Lfp α β f g))ᶜ)ᶜ := by aesop
--   have : (g '' (f '' Lfp)ᶜ)ᶜ = (@Lfp α β f g) := by aesop
--   show g '' (f '' (@Lfp α β f g))ᶜ = (@Lfp α β f g)ᶜ from
--     compl_injective $ by simp; exact this

  -- have := calc
  --   (g '' (f '' (@Lfp α β f g))ᶜ)ᶜ = F (@Lfp α β f g) := by aesop
  --                                _ = (@Lfp α β f g) := by duper [F.monotone']
  -- sorry

-- theorem csb : Bijective h := sorry

end Sets

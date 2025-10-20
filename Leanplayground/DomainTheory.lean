import Mathlib.Topology.Order.ScottTopology
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

import Leanplayground.MathInLean.Utils.Tactic

open Ordinal OrdinalApprox OmegaCompletePartialOrder OrderHom

lemma biSup_eq_sSup {S : Set α} {f : α → β} [CompleteLattice β] :
  ⨆ x ∈ S, f x = sSup {f x | x ∈ S} := calc
      ⨆ x ∈ S, f x
  _ = ⨆ x : {x // x ∈ S}, f x := iSup_subtype'
  _ = sSup {f x | x ∈ S}      := by
    simp only [←sSup_range, Set.range, Subtype.exists, exists_prop]

instance [inst : CompleteLattice α] : Lean.Order.CCPO α :=
  let {le, le_refl, le_trans, le_antisymm, sSup, le_sSup, sSup_le, ..} := inst
  { rel := le
    rel_refl := le_refl _
    rel_trans := le_trans _ _ _
    rel_antisymm := le_antisymm _ _
    csup := sSup
    csup_spec _ :=
      { mp a _ a_1 := le_trans _ _ _ (le_sSup _ _ a_1) a
        mpr := sSup_le _ _ } }

variable
  [CompleteLattice α] {f : α →o α}
  (omega_continuous : ωScottContinuous f)

-- Sanity check.
example [CompleteLattice β] {f : α → β} :
  Monotone f ↔ Lean.Order.monotone f := .rfl

lemma lfpApprox_add_one_bot {o} : lfpApprox f ⊥ (o + 1) = f (lfpApprox f ⊥ o) :=
  lfpApprox_add_one _ _ (OrderBot.bot_le _) _

lemma lfpApprox_ofNat_eq_Nat_iterate :
  ∀ {n : ℕ}, lfpApprox f ⊥ n = f^[n] ⊥
  | 0 => by unfold lfpApprox; simp
  | n + 1 => calc
      lfpApprox f ⊥ (n + 1)
  _ = f (lfpApprox f ⊥ n)  := lfpApprox_add_one_bot
  _ = f (f^[n] ⊥)          := by rw [lfpApprox_ofNat_eq_Nat_iterate]
  _ = f^[n + 1] ⊥          := by rw [Function.iterate_succ_apply']

lemma lfp_eq_lfpApprox_ord_of_fixed_point
  (_ : f (lfpApprox f ⊥ o) = lfpApprox f ⊥ o) :
  lfp f = lfpApprox f ⊥ o :=
  have ⟨o', (_ : lfpApprox f ⊥ o' = lfp f)⟩ :=
    OrdinalApprox.lfp_mem_range_lfpApprox _
  calc
      lfp f
  _ = lfpApprox f ⊥ o' := Eq.symm ‹_›
  _ = lfpApprox f ⊥ o :=
    have :
      (o' ≤ o → lfpApprox f ⊥ o = lfpApprox f ⊥ o') ∧
      (o' ≥ o → lfpApprox f ⊥ o' = lfpApprox f ⊥ o) := by
      refine ⟨?_, ?_⟩
      repeat
        intro
        apply lfpApprox_eq_of_mem_fixedPoints
        . exact OrderBot.bot_le _
        . assumption
        . simp_all only [Function.mem_fixedPoints_iff, map_lfp]
    have := le_total o o'
    by aesop

lemma lfpApprox_limit_eq_sup_lfpApprox (_ : Order.IsSuccLimit o) :
  lfpApprox f ⊥ o = ⨆ o' < o, lfpApprox f ⊥ o' :=
  Eq.symm <| calc
      ⨆ o' < o, lfpApprox f ⊥ o'
  _ = sSup {lfpApprox f ⊥ o' | o' < o} := biSup_eq_sSup

  _ = sSup {f (lfpApprox f ⊥ o') | o' < o} :=
    le_antisymm
      (sSup_le_sSup_of_forall_exists_le <| by
        simp only [Set.mem_setOf_eq, exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        refine λ o' (_ : o' < o) ↦
          ⟨o' + 1, Order.IsSuccLimit.add_one_lt ‹_› ‹_›, ?_⟩

        have : lfpApprox f ⊥ o' ≤ lfpApprox f ⊥ (o' + 1) :=
          lfpApprox_monotone _ _ <| Ordinal.le_add_right _ _

        calc
            lfpApprox f ⊥ o'
        _ ≤ lfpApprox f ⊥ (o' + 1)      := this
        _ = f (lfpApprox f ⊥ o')        := lfpApprox_add_one_bot
        _ ≤ f (lfpApprox f ⊥ <| o' + 1) := f.monotone' this) <|

      sSup_le_sSup λ a
        ⟨o', (_ : o' < o), (_ : f (lfpApprox f ⊥ o') = a)⟩ ↦
        ⟨o' + 1, Order.IsSuccLimit.add_one_lt ‹_› ‹_›, by rwa [lfpApprox_add_one_bot]⟩

  _ = lfpApprox f ⊥ o := by
    conv => rhs; unfold lfpApprox
    simp only [exists_prop, Set.union_singleton, sSup_insert, bot_le, sup_of_le_right]

lemma lfpApprox_omega0_eq_sSup_lfpApprox_Nat :
  lfpApprox f ⊥ ω = ⨆ n : ℕ, lfpApprox f ⊥ n :=
  calc
      lfpApprox f ⊥ ω
  _ = ⨆ o < ω, lfpApprox f ⊥ o := lfpApprox_limit_eq_sup_lfpApprox isSuccLimit_omega0
  _ = sSup {lfpApprox f ⊥ o | o < ω} := biSup_eq_sSup
  _ = ⨆ n : ℕ, lfpApprox f ⊥ n := by
    aesop (add unsafe congr) (add norm lt_omega0)

theorem fix_eq_order_lfp :
  Lean.Order.fix f f.monotone' = lfp f :=
  open Lean.Order in
  have : fix f f.monotone' ≤ lfp f :=
    -- Transfinite induction over fixpoint iteration sequence, because that's
    -- the only proof rule the Lean compiler has for its domain theoretic
    -- fixpoint constructions.
    fix_induct _
      -- Successor stage
      (h := λ x (_ : x ≤ lfp f) ↦ f.map_le_lfp ‹_›)
      -- Limit stage
      (hadm := by aesop (add unsafe sSup_le) (add norm [admissible, CCPO.csup]))

  have : lfp f ≤ fix f f.monotone' :=
    -- RHS is a fixed point of f
    f |>.monotone' |> fix_eq |>.symm
    -- Hence it upper bounds the least fixed point of f
      |> lfp_le_fixed _

  le_antisymm ‹_› ‹_›

-- The fixpoint combinator as used in the Lean compiler is denotationally equal
-- to the transfinite iteration over ordinals up to the Hartog number of the
-- underlying domain.
open Cardinal in
theorem fix_mem_range_lfpApprox :
  Lean.Order.fix f f.monotone' = lfpApprox f ⊥ (Order.succ #α).ord := by
  rw [fix_eq_order_lfp, lfpApprox_ord_eq_lfp]

-- Kleene fixpoint theorem, via fixed point iteration over `Ordinal` up to `ω`
-- as opposed to `ℕ`.
include omega_continuous in
theorem kleene_fixed_point :
  lfp f = lfpApprox f ⊥ ω :=
  let lfpApproxNat : Nat →o α :=
    { toFun := lfpApprox f ⊥ ∘ λ n : ℕ ↦ (n : Ordinal)
      monotone' := by aesop
        (add unsafe [Monotone.comp, Nat.mono_cast, lfpApprox_monotone]) }

  have : f (⨆ n, lfpApproxNat n) = ⨆ n, f (lfpApproxNat n) := by
    simp_all only [
      ωScottContinuous_iff_map_ωSup_of_orderHom, Chain, ωSup, Chain.map,
      comp_coe, Function.comp_apply]

  lfp_eq_lfpApprox_ord_of_fixed_point <| calc
        f (lfpApprox f ⊥ ω)

    _ = f (⨆ n : ℕ, lfpApprox f ⊥ n) := by rw [lfpApprox_omega0_eq_sSup_lfpApprox_Nat]

    _ = ⨆ n : ℕ, f (lfpApprox f ⊥ n) := by
      simp_all only [coe_mk, Function.comp_apply, lfpApproxNat]

    _ = ⨆ n : ℕ, lfpApprox f ⊥ (n + 1) :=
      have := @lfpApprox_add_one_bot (f := f)
      by simp_all only [add_one_eq_succ, lfpApproxNat]

    _ = ⨆ n : ℕ, lfpApprox f ⊥ n :=
      le_antisymm
        (sSup_le_sSup λ _ ⟨n, _⟩ ↦ ⟨n + 1, by simp_all only [add_one_eq_succ, Set.mem_range, Nat.cast_add, Nat.cast_one]⟩) <|
        sSup_le_sSup_of_forall_exists_le λ a ⟨n, h⟩ ↦ by
          simp_all only [Set.mem_range, add_one_eq_succ, exists_exists_eq_and]
          exact ⟨n, by rw [←h]; apply lfpApprox_monotone; exact Order.le_succ _⟩

    _ = lfpApprox f ⊥ ω := by rw [lfpApprox_omega0_eq_sSup_lfpApprox_Nat]

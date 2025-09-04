import Mathlib.Data.Set.Lattice
import Leanplayground.Choice.Utils

namespace StandardChoice

variable {α β : Type u} {σ : α → Type v}

-- syntax term "↦" term : term
-- macro_rules
--   | `($input ∈ $domain ↦ $output ∈ $codomain)
--   => `(λ ($input : $domain) => ($output : $codomain))
--   | `($input ↦ $output ∈ $codomain)
--   => `(λ $input => ($output : $codomain))
--   | `($input ∈ $domain ↦ $output)
--   => `(λ ($input : $domain) => $output)
--   | `($input ↦ $output)
--   => `(λ $input => $output)

-- macro_rules
-- | `({$term ∈ $type | $t}) => `({$term : $type | $t})

-- macro "define" id:ident "as" term:term "," body:term : term =>
--   `(let $id := $term; $body)

-- syntax ("[" ident "]")? "we" "have" term "," "because" term "," term : term
-- macro_rules
-- | `(we have $type, because $term, $body)
-- => `(have : $type := sorryrm; $body)
-- | `([ $id ] we have $type, because $term, $body)
-- => `(have $id : $type := $term; $body)

-- syntax ("[" ident "]")? "we" "have" term "," "by" tactic "," term : term
-- macro_rules
-- | `(we have $type, by $tactic, $body)
-- => `(have : $type := by { $tactic }; $body)
-- | `([ $id ] we have $type, by $tactic, $body)
-- => `(have $id : $type := by { $tactic }; $body)

-- notation "finally" "we" "have" type "," "because" term =>
--   show type from term

-- notation "letting" arg "be" "arbitrary" "," body => (λ arg => body)

-- notation term "is" "nonempty" => Nonempty term

-- notation term "for every" var => ∀ var, term

-- notation "(" t0 "," t1 ")" "∈" binRel => binRel t0 t1

-- notation term "witnesses" "it" => ⟨term⟩
-- notation term0 "and" term1 "witness" "it" => ⟨term0, term1⟩

-- Any All trees as macros.
-- declare_syntax_cat All
-- declare_syntax_cat Any

-- syntax term : All
-- syntax All "and" All : All

-- syntax term : Any
-- syntax Any "or" Any : Any

-- syntax "it" "is" "witnessed" "by" All : term
-- TODO: Recursively macroexpand via splicing lists of terms
-- Can we unify modulo ACI to re-arrange the parse trees?
-- macro_rules
-- | `(it is witnessed by $term:term)
-- => `(⟨$term⟩)
-- | `(it is witnessed by $t0:term and $t1:term)
-- => `(⟨$t0, $t1⟩)

-- macro "letting" id:ident "be" "as" "in" term:term "," body:term : term
-- => `(
--   let ⟨$id, $term⟩ := $term
--   $body
-- )

theorem choice
  (h : ∀ a, Nonempty <| σ a) : Nonempty <| (a : α) → σ a :=
  let f a :=
    have : Nonempty <| σ a := h a
    Classical.choice this
  show _ from ⟨f⟩

  -- define f as
  --   a ∈ α ↦
  --     [this] we have σ a is nonempty, because h a,
  --     finally we have σ a, because Classical.choice this,
  -- finally we have ((a : α) → σ a) is nonempty, because it is witnessed by f

-- notation "Axiom of Choice" => choice

-- syntax "⋃" : term

/-
  Helper macro for invoking the Axiom of Choice.
  It applies Choice to arg and then pattern matches on the result to extract
  a witnessing choice function.
-/
-- syntax
--   "by" "applying" term "to" term ","
--   -- "we" "obtain" ident ":" term "such" "that" term
--   "we" "obtain" ident "such" "that" term
--   "," term
--   : term
-- macro_rules
-- | `(
--     by applying $fn to $arg,
--     -- we obtain $id : $vartype → ⋃ $type such that
--     we obtain $id such that
--     $id0:ident $var0:ident ∈ $type0 for every $var:ident,
--     $body
--   )
-- =>
  -- TODO:
  -- - Check syntactic equivalence modulo redundant parentheses
  --   and α renaming.
  -- - Better error messages.
  -- if var == var0 ∧ id == id0
  -- then `(let ⟨($id : ($var : _) → $type0)⟩ := $fn $arg; $body)
  -- else `("Incorrect use of Choice macro!")

-- Skolemization
private lemma exists_forall_of_forall_exists {R : α → β → Prop}
  (h : ∀ a, ∃ b, R a b) : ∃ f : _ → _, ∀ a, R a (f a) :=
  let σ a := {b | R a b}
  have : ∀ a, Nonempty <| σ a
    | a =>
      have : ∃ b, R a b := h a
      show Nonempty {b | R a b} from Utils.nonempty_subtype_iff_exists.mpr this
  have : Nonempty <| (a : α) → σ a := choice this

  let f : (a : α) → σ a := Classical.choice this
  have : ∀ a, R a (f a) := (f . |>.prop)
  show ∃ f: _ → _, ∀ a, R a (f a) from ⟨(f .), this⟩

  -- define σ as a ∈ α ↦ {b ∈ β | (a, b) ∈ R},

  -- [this] we have σ a is nonempty for every a,
  -- because letting a be arbitrary,
  --   [this] we have ∃ b, (a, b) ∈ R, because h a,
  --   finally we have {b | (a, b) ∈ R} is nonempty,
  --   because Utils.nonempty_subtype_iff_exists.mpr this,

  -- by applying Axiom of Choice to this,
  -- we obtain f such that f a ∈ σ a for every a,

  -- [h] we have ((a, f a) ∈ R) for every a, because a ↦ f a |>.prop,

  -- finally we have ∃ f : _ → _, ∀ a, (a, f a) ∈ R,
  -- because it is witnessed by a ↦ f a |>.val and h

private lemma forall_exists_of_exists_forall {R : α → β → Prop}
  (h : ∃ f : _ → _, ∀ a, R a (f a)) : ∀ a, ∃ b, R a b :=
  have ⟨f, hf⟩ := h
  λ a ↦
    have : R a <| f a := hf a
    show ∃ b, R a b from ⟨f a, this⟩

  -- letting f be as in h, -- extract witness via existential elimination
  -- letting a be arbitrary,
  --   [this] we have (a, f a) ∈ R, because h a,
  --   finally we have ∃ b, (a, b) ∈ R,
  --   because it is witnessed by f a and this

theorem forall_exists_iff_exists_forall {R : α → β → Prop} :
  (∀ a, ∃ b, R a b) ↔ ∃ f : _ → _, ∀ a, R a (f a)
  where
    mp := exists_forall_of_forall_exists
    mpr := forall_exists_of_exists_forall

  -- it is witnessed by
  --     exists_forall_of_forall_exists
  -- and forall_exists_of_exists_forall

theorem distrib {S : α → β → Set U} :
  ⋂ a, ⋃ b, S a b = ⋃ f : _ → _, ⋂ a, S a (f a) :=
  Set.ext_iff.mpr λ x ↦ calc
        x ∈ ⋂ a, ⋃ b, S a b
      ↔ ∀ a, ∃ b, x ∈ S a b := by simp only [Set.mem_iInter, Set.mem_iUnion]
    _ ↔ ∃ f : _ → _, ∀ a, x ∈ S a (f a) := forall_exists_iff_exists_forall
    _ ↔ x ∈ ⋃ f : _ → _, ⋂ a, S a (f a) := by simp only [Set.mem_iUnion, Set.mem_iInter]

-- #print axioms distrib

end StandardChoice

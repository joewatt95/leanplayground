import Lean
import Leanplayground.MathInLean.Utils.Tactic

namespace Subtype

universe u
variable {α : Type u}

-- instance {φ : α → Prop} : Coe α (Subtype φ) where
--   coe (a : α) := ⟨a, by trivial⟩

syntax "↓" term : term

open Lean Meta System Std Elab Command Expr Term PrettyPrinter Delaborator

elab_rules : term <= expectedType
  | `(↓ $term) => do
    match (← whnfR expectedType).app2? ``Subtype with
    | some (_, pred) =>
      let pred ← delab pred
      elabTerm
        (← `(⟨$term, show $pred $term by aesop⟩))
        (expectedType? := expectedType)
    | _ => throwUnsupportedSyntax

-- #check (↓0 : {x : Nat // x < 3})

end Subtype

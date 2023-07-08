import Lean
import Leanplayground.Natural4.Test

namespace TestSubtyping

open Test
open Lean Meta System Std Elab Command Expr Term PrettyPrinter Delaborator

-- class Subtype (α β : Type)

instance : Coe Loan Agreement where
  coe x := x.toAgreement

§ testPolymorphism
GIVEN agr IS A Agreement
DECIDE testPred OF agr IF True 

#check testPred OF SimpleLoan

structure Class where
  agr : Agreement

def classInstance : Class where
  agr := SimpleLoan

#eval classInstance.agr

structure Class' {α : Type} [Coe α Agreement] where
  agr : α

structure Agreement' extends Agreement

instance : Coe Agreement' Agreement where
  coe x := x.toAgreement

/- Idea:
  Use type aware elaboration rather than simple macroexpansion to first infer
  the type of the fields and then checking for subtype/coe.

  Also see:
  https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297515654
  (this is likely a better approach)

  https://arxiv.org/ftp/arxiv/papers/1902/1902.00548.pdf
-/

-- def classInstance' : @Class' _ _ where
--   agr := SimpleLoan

-- #eval classInstance'.agr

axiom agr' : Agreement'

-- noncomputable def classInstance'' : @Class' _ _ where
--   agr := c

syntax "DEFC" ident term : command

elab_rules : command
|  `(DEFC $id:ident $field) => do
  let fieldTyTerm ← liftTermElabM <| do
    let fieldExpr ← elabTerm (expectedType? := none) field
    -- liftM is implicited inserted here.
    let fieldTyExpr ← inferType fieldExpr
    let fieldTyTerm ← delab fieldTyExpr
    return fieldTyTerm

  trace[Meta.debug] "{fieldTyTerm}"

  elabCommand <| ←
    `(def $id : @Class' $fieldTyTerm _ where
        agr := $field)

-- set_option trace.Meta.debug true in
DEFC x SimpleLoan

#eval x.agr

-- set_option trace.Meta.synthInstance true in
-- @[instance]
-- noncomputable def t : @C Child _ where
--   field := child


-- class Subtype (α β : Type)

-- @[default_instance]
-- instance [Coe α β] : Subtype α β where
--   proj x := ↑x

-- structure Class'' [Subtype a Agreement] where
--   agr : a

-- instance : Subtype Loan Agreement where

-- def classInstance'' : Class'' where
--   agr := SimpleLoan

-- #eval classInstance'.agr

-- end TestSubtyping
import Lean.Data.Json
import Mathlib.Order.BoundedOrder
import Std.Data.HashMap
import Leanplayground.Natural4.Statics

namespace Dynamics

variable
 {Time : Type} [LE Time] [OrderBot Time]
 {Duration : Set Time} [BoundedOrder Duration]
 {Agent : Type}
 {Action : Type}

inductive Deontic where
| O | P | F
deriving Repr, Hashable, Lean.FromJson, Lean.ToJson

structure Norm where
  {deontic : Deontic}
  {deadline : Time}
  {agents : Set Agent}
  {action : Action}

declare_syntax_cat deontic
syntax "MUST" : deontic
syntax "MAY" : deontic
syntax "SHANT" : deontic

syntax
  "RULE" ident
  "PARTY" term
  deontic ("DO")?
  term "BY" term
  : command

macro_rules
| `(RULE $norm:ident PARTY $party:term MUST DO $action BY $deadline)
=> `(
    def $norm : Norm where
      agents := return $party
      action := $action
      deontic := (Deontic.O)
      deadline := $deadline
  )

variable {Borrower : Agent} {pay : Action} {deadline : Deadline}

-- RULE Test
-- PARTY Borrower
-- MUST DO pay BY deadline 

structure Event where

-- structure State where
--   {}

end Dynamics
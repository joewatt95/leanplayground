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
  {cond : Prop}

declare_syntax_cat deontic
syntax "MUST" : deontic
syntax "MAY" : deontic
syntax "SHANT" : deontic

syntax
  "RULE" ident
  "PARTY" term
  "IF" term
  deontic ("DO")?
  term "BY" term
  : command

macro_rules
| `(RULE $norm:ident PARTY $party:term IF $cond MUST DO $action BY $deadline)
=> `(
    noncomputable def $norm : @Norm Time Agent Action where
      agents := return $party
      action := $action
      deontic := (Deontic.O)
      deadline := $deadline
      cond := $cond
  )
  
variable
  {Borrower Lender : Agent}
  {pay : Action}
  {deadline : Time}

RULE Test
PARTY Borrower
IF ∃ x, (x EQUALS 0) AND x EQUALS x
MUST DO pay BY deadline 

RULE Test1
PARTY Lender
IF True
MUST DO pay BY deadline

-- #print Test

structure Event where

-- structure State where
--   {}

end Dynamics
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

DECLARE Deontic IS MUST PLUS MAY PLUS SHANT

DECLARE Norm
HAS deontic IS A Deontic
HAS deadline IS A Time
HAS agents IS A Set OF Agent
HAS action IS A Action
HAS cond IS A Prop

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
      deontic := (Deontic.MUST)
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
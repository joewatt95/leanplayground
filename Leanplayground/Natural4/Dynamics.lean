import Lean.Data.Json
import Mathlib.Order.BoundedOrder
import Std.Data.HashMap
import Leanplayground.Natural4.Statics

namespace Dynamics

variable
  -- TODO: Add a typeclass constraint forcing ≤ to be decidable.
 {Time : Type u} [LE Time] [OrderBot Time]
 {Duration : Set Time} [BoundedOrder Duration]
 {Agent : Type v}
 {Action : Type w}

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
  "§" ident
  "PARTY" term
  "IF" term
  deontic ("DO")?
  term "BY" term
  : command

macro_rules
| `(§ $norm:ident PARTY $party:term IF $cond MUST DO $action BY $deadline)
=>`(§ $norm:ident PARTY $party:term IF $cond MUST $action BY $deadline)

| `(§ $norm:ident PARTY $party:term IF $cond MUST $action BY $deadline)
=> `(
  DEFINE $norm IS A @Norm Time Agent Action
  HAS pure ($party) IS THE agents
  HAS ($action) IS THE action
  HAS Deontic.MUST IS THE deontic
  HAS ($deadline) IS THE deadline
  HAS ($cond) IS THE cond
)
  --   noncomputable def $norm : @Norm Time Agent Action where
  --     agents := return $party
  --     action := $action
  --     deontic := (Deontic.MUST)
  --     deadline := $deadline
  --     cond := $cond
  -- )
  
variable
  {borrower lender : Agent}
  {pay : Action}
  {deadline : Time}

§ Test
PARTY borrower
IF ∃ x, (x EQUALS 0) AND x EQUALS x
MUST DO pay BY deadline 

§ Test'
PARTY lender
IF True
MUST pay BY deadline

-- #print Test

DECLARE Event
-- Preconds that need to hold for the event to be able to fire.
HAS preconds IS A Set OF Prop
-- Postconds is a set of positive and negative fact literals that tell us what
-- holds after the event fires.
-- Positive literals indicate facts that hold.
-- Negative literals indicate facts that no longer hold.
HAS postconds IS A Set OF Prop

DECLARE ActionEvent IS A Event
HAS agent IS A Agent
HAS action IS A Action

macro
  "EVENT"
  "{" preconds:term "}"
  eventName:ident
  "{" postconds:term "}"
  : command
=> `(
  DEFINE $eventName IS A Event
  HAS ($preconds) IS THE preconds
  HAS ($postconds) IS THE postconds
)

macro
  "EVENT"
  "{" preconds:term "}"
  eventName:ident "(" agent:term "DOES" action:term ")"
  "{" postconds:term "}"
  : command
=> `(
  DEFINE $eventName IS A @ActionEvent Agent Action
  HAS ($preconds) IS THE preconds
  HAS ($postconds) IS THE postconds
  HAS ($agent) IS THE agent
  HAS ($action) IS THE action
)

EVENT { pure True } testEvent { pure True }

EVENT { pure True } testActionEvent (borrower DOES pay) { pure True }

-- structure State where
--   {}

end Dynamics
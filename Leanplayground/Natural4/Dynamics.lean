import Lean.Data.Json
import Mathlib.Data.Set.Functor
-- import Mathlib.Order.BoundedOrder
import Std.Data.HashMap
import Leanplayground.Natural4.Statics

namespace Dynamics

-- variable {Time : Type} -- [LinearOrder Time] [BoundedOrder Time]

DECLARE Deontic IS MUST OR MAY OR SHANT

DECLARE Party

-- structure Action where
--   pre : Set Prop
--   post : Set Prop

-- DECLARE Time

DECLARE Duration

structure Event where
-- Preconds that need to hold for the event to be able to fire.
  preconds : Set Prop
-- Postconds is a set of positive and negative fact literals that tell us what
-- holds after the event fires.
-- Positive literals indicate facts that hold.
-- Negative literals indicate facts that no longer hold.
  postconds : Set Prop

structure Norm where
  cond : Prop
  deontic : Deontic
  deadline : ℕ
  agent : Party
  action : Event

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
  @[regulative]
  def $norm : Norm where
    agent := $party
    action := $action
    deontic := Deontic.MUST
    deadline := $deadline
    cond := $cond
)

structure ActionEvent extends Event where
  agent : Party
  action : Action

macro
  "EVENT"
  "{" preconds:term "}"
  eventName:ident
  "{" postconds:term "}"
  : command
=> `(
  DEFINE $eventName IS A Event
  HAS ($preconds) IS THE preconds
      ($postconds) IS THE postconds
)

macro
  "EVENT"
  "{" preconds:term "}"
  eventName:ident "(" agent:term "DOES" action:term ")"
  "{" postconds:term "}"
  : command
=> `(
  DEFINE $eventName IS A ActionEvent
  HAS ($preconds) IS THE preconds
      ($postconds) IS THE postconds
      ($agent) IS THE agent
      ($action) IS THE action
)

-- structure State where
--   {}

end Dynamics

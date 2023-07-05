import Lean.Data.Json
import Mathlib.Data.Set.Functor
import Mathlib.Order.BoundedOrder
import Std.Data.HashMap
import Leanplayground.Natural4.Statics

namespace Dynamics

-- variable
--   -- TODO: Add a typeclass constraint forcing ≤ to be decidable.
--   {Time : Type} [LE Time] [OrderBot Time]
--   {Duration : Type} [LE Duration] [Monoid Duration] [BoundedOrder Duration]

DECLARE Deontic IS MUST OR MAY OR SHANT

DECLARE Agent

DECLARE Action
HAS pre IS A Set OF Prop
    post IS A Set OF Prop

DECLARE Time

DECLARE Duration

DECLARE Norm
HAS cond IS A Prop
    deontic IS A Deontic
    deadline IS A Time
    agent IS A Agent
    action IS A Action

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
  DEFINE $norm IS A Norm -- Time Agent Action
  HAS ($party) IS THE agent
      ($action) IS THE action
      Deontic.MUST IS THE deontic
      ($deadline) IS THE deadline
      ($cond) IS THE cond
)
  --   noncomputable def $norm : @Norm Time Agent Action where
  --     agents := return $party
  --     action := $action
  --     deontic := (Deontic.MUST)
  --     deadline := $deadline
  --     cond := $cond
  -- )

-- #print Test

DECLARE Event
-- Preconds that need to hold for the event to be able to fire.
HAS preconds IS A Set OF Prop
-- Postconds is a set of positive and negative fact literals that tell us what
-- holds after the event fires.
-- Positive literals indicate facts that hold.
-- Negative literals indicate facts that no longer hold.
    postconds IS A Set OF Prop

DECLARE ActionEvent IS A Event
HAS agent IS A Agent
    action IS A Action

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
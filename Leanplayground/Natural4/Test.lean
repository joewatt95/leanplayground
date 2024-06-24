import Lean
import Mathlib.Algebra.BigOperators.Group.List

import Leanplayground.Natural4.Attrs
import Leanplayground.Natural4.Commands
import Leanplayground.Natural4.Dynamics

-- import LeanCopilot

-- import Smt

namespace Test

-- variable
--   {Time : Type} [LinearOrder Time] [BoundedOrder Time]
--   (deadline : Time)
-- set_option smt.solver.kind "z3"

-- Uncomment the next 2 lines to trace debug macroexpansion.
-- set_option trace.Elab.command true
-- set_option trace.Elab.step true

DECLARE Agreement

DECLARE Role IS Borrower OR Lender

DECLARE Party IS A Dynamics.Party
HAS role IS A Role
    bankBalance IS A Int

DECLARE Loan IS A Agreement
HAS Parties IS A MAP FROM Role TO Party
    PrincipalAmt IS A Nat

DEFINE B IS A Party
HAS .Borrower IS THE role
    100 IS THE bankBalance

DEFINE L IS A Party
HAS Role.Lender IS THE role
    0 IS THE bankBalance

DEFINE SimpleLoan IS A Loan
HAS #[(Role.Borrower, B), (Role.Lender, L)] IS THE Parties
    1000 IS THE PrincipalAmt

§ testRule
GIVEN
  p1 IS A Party
  n IS A Int
  p2 IS A Party
DECIDE canTransfer OF p1, n, p2
IF
  let p1NEp2 := p1 ≠ p2
  (p1.bankBalance ≥ n) AND p1NEp2

-- DECIDE isLender IF (Party.role OF p) EQUALS Role.Lender

EVENT { {} } pay { {} }

-- EVENT { {True} } payPayment (B.toParty DOES pay) { {True} }

-- § Test
-- TODO: Automatically insert a coercion here.
-- PARTY B.toParty
-- IF ∃ x, (x EQUALS 0) AND x EQUALS x
-- MUST DO pay BY 10

-- axiom deadline : Time

-- § testRegulative
-- PARTY lender
-- IF THERE IS SOME xs : List OF Int SUCH THAT xs.sum EQUALS 0
-- MUST DO pay BY deadline

-- EVENT { pure True } testEvent { pure True }

-- EVENT { pure True } testActionEvent (borrower DOES pay) { pure True }

§ goodRule1
GIVEN n IS A Int
DECIDE n < 0 IF THERE IS SOME m SUCH THAT (0 < m) AND (m + n = 0)

§ goodRule2
GIVEN xs IS A List OF ℤ
DECIDE xs.foldl (. * .) 1 EQUALS Id.run do
  let mut result := 1
  for x in xs do
    result := x * result
  return result
IF True

example : goodRule2 := by
  unfold goodRule2
  intro xs
  induction xs with
  | nil =>
    aesop
  | cons x xs ih =>
    simp [*] at *
    sorry

-- #TEST goodRule2

§ badRule1
GIVEN
  m IS A Int
  n IS A Int
DECIDE m < n
IF True

-- set_option trace.smt.solve true in
-- set_option trace.smt.translate.expr true in
-- #SMT badRule1

§ badRule2
GIVEN xs IS A List OF Int
DECIDE xs.sum EQUALS xs.foldl (. * .) 0
IF True

-- #TEST badRule2

section
variable {α β : Type}

§ skolemize
GIVEN R IS A RELATION BETWEEN α AND β
DECIDE THERE IS SOME f FROM _ TO _ SUCH THAT FOR EVERY a, R RELATES a TO f a
IF FOR EVERY a, THERE IS SOME b SUCH THAT R RELATES a TO b

-- #print skolemize
end

DECLARE ClaimType
IS Accident
OR Illness

DECLARE HighRiskActivities

DECLARE AccidentForm

DECLARE IllnessForm

def WebForm : Type :=
  Σ claimType : ClaimType,
    match claimType with
    | .Accident => AccidentForm
    | .Illness => IllnessForm
    -- if _ : claimType == ClaimType.Accident
    -- then AccidentForm
    -- else
    --   have : claimType == ClaimType.Illness := by cases claimType; repeat aesop
    --   IllnessForm

-- #reduce WebForm

-- open Cardinal

-- universe u

-- § InaccessibleCardinal'
-- GIVEN κ IS A Cardinal.{u}
-- DECIDE IsInaccessible' OF κ
-- IF (κ > ℵ₀) AND (Cardinal.IsRegular κ) AND IsStrongLimit κ

-- set_option trace.aesop.ruleSet true in
-- example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by aesop

open Lean Lean.Meta in
def test : MetaM Unit := do
  let declsSize := (← read).lctx.decls.size
  trace[Meta.debug] "Size of decls: {declsSize}"

  let testRule := `Test.testRule
  match (← getEnv).find? testRule with
  | some <| ConstantInfo.defnInfo {value, ..} =>
    try
      let ty ← inferType value
      trace[Meta.debug] s!"{ty}"
    catch _ => return
  | _ => return

-- set_option trace.Meta.debug true
-- #eval Attrs.listAll constitutive

end Test

import Lean
import Leanplayground.Natural4.Attrs
import Leanplayground.Natural4.Commands
import Leanplayground.Natural4.Dynamics

namespace Test

set_option smt.solver.kind "z3"

-- Uncomment the next 2 lines to trace debug macroexpansion.
-- set_option trace.Elab.command true
-- set_option trace.Elab.step true

DECLARE Agreement

DECLARE Role IS Borrower OR Lender

DECLARE Party
HAS role IS A Role
    bankBalance IS A Int

DECLARE Loan IS A Agreement
HAS Parties IS A MAP FROM Role TO Party
    PrincipalAmt IS A Nat

DEFINE B IS A Party
HAS Role.Borrower IS THE role
    100 IS THE bankBalance

DEFINE L IS A Party
HAS Role.Lender IS THE role
    0 IS THE bankBalance

DEFINE SimpleLoan IS A Loan
HAS #[(Role.Borrower, B), (Role.Lender, L)] IS THE Parties
    1000 IS THE PrincipalAmt

-- #eval Lean.toJson SimpleLoan

-- DECIDE isLender IF (Party.role OF p) EQUALS Role.Lender

-- § Test
-- PARTY Agent.borrower
-- IF ∃ x, (x EQUALS 0) AND x EQUALS x
-- MUST DO Action.pay BY 0

§ testRule
GIVEN
  p1 IS A Party
  n IS A Int
  p2 IS A Party
DECIDE canTransfer OF p1, n, p2
IF
  letI p1NEp2 := p1 ≠ p2
  (p1.bankBalance ≥ n) AND p1NEp2

DEFINE borrower IS A Dynamics.Agent
DEFINE lender IS A Dynamics.Agent

DEFINE pay IS A Dynamics.Action
HAS pure True IS THE pre
    pure True IS THE post

DEFINE deadline IS A Dynamics.Time

§ testRegulative
PARTY lender
IF THERE IS SOME xs : List OF Int SUCH THAT xs.sum EQUALS 0
MUST pay BY deadline

EVENT { pure True } testEvent { pure True }

EVENT { pure True } testActionEvent (borrower DOES pay) { pure True }

§ goodRule
GIVEN n IS A Int
DECIDE n < 0 IF THERE IS SOME m SUCH THAT (0 < m) AND (m + n = 0)

-- #SMT goodRule

§ badRule1
GIVEN
  m IS A Int
  n IS A Int
DECIDE m < n IF True

-- #print badRule1

-- #SMT badRule1

§ badRule2
GIVEN xs IS A List OF Int
DECIDE xs.sum EQUALS 0 IF 0 EQUALS
  Id.run do
    let mut result := 1
    for x in xs do
      result := x * result
    return result

-- #print badRule2

-- #TEST badRule2

section
variable {α β : Type}

§ skolemize
GIVEN R IS A RELATION BETWEEN α AND β
DECIDE THERE IS SOME f FROM _ TO _ SUCH THAT FOR EVERY a, R RELATES a TO f a
IF FOR EVERY a, THERE IS SOME b SUCH THAT R RELATES a TO b

-- #print skolemize
end

open Cardinal

universe u

§ InaccessibleCardinal'
GIVEN κ IS A Cardinal.{u}
DECIDE IsInaccessible' OF κ
IF (κ > ℵ₀) AND (Cardinal.IsRegular κ) AND IsStrongLimit κ

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
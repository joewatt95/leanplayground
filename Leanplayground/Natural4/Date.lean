import Auto.Tactic
import Duper
-- import LeanCopilot
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Date

abbrev Date :=
  {(year, month, day) | is_valid_date year month day}
where
  @[reducible]
  is_valid_date year month day :=
    1 ≤ month ∧ month ≤ 12 ∧
    1 ≤ day ∧ day ≤ 31 ∧

    (month ∈ [4, 6, 9, 11] → day ≤ 30) ∧

    (month = 2 → day ≤ 29) ∧
    (month = 2 ∧ day = 29 → is_leap_year year)

  @[reducible]
  is_leap_year year := year % 400 = 0 ∨ (year % 4 = 0 ∧ year % 100 ≠ 0)

inductive Period
  | Days | Weeks | Months | Years
deriving BEq, Ord, Hashable, Repr

structure Duration where
  num : ℤ
  period : Period
deriving BEq, Ord, Hashable, Repr

declare_syntax_cat period
declare_syntax_cat duration
declare_syntax_cat before_after

syntax "DAYS" : period
syntax "WEEKS" : period
syntax "MONTHS" : period
syntax "YEARS" : period

syntax term period : term
macro_rules
| `($num DAYS) => `((⟨$num, Period.Days⟩ : Duration))
| `($num WEEKS) => `((⟨$num, Period.Weeks⟩ : Duration))
| `($num MONTHS) => `((⟨$num, Period.Months⟩ : Duration))
| `($num YEARS) => `((⟨$num, Period.Years⟩ : Duration))

syntax "BEFORE" : before_after
syntax "AFTER" : before_after

-- instance [Repr α] : ToString α := ⟨reprStr⟩

inductive BeforeAfter
  | Before | After
deriving BEq, Ord, Hashable, Repr

structure BeforeAfterDate where
  beforeAfter : BeforeAfter
  duration : Duration
  date : Date
deriving BEq, Hashable, Repr

infix:65 "BEFORE" => BeforeAfterDate.mk BeforeAfter.Before
infix:65 "AFTER" => BeforeAfterDate.mk BeforeAfter.After

set_option auto.smt true
set_option auto.smt.trust true
-- set_option auto.smt.solver.name "z3"

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

-- #configure_llm_aesop

syntax "date" "{" term  "}": term
macro_rules
| `(date { $year - $month - $day }) =>
  `((⟨($year, $month, $day), by
      simp[Date.is_valid_date, Date.is_leap_year]
      repeat (first| omega | duper | auto)⟩
    : Date))

-- #check 3 DAYS AFTER date { 2024 - 2 - 29 }
-- #check 10 YEARS BEFORE date { 2022 - 2 - 29 }

example
  (_ : 1 ≤ month ∧ month ≤ 12)
  (_ : 1 ≤ day ∧ day ≤ 28)
  : Date.is_valid_date year month day := by
  omega

end Date

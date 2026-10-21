/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Leanplayground.Util.SOS.Certificate
public import Leanplayground.Util.SOS.Raw
public import Leanplayground.Util.SOS.Polynomial
public import Leanplayground.Util.SOS.Reify
public import Leanplayground.Util.SOS.Lift
public import Leanplayground.Util.SOS.Verifier
public import Leanplayground.Util.SOS.Tactic

/-!
# Sum-of-squares automation

Mathlib-facing soundness proofs and tactic elaboration for the `sos` tactic.

The proof-producing frontend lives in Mathlib. The computational engine is
provided by the external `sos` package, whose modules do not import Mathlib.

## Trust boundary

The native CSDP solver is a search oracle: it proposes floating-point Gram
matrices, which the engine rationalizes into exact certificates. Mathlib then
checks the certificate identity with kernel reduction and applies the
soundness theorems in `Mathlib.Tactic.SOS.Verifier`; neither certificate
checking nor proof replay uses `native_decide`. The committed axiom audit in
`MathlibTest.Tactic.SOS.Axioms` guards the principal soundness theorems.

This separation removes CSDP's numerical algorithm from the *logical* trusted
base: an incorrect solver answer is rejected rather than proving a false
statement. It does not make arbitrary native code process-safe. The CSDP FFI
runs inside the Lean process while a proof is elaborated, so its native memory
safety and the integrity of its distributed binaries remain part of the
ordinary software and host-security trusted base.
-/

/-! ## This copy

A temporary port of the tactic from Mathlib PR #42336, taken at `e4f24b8461` on its branch,
the last commit there on the 4.34 line. The eight files are the PR's own, verbatim apart from
their imports, which are moved off the `Mathlib.` module path so that this copy and Mathlib's
cannot clash once the PR merges. Each also gains a `set_option doc.verso false` after its
imports, keeping the PR's Markdown docstrings out of the Verso docstrings the lakefile sets for
the rest of the package. Declarations keep their `Mathlib.Tactic.SOS` namespace, which keeps a
diff against upstream trivial.

The engine is `leanprover/sos` at `v0.2.4`, the release that commit pins.

To retire it, delete `Leanplayground/Util/SOS/` and this file, drop the `sos` requirement from
`lakefile.lean`, and import `Mathlib.Tactic.SOS` in `Leanplayground/Util/Tactic.lean` instead.

## It can crash, and a crash is not unsoundness

On some goals the tactic takes the Lean process down, exiting with code 206 and no message,
where it should report a failure. That stops elaboration and nothing more. Every certificate
is checked by the kernel, so a crash cannot let a false statement through.

Checked on this port under Lean 4.34.0, 2026-09-23. Each of these crashes:

```
example (x : ℝ) : 0 ≤ x := by sos
example (x : ℝ) : x > 0 := by sos
example (x : ℝ) : x < 0 := by sos
example (x : ℝ) : 0 ≤ x ^ 3 := by sos
```

Each of these fails cleanly instead, reporting that the search found no certificate:

```
example (x : ℝ) : 0 ≤ x ^ 2 - 1 := by sos
example (x : ℝ) (h : 0 ≤ x) : x ≤ 0 := by sos
example (x y : ℝ) : 0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by sos
```

The crashes seen so far are unprovable goals with no hypotheses and an odd-degree
polynomial, while an even degree or a hypothesis gives a clean failure. The last example
above is the Motzkin polynomial, which is nonnegative but not a sum of squares. Every true
goal tried on this port was proved. Crashes on harder true goals were seen under the 4.33
build of the tactic and have not been reproduced here.

The practical consequence is small, since a linear goal is `linarith`'s before it is this
tactic's. A crash costs the file's Lean process, which the editor restarts. -/

#!/usr/bin/env python3
"""Calibration for the `laundering` guard in `check.py`, asserted in both directions
with no slack.

The two failure modes differ in consequence and both are fatal to the tool:

  FALSE NEGATIVE -- a planted laundering pattern goes unreported.  The report then reads
                    as "this corpus is clean", the one claim it cannot support.
  FALSE POSITIVE -- ordinary mathematics is reported as laundering.  Readers learn to
                    skim, and the real findings go with the noise.

So this asserts EXACT SETS, not containment:

  POSITIVE  every planted pattern is reported, AND under the right family.  A pattern
            reported under the wrong family is a failure: family fixes severity, and
            severity decides whether the build stops.
  NEGATIVE  clean mathematics produces NO finding at FATAL or CONDITIONAL severity.
            FIDELITY findings are a ledger rather than an accusation and are allowed --
            a side condition is correctly reported as F16s and correctly does not gate.

Every negative below is a trap this detector actually failed, or would fail under an
obvious simplification of its rules:

  * `h s` is modus ponens, not a restated hypothesis.
  * a contrapositive applies a premise to a theorem the corpus proves.
  * a witnessed model class is not an unbuilt certificate.
  * a witness may take DATA parameters and still be a witness.
  * a Prop-valued structure can be witnessed by a THEOREM rather than a term.
  * `(h : 0 < rate)` on a free real is a side condition, and deleting it makes the
    statement FALSE.  It must stay out of the laundering family even though `rate` is
    also a structure field name in the same file -- the bug that made this test
    necessary reported ~4x more laundering than exists.
  * a premise may bind a variable whose name collides with a corpus definition.

Run:  python3 proofs/validation/code/test_check.py
"""
import subprocess
import sys
import tempfile
from pathlib import Path

# test_check.py sits beside check.py at proofs/validation/code/.
CHECK = Path(__file__).resolve().parent / "check.py"

# --------------------------------------------------------------------------------------
# Planted laundering.  Each block is labelled with the family it MUST be reported as.
# --------------------------------------------------------------------------------------

POSITIVE = r"""
import Mathlib

namespace Fixture

def FamousConjecture : Prop := ∀ n : ℕ, n = n
def portabilityDecay (x : ℝ) : ℝ := x

-- F1: the conclusion IS the hypothesis.
theorem famous_conjecture (h : FamousConjecture) : FamousConjecture := h

-- F1b: the whole proof is the bare premise.
theorem decay_bare (h : portabilityDecay 1 = 1) : portabilityDecay 1 = 1 := h

-- F2: a Prop named like a theorem, with nothing proving it.
def ClassificationTheorem : Prop := ∀ n : ℕ, 0 ≤ n

-- F4: a certificate carrying the mathematics, consumed and never constructed.
structure ConstructionSetup where
  object : ℕ
  propertyA : 0 < object
  finalHardIdentity : object * object = object

theorem main_result (s : ConstructionSetup) : ∃ x : ℕ, 0 < x :=
  ⟨s.object, s.propertyA⟩

-- F4 again, in its purest form: the theorem IS the field, renamed.
theorem setup_object_pos (s : ConstructionSetup) : 0 < s.object :=
  s.propertyA

-- F8: the target property weakened to nothing.
def IsSecure (system : ℕ) : Prop := True

-- F11: a class whose field is `False`.
class MagicalStructure where
  contradiction : False

-- F16: a premise CLOSED under the theorem's binders -- it constrains nothing the
-- theorem quantifies over, so it is not a restriction; it is a fact about this corpus's
-- own definition, handed in rather than proved.
theorem decay_bound (h : ∀ y : ℝ, portabilityDecay y ≤ 1) (x : ℝ) :
    portabilityDecay x ≤ 2 := by
  have := h x; linarith

-- F21: the conclusion divides by `d`, which no premise shows is nonzero.  At `d = 0`
-- Lean makes the quotient `0` and the claim is silently true.
theorem ratio_nonneg (x d : ℝ) (hx : 0 ≤ x) : 0 ≤ x / d := by positivity

-- F24: a custom axiom.
axiom deepResult : ∀ n : ℕ, n = n

end Fixture
"""

POSITIVE_EXPECTED = {"F1", "F1b", "F2", "F4", "F8", "F11", "F16", "F21", "F24"}

# --------------------------------------------------------------------------------------
# Clean mathematics that superficially resembles each of the above.
# --------------------------------------------------------------------------------------

NEGATIVE = r"""
import Mathlib

namespace Clean

/-- A model class WITH a witness: not an unbuilt certificate. -/
structure Model where
  rate : ℝ
  rate_pos : 0 < rate

def Model.witness : Model where
  rate := 1
  rate_pos := by norm_num

theorem Model.rate_ne_zero (m : Model) : m.rate ≠ 0 := ne_of_gt m.rate_pos

/-- A witness may take DATA parameters and still inhabit the class. -/
structure Panel (n : ℕ) where
  mass : Fin n → ℝ
  mass_nonneg : ∀ j, 0 ≤ mass j

def Panel.witness (n : ℕ) : Panel n where
  mass := fun _ => 0
  mass_nonneg := fun _ => le_refl 0

theorem Panel.mass_sum_nonneg {n : ℕ} (p : Panel n) (i j : Fin n) :
    0 ≤ p.mass i + p.mass j :=
  add_nonneg (p.mass_nonneg i) (p.mass_nonneg j)

/-- A Prop-valued structure witnessed by a THEOREM rather than a term. -/
structure IsBudget (k : ℝ) (M : ℝ) : Prop where
  lower : 0 ≤ M
  upper : M ≤ k

theorem IsBudget.witness : IsBudget 1 0 where
  lower := le_refl 0
  upper := by norm_num

/-- Definitional unfolding at a point: `h s` is modus ponens, not laundering. -/
def Even' (f : ℤ → ℝ) : Prop := ∀ s, f (-s) = f s

theorem even_blind (f : ℤ → ℝ) (h : Even' f) (s : ℤ) : f (-s) = f s := h s

/-- A contrapositive: applies a premise to a theorem this file proves. -/
theorem double_lt (x y : ℝ) (h : x < y) : 2 * x < 2 * y := by linarith

theorem not_double_lt (x y : ℝ) (h : ¬ (2 * x < 2 * y)) : ¬ (x < y) :=
  fun hxy => h (double_lt x y hxy)

/-- A side condition on a free real.  `rate` is also a FIELD name above, and a premise
mentioning it must still not be classed as an assumed fact about the corpus. -/
theorem inv_rate_pos (rate : ℝ) (h : 0 < rate) : 0 < 1 / rate := by positivity

/-- A DEFINITION dividing by its own parameter is not a defect: a definition takes no
premises, so there is nothing for it to have guarded. -/
def share (part total : ℝ) : ℝ := part / total

/-- A theorem whose denominator IS guarded. -/
theorem share_nonneg (part total : ℝ) (hp : 0 ≤ part) (ht : 0 < total) :
    0 ≤ share part total := by
  unfold share; positivity

/-- A premise binding a variable whose name collides with a corpus definition. -/
theorem forall_even (f : ℤ → ℝ) (h : ∀ Even' : ℤ, f Even' = 0) : f 0 = 0 := h 0

/-- A side condition whose constrained binder is a GREEK letter.  Lean identifiers are
not ASCII, and an ASCII-only identifier class cannot see that this premise constrains
`β` — it then reads as a fact handed in about `variance`, which it is not. -/
def variance (β : ℤ → ℝ) : ℝ := β 0

theorem variance_ne_zero (β : ℤ → ℝ) (τ : ℝ) (h : 0 < variance β) (hτ : 0 < τ) :
    variance β ≠ 0 := ne_of_gt h

end Clean
"""


def run(src: str, *args: str) -> str:
    with tempfile.TemporaryDirectory() as td:
        f = Path(td) / "Fixture.lean"
        f.write_text(src)
        r = subprocess.run(
            [sys.executable, str(CHECK), "--only", "laundering", str(f), *args],
            capture_output=True, text=True)
        return r.stdout + r.stderr


def families(out: str) -> set[str]:
    return {l.strip().split()[1] for l in out.splitlines() if l.strip().startswith("=== F")}


def main() -> int:
    failures: list[str] = []

    # False negatives, and misfiling -- which is a false negative at the severity that
    # matters, since a FATAL pattern reported as FIDELITY does not stop the build.
    got = families(run(POSITIVE, "--severity", "conditional"))
    for missing in sorted(POSITIVE_EXPECTED - got):
        failures.append(f"FALSE NEGATIVE  {missing} planted but not reported")
    for extra in sorted(got - POSITIVE_EXPECTED):
        failures.append(f"MISFILED        {extra} reported but not planted")

    # False positives: clean mathematics must never gate the build.
    for bad in sorted(families(run(NEGATIVE, "--severity", "conditional"))):
        failures.append(f"FALSE POSITIVE  {bad} reported on clean mathematics")

    for f in failures:
        print(f"FAIL  {f}")
    if failures:
        print(f"\n{len(failures)} calibration failure(s).  Until these pass the "
              f"detector's report is not evidence, in either direction.")
        return 1
    print("laundering-guard calibration PASSED")
    print(f"  {len(POSITIVE_EXPECTED)} planted patterns, each reported in the right family")
    print("  0 findings at FATAL or CONDITIONAL severity on clean mathematics")
    return 0


if __name__ == "__main__":
    sys.exit(main())

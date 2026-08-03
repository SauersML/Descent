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
import json
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

-- F22: the noun does all the work -- the structure's field IS the conclusion.
-- Witnessed on purpose: an UNwitnessed certificate is F4, and F4 would mask this.
-- The defect here is not that nothing inhabits the class; it is that the class is
-- defined to already satisfy the theorem.
structure GoodAction where
  act : ℕ
  fixedPoint : ∃ x : ℕ, x = act

def GoodAction.witness : GoodAction where
  act := 0
  fixedPoint := ⟨0, rfl⟩

theorem every_good_action_has_fixed_point (a : GoodAction) : ∃ x : ℕ, x = a.act :=
  a.fixedPoint

-- F3: an assumption wearing instance syntax.
theorem needs_fact [Fact (1 < 2)] : True := trivial

-- F5: an existential conclusion repackaging an existential premise.
theorem exists_nonneg (h : ∃ n : ℕ, 0 < n) : ∃ m : ℕ, 0 ≤ m := by
  obtain ⟨n, hn⟩ := h; exact ⟨n, Nat.zero_le n⟩

-- F6: choice applied to an ASSUMED existence premise. The gap is `h`, not `choose`.
theorem choose_pos (h : ∃ n : ℕ, 0 < n) : 0 < Classical.choose h :=
  Classical.choose_spec h

-- F7: the advertised conclusion is a conjunct of the predicate's own definition.
def isCalibrated (x : ℕ) : Prop := x = 0
def ValidSetup (x : ℕ) : Prop := 0 ≤ x ∧ isCalibrated x

-- F9: premise and conclusion are the same existential, up to renaming.
theorem solve_it (h : ∃ s : ℕ, s = 1) : ∃ t : ℕ, t = 1 := h

-- F10: quantified over the empty type, so it says nothing.
theorem all_empty_good (x : Empty) : False := nomatch x

-- F12: the domain is defined to consist of objects already satisfying the property.
theorem sub_pos (x : {n : ℕ // 0 < n}) : 0 < x.val := x.property

-- F13: a range advertised as the canonical object, with no isomorphism proved.
/-- The canonical construction of the object. -/
def constructedObject : Set ℕ := Set.range (fun n : ℕ => n + 1)

-- F19: a Prop premise hidden in an implicit binder.
theorem hidden_premise {h : (1 : ℕ) = 1} : True := trivial

-- F20: a standard name redefined locally to mean something else.
def IsCompact (s : Set ℕ) : Prop := s = ∅

-- F23: existence proved by wrapping a parameter that was handed in.
structure Carrier where
  val : ℕ

theorem carrier_nonempty (w : Carrier) : Nonempty Carrier := ⟨w⟩

-- F15: prose asserts a bridge between two definitions; no theorem states it.
def compressor : ℕ := 2

/-- The map that `compressor` induces on the index. -/
def compressionMap : ℕ → ℕ := fun n => n + 2

-- F18: `#print axioms` aimed at a Prop DEFINITION rather than at a proof of it.
#print axioms FamousConjecture

-- F24: a custom axiom.
axiom deepResult : ∀ n : ℕ, n = n

end Fixture
"""

# The EXACT set the positive fixture produces at every severity.  Two entries are
# incidental to the planted patterns and are correct: `famous_conjecture` carries a
# premise under a name claiming a conjecture (F17), and `ratio_nonneg` has an honest
# side condition alongside its unguarded denominator (F16s).
POSITIVE_EXPECTED = {"F1", "F1b", "F2", "F3", "F4", "F5", "F6", "F7", "F8", "F9",
                     "F10", "F11", "F12", "F13", "F15", "F16", "F16s", "F17", "F18",
                     "F19", "F20", "F21", "F22", "F23", "F24"}

# --------------------------------------------------------------------------------------
# Clean mathematics that superficially resembles each of the above.
# --------------------------------------------------------------------------------------

NEGATIVE = r"""
import Mathlib

namespace Clean

-- A locally proved instance discharges an obligation; it does not hide one in a parameter.
theorem local_instance_is_proof_plumbing : True := by
  letI : Fact True := ⟨trivial⟩
  trivial

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


# ======================================================================================
# Calibration for the other six guards
# ======================================================================================
#
# WHY THIS EXISTS.  Until now only the laundering guard had a control.  The other
# six were run in CI, reported clean, and that clean report was treated as
# evidence -- which it was not, because nothing had ever shown they could fail.
#
# The cost was paid before this was written.  A refactor rewrote the word
# `declarations` inside the wiring guard's own JSON keys and printed label,
# changing a machine-readable contract that `--json` consumers parse.  Every
# guard passed.  CI passed.  It was found by reading output by eye.
#
# Each guard below gets BOTH directions, because they fail differently and only
# one of the two is visible in ordinary use:
#
#   POSITIVE  a planted defect IS reported.  Without this a guard that silently
#             stopped matching -- a regex that no longer fires, a root that
#             resolves to an empty tree -- is indistinguishable from a clean
#             corpus, and reports success forever.
#   NEGATIVE  clean input is NOT reported.  Without this a guard can be "fixed"
#             into firing on everything, which trains readers to ignore it, and
#             an ignored guard is the same as a deleted one.
#
# The fixtures are a whole miniature corpus under GNOMON_CORPUS, not the real
# one, so a control cannot be broken by ordinary corpus edits and cannot be made
# to pass by changing the corpus.

HEADER = """/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Fixture -/
"""


def write_corpus(root: Path, files: dict) -> None:
    """Materialise a fixture corpus: `root` plays the part of `proofs/`."""
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def run_guard(guard: str, files: dict, *args: str):
    """Run one guard against a fixture corpus. Returns (exit code, output)."""
    import os
    with tempfile.TemporaryDirectory() as td:
        corpus = Path(td) / "proofs"
        corpus.mkdir()
        write_corpus(corpus, files)
        env = dict(os.environ, GNOMON_CORPUS=str(corpus))
        r = subprocess.run(
            [sys.executable, str(CHECK), "--only", guard, *args],
            capture_output=True, text=True, env=env)
        return r.returncode, r.stdout + r.stderr


# A minimal corpus every guard is willing to call clean: license header, module
# docstring, short lines, one imported module, no forbidden shapes.
CLEAN_ROOT = HEADER + """
import Calibrator.Sub

namespace Calibrator

/-- A definition with a declared status. -/
noncomputable def cleanRate (x : ℝ) : ℝ := x

theorem clean_rate_eq (x : ℝ) : cleanRate x = x := rfl

end Calibrator
"""

CLEAN_SUB = HEADER + """
namespace Calibrator

/-- A model carrying data, not a conclusion. -/
structure CleanModel where
  rate : ℝ

end Calibrator
"""

CLEAN = {
    "Calibrator.lean": CLEAN_ROOT,
    "Calibrator/Sub.lean": CLEAN_SUB,
}


def clean_plus(rel: str, text: str) -> dict:
    files = dict(CLEAN)
    files[rel] = text
    return files


CASES = [
    # (guard, label, files, must_appear_in_output)
    ("style", "line over 100 characters",
     clean_plus("Calibrator/Sub.lean",
                CLEAN_SUB + "\n-- " + "x" * 120 + "\n"),
     "characters"),
    ("style", "missing license header",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB.replace("Released under Apache", "Licensed under")),
     "license header"),
    ("style", "lambda written with =>",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB + "\ndef f := fun x => x\n"),
     "rather than `=>`"),
    ("style", "documentation narrating development history",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB + "\n-- A previous version of this used a different form.\n"),
     "development history"),
    ("regimes", "forbidden result-carrier structure",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB + """
structure ChaosSpectroscopy where
  value : ℝ
"""),
     "forbidden result carrier"),
    ("regimes", "bare Prop switch field",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB + """
structure Switchy where
  flag : Prop
"""),
     "bare Prop switch"),
    ("regimes", "field packaging an advertised result",
     clean_plus("Calibrator/Sub.lean", CLEAN_SUB + """
structure Carrier where
  identification : ℝ
"""),
     "packages an advertised result"),
    ("closure", "module outside the root import closure",
     clean_plus("Calibrator/Orphan.lean", CLEAN_SUB),
     "MODULE_ABSENT"),
]


def calibrate_others() -> list:
    """Both directions for every guard that has a fixture. Returns failures."""
    failures = []

    # NEGATIVE, run once per guard: the clean fixture must satisfy all of them.
    # If this fails the positives below prove nothing, because a guard that
    # reports everything reports the planted defect too.
    for guard in ("style", "regimes", "closure", "wiring"):
        code, out = run_guard(guard, CLEAN)
        if code != 0:
            failures.append(
                f"FALSE POSITIVE  {guard}: clean fixture corpus rejected\n"
                + "\n".join("      " + l for l in out.strip().split("\n")[:12]))

    # POSITIVE: each planted defect must be reported, by the right guard.
    for guard, label, files, expected in CASES:
        code, out = run_guard(guard, files)
        if code == 0:
            failures.append(f"FALSE NEGATIVE  {guard}: {label} not reported at all")
        elif expected not in out:
            failures.append(
                f"MISREPORTED     {guard}: {label} reported, but not as {expected!r}")

    # The wiring guard's --json keys are a machine-readable contract. This is the
    # exact defect that shipped undetected, so it is asserted by name.
    code, out = run_guard("wiring", CLEAN, "--json")
    try:
        report = json.loads(out)
    except json.JSONDecodeError:
        failures.append("CONTRACT        wiring --json did not emit parseable JSON")
    else:
        for module, entry in report.items():
            missing = {"declarations", "dependents", "wired"} - set(entry)
            if missing:
                failures.append(
                    f"CONTRACT        wiring --json entry {module!r} is missing "
                    f"{sorted(missing)}; these keys are what consumers read")
            break

    # --list must name every guard the runner can dispatch, or a guard can be
    # dropped from the default set and nothing says so.
    r = subprocess.run([sys.executable, str(CHECK), "--list"],
                       capture_output=True, text=True)
    for guard in ("style", "identifications", "laundering", "regimes",
                  "closure", "wiring", "field-proofs"):
        if guard not in r.stdout:
            failures.append(f"DISPATCH        --list does not name the {guard!r} guard")

    return failures


def main() -> int:
    failures: list[str] = []

    # False negatives, and misfiling -- which is a false negative at the severity that
    # matters, since a FATAL pattern reported as FIDELITY does not stop the build.
    #
    # AT EVERY SEVERITY, not `--severity conditional`.  F21 is a FIDELITY family, so
    # filtering to CONDITIONAL hid it and the harness reported a working detector as a
    # FALSE NEGATIVE.  A severity flag in the harness cannot be distinguished from a
    # blind spot in the detector, so the harness must not use one here.
    got = families(run(POSITIVE))
    for missing in sorted(POSITIVE_EXPECTED - got):
        failures.append(f"FALSE NEGATIVE  {missing} planted but not reported")
    for extra in sorted(got - POSITIVE_EXPECTED):
        failures.append(f"MISFILED        {extra} reported but not planted")

    # False positives: clean mathematics must never gate the build.
    for bad in sorted(families(run(NEGATIVE, "--severity", "conditional"))):
        failures.append(f"FALSE POSITIVE  {bad} reported on clean mathematics")

    # The other six guards, both directions, against fixture corpora.
    failures.extend(calibrate_others())

    for f in failures:
        print(f"FAIL  {f}")
    if failures:
        print(f"\n{len(failures)} calibration failure(s).  Until these pass the "
              f"detector's report is not evidence, in either direction.")
        return 1
    print("guard calibration PASSED")
    print(f"  laundering: {len(POSITIVE_EXPECTED)} planted patterns, each in the right family")
    print("  laundering: 0 findings at FATAL or CONDITIONAL severity on clean mathematics")
    print(f"  style/regimes/closure/wiring: {len(CASES)} planted defects reported, "
          f"clean fixture corpus accepted by all four")
    print("  wiring --json keys asserted by name; --list names all seven guards")
    return 0


if __name__ == "__main__":
    sys.exit(main())

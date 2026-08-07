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
            a side condition emits nothing at all, because it is not a defect.

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

It also calibrates the other guards in `check.py` against fixture corpora, in both
directions.  The `conventions` guard is calibrated hardest, because its ledger is a
COMMITTED snapshot of a corpus that changes daily and therefore has failure modes the
other guards do not: wrong by omission, wrong by staleness, wrong by contradiction, and
wrong in its recorded data.  All four are planted here, together with the substring trap
that would let a careless matcher demand an F_ST estimator from a meeting time.

Run:  python3 validation/code/test_check.py
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# test_check.py sits beside check.py at validation/code/.
CHECK = Path(__file__).resolve().parent / "check.py"

# Read the depth limit from the guard rather than pinning it here. A fixture that
# hard-codes 12 stops testing the rule the moment someone changes the limit, and
# changing it is exactly the edit this harness exists to keep honest.
sys.path.insert(0, str(CHECK.parent))
import check as _check  # noqa: E402 -- the path has to be set first

SHAPE_DEPTH_LIMIT = _check.SHAPE_DEPTH_LIMIT

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
# side condition alongside its unguarded denominator; the side condition itself is
# not a finding.
POSITIVE_EXPECTED = {"F1", "F1b", "F2", "F3", "F4", "F5", "F6", "F7", "F8", "F9",
                     "F10", "F11", "F12", "F13", "F15", "F16", "F17", "F18",
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
# Calibration for the other seven guards
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
# The fixtures are a whole miniature corpus under DESCENT_CORPUS, not the real
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
        env = dict(os.environ, DESCENT_CORPUS=str(corpus))
        r = subprocess.run(
            [sys.executable, str(CHECK), "--only", guard, *args],
            capture_output=True, text=True, env=env)
        return r.returncode, r.stdout + r.stderr


def run_mathlib_guard(files: dict, mathlib: dict | None):
    """Run the `mathlib` guard against a fixture corpus AND a fixture Mathlib.

    `check.mathlib_root()` honours `DESCENT_MATHLIB` "so the guard can be
    calibrated against a fixture tree" -- that hook was built and never used,
    which is why this guard was the one guard with no calibration.  Passing
    `mathlib=None` points the override at a path that does not exist, which is
    how the cannot-run direction is exercised.

    Fixture Mathlib declarations must sit at ROOT level: the guard keys upstream
    names by their namespace stack, so a declaration written inside
    `namespace Mathlib` is stored as `Mathlib.foo` and can never collide with a
    corpus root name.  A fixture that wraps them reports a clean zero and looks
    like a blind spot in the guard rather than a mistake in the fixture.
    """
    import os
    with tempfile.TemporaryDirectory() as td:
        corpus = Path(td) / "proofs"
        corpus.mkdir()
        write_corpus(corpus, files)
        env = dict(os.environ, DESCENT_CORPUS=str(corpus))
        if mathlib is None:
            env["DESCENT_MATHLIB"] = str(Path(td) / "no-such-mathlib")
        else:
            root = Path(td) / "Mathlib"
            root.mkdir()
            write_corpus(root, mathlib)
            env["DESCENT_MATHLIB"] = str(root)
        r = subprocess.run(
            [sys.executable, str(CHECK), "--only", "mathlib"],
            capture_output=True, text=True, env=env)
        return r.returncode, r.stdout + r.stderr


# A fixture Mathlib: two root-level declarations the corpus can collide with.
FAKE_MATHLIB = {
    "Algebra/Fake.lean": (
        "/-! A fixture stand-in for Mathlib. -/\n"
        "theorem gnomonFakeUpstreamLemma (a b : Nat) : a + b = b + a := by\n"
        "  omega\n"
        "def gnomonFakeUpstreamDef (x : Nat) : Nat := x + 1\n"
    ),
}

# A corpus that declares only its own names.
MATHLIB_CLEAN = {
    "Descent.lean": HEADER + "\nimport Descent.Sub\n",
    "Descent/Sub.lean": HEADER + (
        "\nnamespace Descent\n\n"
        "/-- A definition with a declared status.\n\n"
        "Empirical status: UNTESTED. -/\n"
        "noncomputable def gnomonOwnRate (x : ℝ) : ℝ := x\n\n"
        "theorem gnomon_own_rate_eq (x : ℝ) : gnomonOwnRate x = x := rfl\n\n"
        "end Descent\n"
    ),
}

# The same corpus, but restating an upstream declaration under its own name.
MATHLIB_COLLIDES = {
    "Descent.lean": HEADER + "\nimport Descent.Sub\n",
    "Descent/Sub.lean": HEADER + (
        "\nnamespace Descent\n\n"
        "/-- Restates an upstream lemma.\n\n"
        "Empirical status: UNTESTED. -/\n"
        "theorem gnomonFakeUpstreamLemma (a b : Nat) : a + b = b + a := by\n"
        "  omega\n\n"
        "end Descent\n"
    ),
}


def calibrate_mathlib() -> list:
    """Both directions for the `mathlib` guard, plus cannot-run.

    WHY THIS EXISTS.  A mutation test -- neuter each `run_<guard>()` in
    check.py so it returns 0 with no findings, then re-run this file -- found
    that eight of the nine guards were covered and `mathlib` was not: silencing
    it entirely left this calibration green.  Its planted defects were being
    reported by other guards or not at all, so the guard that proves the corpus
    does not duplicate Mathlib could have gone blind without anything noticing.

    The cannot-run case is asserted first and is the one worth having most.  The
    guard already refuses to report a clean zero when it has no Mathlib to
    compare against; that behaviour is the difference between "found nothing"
    and "could not look", and it is exactly what an absent or renamed
    `.lake/packages/mathlib` would silently turn into a pass.
    """
    failures = []

    code, out = run_mathlib_guard(MATHLIB_CLEAN, None)
    if code == 0:
        failures.append(
            "CANNOT-RUN AS CLEAN  mathlib: with no Mathlib source the guard "
            "exited 0. A screen that cannot look must not report that it "
            "found nothing.")
    elif "CANNOT RUN" not in out:
        failures.append(
            "MISREPORTED     mathlib: no Mathlib source was reported as a "
            "finding rather than as an inability to run")

    code, out = run_mathlib_guard(MATHLIB_CLEAN, FAKE_MATHLIB)
    if code != 0:
        failures.append(
            "FALSE POSITIVE  mathlib: a corpus declaring only its own names "
            "was rejected\n"
            + "\n".join("      " + l for l in out.strip().split("\n")[:8]))

    code, out = run_mathlib_guard(MATHLIB_COLLIDES, FAKE_MATHLIB)
    if code == 0:
        failures.append(
            "FALSE NEGATIVE  mathlib: a corpus declaration whose name Mathlib "
            "already uses was not reported")
    elif "gnomonFakeUpstreamLemma" not in out:
        failures.append(
            "MISREPORTED     mathlib: the collision was reported without "
            "naming the colliding declaration")

    return failures


# A minimal corpus every guard is willing to call clean: license header, module
# docstring, short lines, one imported module, no forbidden shapes.
CLEAN_ROOT = HEADER + """
import Descent.Sub

namespace Descent

/-- A definition with a declared status. -/
noncomputable def cleanRate (x : ℝ) : ℝ := x

theorem clean_rate_eq (x : ℝ) : cleanRate x = x := rfl

end Descent
"""

CLEAN_SUB = HEADER + """
namespace Descent

/-- A model carrying data, not a conclusion. -/
structure CleanModel where
  rate : ℝ

end Descent
"""

CLEAN = {
    "Descent.lean": CLEAN_ROOT,
    "Descent/Sub.lean": CLEAN_SUB,
}


def clean_plus(rel: str, text: str) -> dict:
    files = dict(CLEAN)
    files[rel] = text
    return files


# --------------------------------------------------------------------------------------
# Convention-ledger fixtures.
#
# The ledger is a COMMITTED snapshot of a corpus that changes daily, so its
# failure modes are not the usual ones.  A ledger can be wrong by omission (a new
# declaration nobody classified), wrong by staleness (an entry for a declaration
# that is gone), wrong by contradiction (two conventions in one module with
# nothing relating them), or wrong in its data (a constant that drifted).  All
# four are asserted below, and so is the substring trap that would make the
# matcher pull unrelated declarations into a quantity family.
# --------------------------------------------------------------------------------------

CONVENTION_LEAN = HEADER + """
namespace Descent

/-- A model carrying data, not a conclusion. -/
structure CleanModel where
  rate : ℝ

/-- Hudson-flavoured. -/
noncomputable def sampleHudsonFst (p : ℝ) : ℝ := p / (1 + p)

/-- Nei-flavoured, in the same module. -/
noncomputable def sampleNeiGst (p : ℝ) : ℝ := p * p

/-- Merely transforms whatever it is handed. -/
noncomputable def retentionFromFst (f : ℝ) : ℝ := 1 - f

/-- A name that CONTAINS the letters `gSt` and is not an F_ST at all. -/
noncomputable def steppingStoneMeetingTime (x : ℝ) : ℝ := x

/-- Not named for an F_ST, but it consumes one.

    Empirical status: UNTESTED. -/
noncomputable def portabilityFromDivergence (v fst : ℝ) : ℝ := v * (1 - fst)

theorem sample_bridge (p : ℝ) : sampleHudsonFst p = p / (1 + p) := rfl

end Descent
"""


def convention_ledger(entries: dict, bridges: list | None = None,
                      verified: dict | None = None) -> str:
    return json.dumps({
        "verified_constants": verified or {},
        "empirical_status_vocabulary": {"terms": {
            "UNTESTED": "no measurement has been made",
            "VALIDATED": "measured and not rejected",
            "NOT AN EMPIRICAL CLAIM": "no observable content",
        }},
        "conventions": {
            "hudson": {"means": "between-subgroup denominator", "source": "Hudson (1992)"},
            "nei-gst": {"means": "total-pool denominator", "source": "Nei (1973)"},
            "inherited": {"means": "commits to nothing", "source": "n/a"},
        },
        "bridges": [{"between": ["nei-gst", "hudson"], "theorem": "sample_bridge",
                     "says": "fixture bridge"}] if bridges is None else bridges,
        "quantities": {
            "fst": {"words": ["fst", "gst"], "scope": "complete",
                    "argument_scope": "complete",
                    "conventions": ["hudson", "nei-gst", "inherited"],
                    "incompatible": [["nei-gst", "hudson"]],
                    "why": "fixture"},
        },
        "declarations": entries,
    }, indent=2)


CONVENTION_ENTRIES = {
    "Descent/Sub.lean::sampleHudsonFst": {
        "quantity": "fst", "convention": "hudson", "constants": ["1"]},
    "Descent/Sub.lean::sampleNeiGst": {
        "quantity": "fst", "convention": "nei-gst"},
    "Descent/Sub.lean::retentionFromFst": {
        "quantity": "fst", "convention": "inherited", "constants": ["1"]},
    "Descent/Sub.lean::portabilityFromDivergence": {
        "quantity": "fst", "convention": "inherited", "role": "consumer",
        "constants": ["1"]},
}


def convention_corpus_files(entries=None, bridges=None, lean=None, ledger=True,
                            verified=None) -> dict:
    files = dict(CLEAN)
    files["Descent/Sub.lean"] = CONVENTION_LEAN if lean is None else lean
    if ledger:
        files["validation/conventions.json"] = convention_ledger(
            CONVENTION_ENTRIES if entries is None else entries, bridges, verified)
    return files


# The `layers` guard had no fixture in either direction, and its REACHABLE rule is
# the one rule in this file that a repair can silence by accident: it scans the corpus
# TEXT for qualified names, so anything that narrows what counts as text narrows the
# rule, and a rule that reports nothing looks exactly like a corpus with nothing to
# report.  Both cases below are about that rule and about the same name.
#
# The trap is not hypothetical.  `Descent.Meta.Linters` builds the message
# "`Core.Theta`, `Core.BigM` ... are the types for these" and hands it to an author
# who wrote a bare `ℝ`; REACHABLE read those as references and asked that file to
# import `Descent.Core.Scaling`, which the guard's own META rule forbids it to import.
LAYERS_CORE = HEADER + """
namespace Descent.Core

/-- A scaled quantity, defined here and nowhere else. -/
def bigM : ℝ := 1

end Descent.Core
"""

LAYERS_ROOT = HEADER + """
import Descent.Core.Scale
import Descent.PopGen.Uses
"""


def layers_corpus(uses: str) -> dict:
    """A two-layer fixture: `Core` defines `bigM`, `PopGen` does something with it."""
    return {
        "Descent.lean": LAYERS_ROOT,
        "Descent/Core/Scale.lean": LAYERS_CORE,
        "Descent/PopGen/Uses.lean": HEADER + uses,
    }


LAYERS_REFERENCE = """
namespace Descent.PopGen

theorem uses_it : Core.bigM = 1 := rfl

end Descent.PopGen
"""

LAYERS_IN_A_STRING = """
namespace Descent.PopGen

/-- Advice for an author, which is prose and not a reference. -/
def advice : String := "Core.bigM is the type for this"

end Descent.PopGen
"""

# A corpus with SHAPE: two directories, each with a head, and a real edge between
# them. `heads` and the four shape guards read the directory layout and the import
# graph rather than the text of a declaration, so none of the fixtures above can reach
# them -- which is why all five had no control of any kind. This is the smallest tree
# that satisfies all of them at once, and every case below is one planted defect in it.
SHAPE_ROOT = HEADER + """
import Descent.Alpha
import Descent.Beta
"""

SHAPE_ALPHA_HEAD = HEADER + """
import Descent.Alpha.One
"""

SHAPE_ALPHA_ONE = HEADER + """
namespace Descent.Alpha

/-- A quantity the other directory reads. -/
noncomputable def alphaOne (x : ℝ) : ℝ := x

end Descent.Alpha
"""

SHAPE_BETA_HEAD = HEADER + """
import Descent.Beta.Two
"""

SHAPE_BETA_TWO = HEADER + """
import Descent.Alpha.One

namespace Descent.Beta

/-- Reads `Alpha.One`, which is the edge that makes this corpus one component. -/
noncomputable def betaTwo (x : ℝ) : ℝ := Alpha.alphaOne x

end Descent.Beta
"""


def shape_corpus(**overrides) -> dict:
    """The clean shape fixture, with named files replaced or added."""
    files = {
        "Descent.lean": SHAPE_ROOT,
        "Descent/Alpha.lean": SHAPE_ALPHA_HEAD,
        "Descent/Alpha/One.lean": SHAPE_ALPHA_ONE,
        "Descent/Beta.lean": SHAPE_BETA_HEAD,
        "Descent/Beta/Two.lean": SHAPE_BETA_TWO,
    }
    for rel, text in overrides.items():
        files[rel.replace("__", "/").replace("_lean", ".lean")] = text
    return files


def shape_chain(n: int) -> dict:
    """A corpus that is one chain of `n` modules under a single head.

    `shape-depth`'s limit is 12, and nothing shorter than that can exercise it. The
    chain is generated rather than written out because the number is the point: a
    fixture pinned at exactly the limit stops testing the rule the moment someone
    changes the limit.
    """
    files = {"Descent.lean": HEADER + "\nimport Descent.Alpha\n"}
    head = [f"import Descent.Alpha.M{i}" for i in range(n)]
    files["Descent/Alpha.lean"] = HEADER + "\n" + "\n".join(head) + "\n"
    for i in range(n):
        imports = f"import Descent.Alpha.M{i - 1}\n" if i else ""
        body = (f"noncomputable def m{i} (x : ℝ) : ℝ := "
                + (f"Alpha.m{i - 1} x" if i else "x"))
        files[f"Descent/Alpha/M{i}.lean"] = (
            HEADER + "\n" + imports + "\nnamespace Descent.Alpha\n\n"
            f"/-- Rung {i} of a chain. -/\n{body}\n\nend Descent.Alpha\n")
    return files


# `shape-routes` reads the FIELD NAMES off `structure PopGenParameters` in
# `Descent.Core.Parameters`, so its fixture has to be a corpus with that record in that
# module. Its docstring says it "was calibrated against a fixture holding exactly the
# pair above"; this is that fixture, in the harness, where the claim can be checked.
ROUTES_PARAMETERS = HEADER + """
namespace Descent.Core

/-- The record every route is supposed to go through. -/
structure PopGenParameters where
  /-- Effective population size. -/
  Ne : ℝ
  /-- Mutation rate. -/
  mu : ℝ
  /-- Migration rate. -/
  mig : ℝ
  /-- Additive genetic variance. -/
  V_A : ℝ

end Descent.Core
"""

ROUTES_RECORD_ROUTE = """
/-- The route through the record, which is the one whose constraints reach a caller. -/
noncomputable def deployedR2 (p : PopGenParameters) (V_E : ℝ) : ℝ := p.V_A + V_E
"""

ROUTES_RAW_ROUTE = """
/-- A second route to the same metric, taking the record's fields as loose reals. -/
noncomputable def deployedR2FromIsland (Ne mu mig V_A : ℝ) : ℝ := Ne + mu + mig + V_A
"""


def routes_corpus(raw: bool) -> dict:
    """The record-typed route, with or without a raw-real twin beside it."""
    body = ROUTES_RECORD_ROUTE + (ROUTES_RAW_ROUTE if raw else "")
    return {
        "Descent.lean": HEADER + "\nimport Descent.Core\n",
        "Descent/Core.lean": HEADER + """
import Descent.Core.Parameters
import Descent.Core.Metrics
""",
        "Descent/Core/Parameters.lean": ROUTES_PARAMETERS,
        "Descent/Core/Metrics.lean": HEADER + """
import Descent.Core.Parameters

namespace Descent.Core
""" + body + """
end Descent.Core
""",
    }


# `shape-spine`'s two floors -- 80 spine theorems, 20% cross-module reuse -- cannot be
# MET by a fixture, so its control is not about the floors. It is about the detection
# underneath them: which theorems the guard counts as spine. Both halves of that
# definition are asserted here, because a guard that counted the wrong theorems would
# report a number that looks exactly as wrong as a corpus with no spine.
SPINE_MOMENTS = HEADER + """
namespace Descent.Core

/-- A deployed metric: an `ℝ`-valued definition of `Core/Moments.lean`.  The body is on
the next line because that is what the kernel scan requires -- it reads a definition
whose SIGNATURE ends the line, so a one-liner is not seen as a metric at all. -/
noncomputable def r2 (x : ℝ) : ℝ :=
  x

end Descent.Core
"""

SPINE_PARAMETERS = HEADER + """
namespace Descent.Core

/-- The record a spine theorem has to start from. -/
structure PopGenParameters where
  /-- Additive genetic variance. -/
  V_A : ℝ

end Descent.Core
"""

SPINE_THEOREMS = HEADER + """
import Descent.Core.Moments
import Descent.Core.Parameters

namespace Descent.Core

/-- Binds the record AND names a deployed metric, which is what a spine theorem is. -/
theorem carries_demography_to_r2 (p : PopGenParameters) : r2 p.V_A = p.V_A := rfl

/-- Names the metric about a free real. The record is what the free real was supposed
to have come from, and nothing here says it did. -/
theorem free_real_reaches_r2 (x : ℝ) : r2 x = x := rfl

end Descent.Core
"""


def spine_corpus() -> dict:
    return {
        "Descent.lean": HEADER + "\nimport Descent.Core\n",
        "Descent/Core.lean": HEADER + """
import Descent.Core.Moments
import Descent.Core.Parameters
import Descent.Core.Spine
""",
        "Descent/Core/Moments.lean": SPINE_MOMENTS,
        "Descent/Core/Parameters.lean": SPINE_PARAMETERS,
        "Descent/Core/Spine.lean": SPINE_THEOREMS,
    }


# `core-empirics` joins Core's docstrings against `simcov/ledger.json`, and
# `LEDGER_PATH` is built from `CORPUS`, so a fixture corpus can carry its own ledger --
# which is the only way to test a rule whose whole content is the join.
CORE_EMPIRICS_LEAN = HEADER + """
namespace Descent.Core

/-- A quantity a battery measured.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a definition and the laws
    computed from it. -/
noncomputable def measuredRate (x : ℝ) : ℝ :=
  x

end Descent.Core
"""


def core_empirics_corpus(verdict: str) -> dict:
    """Core's surface, plus a ledger holding one row against it."""
    ledger = {
        "records": [
            {
                "role": "corpus",
                "declaration": "measuredRate",
                "lean_file": "Descent/Core/Rates.lean",
                "verdict": verdict,
                "battery": "fixture1",
            }
        ]
    }
    return {
        "Descent.lean": HEADER + "\nimport Descent.Core\n",
        "Descent/Core.lean": HEADER + "\nimport Descent.Core.Rates\n",
        "Descent/Core/Rates.lean": CORE_EMPIRICS_LEAN,
        "validation/empirical/simcov/ledger.json": json.dumps(ledger, indent=2),
    }


LEDGER_LEAN = HEADER + """
namespace Descent.Core

/-- A quantity whose docstring cites a battery.

Measured by `simcov/battery_ghost.py`.

    Empirical status: MEASURED -- a number was obtained. -/
noncomputable def citedRate (x : ℝ) : ℝ :=
  x

end Descent.Core
"""


def ledger_corpus(known_battery: bool) -> dict:
    """A docstring citing a battery the ledger has, or has never seen."""
    records = []
    if known_battery:
        records.append({
            "role": "corpus",
            "declaration": "citedRate",
            "lean_file": "Descent/Core/Cited.lean",
            "verdict": "MATCH",
            "battery": "ghost",
        })
    return {
        "Descent.lean": HEADER + "\nimport Descent.Core\n",
        "Descent/Core.lean": HEADER + "\nimport Descent.Core.Cited\n",
        "Descent/Core/Cited.lean": LEDGER_LEAN,
        "validation/empirical/simcov/ledger.json": json.dumps({"records": records},
                                                             indent=2),
    }


CASES = [
    # (guard, label, files, must_appear_in_output)
    ("ledger", "a docstring citing a battery the ledger has never seen",
     ledger_corpus(known_battery=False), "never seen"),
    ("core-empirics", "a Core declaration denying measurement the ledger measured",
     core_empirics_corpus("MATCH"), "while the ledger holds"),
    ("core-empirics", "a FALSIFIED row whose declaration never names the battery",
     core_empirics_corpus("FALSIFIED"), "never names that battery"),
    ("shape-spine", "a theorem binding the record and naming a deployed metric",
     spine_corpus(), "have: carries_demography_to_r2"),
    ("heads", "a module on disk that its directory head does not import",
     shape_corpus(**{"Descent/Alpha.lean": HEADER + "\n"}),
     "does not import"),
    ("heads", "a head that states a theorem instead of listing modules",
     shape_corpus(**{"Descent/Alpha.lean": SHAPE_ALPHA_HEAD
                     + "\ntheorem head_states_something : (1:ℕ) = 1 := rfl\n"}),
     "a head is a table of contents"),
    ("shape-components", "a subsystem that reaches nothing and nothing reaches",
     shape_corpus(**{"Descent/Beta/Two.lean": HEADER + """
namespace Descent.Beta

/-- Names nothing in the corpus, and nothing names it. -/
noncomputable def betaTwo (x : ℝ) : ℝ := x

end Descent.Beta
"""}),
     "component"),
    ("shape-chains", "a module whose one internal import is a sibling it never names",
     shape_corpus(**{"Descent/Alpha.lean": SHAPE_ALPHA_HEAD + "import Descent.Alpha.Three\n",
                     "Descent/Alpha/Three.lean": HEADER + """
import Descent.Alpha.One

namespace Descent.Alpha

/-- Imports `One` and names nothing it declares. -/
noncomputable def alphaThree (x : ℝ) : ℝ := x

end Descent.Alpha
"""}),
     "unused sibling"),
    ("shape-depth", "an import chain past the limit",
     shape_chain(SHAPE_DEPTH_LIMIT + 2),
     "exceeds"),
    ("shape-routes", "a raw-real second route beside the record-typed one",
     routes_corpus(raw=True),
     "re-supplies"),
    ("layers", "a qualified name from a layer the file cannot reach",
     layers_corpus(LAYERS_REFERENCE), "names Core.bigM"),
    # The `set_option` screen was one rule reading a timeout and a kernel bypass as
    # the same finding. It is two now, and both directions are asserted: the bypass
    # here, the budget among the traps below.
    ("identifications", "a compiler option that disables the kernel check",
     clean_plus("Descent/Sub.lean",
                CLEAN_SUB.replace("namespace Descent",
                                  "set_option debug.skipKernelTC true\n\nnamespace Descent")),
     "changes what is ACCEPTED"),
    ("identifications", "a compiler option that is neither a budget nor named",
     clean_plus("Descent/Sub.lean",
                CLEAN_SUB.replace("namespace Descent",
                                  "set_option pp.all true\n\nnamespace Descent")),
     "other than `maxHeartbeats`"),
    ("style", "line over 100 characters",
     clean_plus("Descent/Sub.lean",
                CLEAN_SUB + "\n-- " + "x" * 120 + "\n"),
     "characters"),
    ("style", "missing license header",
     clean_plus("Descent/Sub.lean", CLEAN_SUB.replace("Released under Apache", "Licensed under")),
     "license header"),
    ("style", "lambda written with =>",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + "\ndef f := fun x => x\n"),
     "rather than `=>`"),
    ("style", "documentation narrating development history",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + "\n-- A previous version of this used a different form.\n"),
     "development history"),
    ("regimes", "forbidden result-carrier structure",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure ChaosSpectroscopy where
  value : ℝ
"""),
     "forbidden result carrier"),
    ("regimes", "bare Prop switch field",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure Switchy where
  flag : Prop
"""),
     "bare Prop switch"),
    ("regimes", "field packaging an advertised result",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure Carrier where
  identification : ℝ
"""),
     "packages an advertised result"),
    ("closure", "module outside the root import closure",
     clean_plus("Descent/Orphan.lean", CLEAN_SUB),
     "MODULE_ABSENT"),
    # Elaboration-time code, which can change what a declaration means.
    ("identifications", "an elaborator installed in the corpus",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
elab "cheat" : tactic => do
  pure ()
"""),
     "installs custom syntax"),
    # The missing-argument screen, in both directions.  A definition that COMPUTES
    # statistical power without a significance threshold is the defect it exists for.
    ("identifications", "a power definition with no significance threshold",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
/-- Power of the association test at effect size `beta`.

    Empirical status: UNTESTED. -/
noncomputable def gwasDetectionPower (beta sampleSize : ℝ) : ℝ :=
  beta * sampleSize
"""),
     "takes no alpha-like argument"),
    # A macro at TERM level rewrites the statement a reader thinks they read.
    ("identifications", "a term-level macro",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
macro "myRate" x:term : term => `(cleanRate $x)
"""),
     "non-tactic macro"),
    # The three duplication shapes, one case each.  They are planted separately
    # because they have three different fixes, and a screen that reports the
    # wrong one of the three sends the reader to the wrong repair.
    ("duplication", "one proposition proved twice under two names",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem retention_le_initial (ne t : ℝ) (h : 0 < ne) :
    (1 - 1 / (2 * ne)) ^ t * cleanRate ne ≤ cleanRate ne := by
  sorry

theorem heterozygosity_bounded (n s : ℝ) (hn : 0 < n) :
    (1 - 1 / (2 * n)) ^ s * cleanRate n ≤ cleanRate n := by
  sorry
"""),
     "same proposition under different names"),
    ("duplication", "one proof script under two different statements",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem alpha_bound (x : ℝ) (hx : 0 < x) : cleanRate x ≤ cleanRate x + x := by
  have h1 : 0 ≤ x := le_of_lt hx
  have h2 : cleanRate x = x := rfl
  simp [cleanRate, h1, h2]
  linarith [hx, h1]

theorem beta_bound (y : ℝ) (hy : 0 < y) : cleanRate y ≤ cleanRate y * 2 + y := by
  have h1 : 0 ≤ y := le_of_lt hy
  have h2 : cleanRate y = y := rfl
  simp [cleanRate, h1, h2]
  linarith [hy, h1]
"""),
     "identical proof scripts under different statements"),
    ("duplication", "a copy-pasted block of source lines",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure PanelA where
  sampleSizePerAncestry : ℕ
  alleleFrequencySpectrum : ℝ
  effectSizeStandardError : ℝ
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  observedGenerationCount : ℕ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ

structure PanelB where
  sampleSizePerAncestry : ℕ
  alleleFrequencySpectrum : ℝ
  effectSizeStandardError : ℝ
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  observedGenerationCount : ℕ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ
"""),
     "verbatim repeated source blocks"),
    # A copy that was renamed on the way. Comparing raw text misses exactly the
    # copy-paste-then-rename, which is the commonest way a block gets duplicated.
    ("duplication", "a block repeated up to its local names",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
noncomputable def panelScoreFirst (widthA depthA : ℝ) : ℝ :=
  let scaledWidth := cleanRate widthA * 2
  let scaledDepth := cleanRate depthA * 3
  let combined := scaledWidth + scaledDepth
  let penalised := combined - cleanRate widthA
  let widened := penalised * cleanRate depthA
  let settled := widened + combined
  let finished := settled * 2
  finished + combined

noncomputable def panelScoreSecond (spanB reachB : ℝ) : ℝ :=
  let scaledSpan := cleanRate spanB * 2
  let scaledReach := cleanRate reachB * 3
  let merged := scaledSpan + scaledReach
  let charged := merged - cleanRate spanB
  let broadened := charged * cleanRate reachB
  let rested := broadened + merged
  let closed := rested * 2
  closed + merged
"""),
     "verbatim repeated source blocks"),
    # Shorter, but three times. Eight-lines-twice and five-lines-three-times are
    # the same defect with the copying spread differently.
    ("duplication", "a five-line block repeated three times",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure ShortPanelA where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ

structure ShortPanelB where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ

structure ShortPanelC where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ
"""),
     "verbatim repeated source blocks"),
    # An argument, not a reflex, at twelve tokens: below the old fifteen-token
    # floor and invisible because of it.
    ("duplication", "a short but chosen proof script under two statements",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem chosen_step_first (x : ℝ) (hx : 0 < x) : 0 < cleanRate x + x := by
  unfold cleanRate
  have hdouble : 0 < x + x := by linarith
  linarith

theorem chosen_step_second (y : ℝ) (hy : 0 < y) : 0 < cleanRate y + y * 1 := by
  unfold cleanRate
  have hdouble : 0 < y + y := by linarith
  linarith
"""),
     "identical proof scripts under different statements"),
    # Citing a corpus lemma exempts a one-step application, not a whole argument
    # built around one: the rest of the script is still shared and still unnamed.
    ("duplication", "a long shared argument that happens to cite a corpus lemma",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem cited_helper (x : ℝ) : 0 ≤ x * x := mul_self_nonneg x

theorem long_shared_first (x : ℝ) (hx : 0 < x) : 0 < cleanRate x + x * x + x := by
  have hsquare := cited_helper x
  have hrate : cleanRate x = x := rfl
  have hsum : 0 < x + x := by linarith
  rw [hrate]
  nlinarith [hx, hsquare, hsum]

theorem long_shared_second (y : ℝ) (hy : 0 < y) : 0 < cleanRate y + y * y + y * 1 := by
  have hsquare := cited_helper y
  have hrate : cleanRate y = y := rfl
  have hsum : 0 < y + y := by linarith
  rw [hrate]
  nlinarith [hy, hsquare, hsum]
"""),
     "identical proof scripts under different statements"),
    # Short, and about this corpus: under the old length floor it was dropped
    # for being nineteen characters long.
    ("duplication", "a short statement naming a corpus definition, proved twice",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem clean_rate_at_one_first : cleanRate 1 = 1 := rfl

theorem clean_rate_at_one_second : cleanRate 1 = 1 := by
  unfold cleanRate
"""),
     "same proposition under different names"),

    # --- conventions: the four rules, one planted defect each -------------------
    ("conventions", "a definition carrying a ledgered quantity with no ledger entry",
     convention_corpus_files(
         entries={k: v for k, v in CONVENTION_ENTRIES.items()
                  if not k.endswith("sampleNeiGst")}),
     "has no ledger entry"),
    ("conventions", "two incompatible conventions in one module with no bridge",
     convention_corpus_files(bridges=[]),
     "declares incompatible"),
    ("conventions", "a ledgered constant the body no longer carries",
     convention_corpus_files(
         entries=dict(CONVENTION_ENTRIES,
                      **{"Descent/Sub.lean::sampleHudsonFst": {
                          "quantity": "fst", "convention": "hudson",
                          "constants": ["4"]}})),
     "ledger records constants"),
    ("conventions", "a ledger entry whose declaration no longer exists",
     convention_corpus_files(
         entries=dict(CONVENTION_ENTRIES,
                      **{"Descent/Sub.lean::deletedFst": {
                          "quantity": "fst", "convention": "hudson"}})),
     "is no longer a `def`"),
    ("conventions", "a bridge naming a theorem the corpus does not have",
     convention_corpus_files(
         bridges=[{"between": ["nei-gst", "hudson"], "theorem": "vanished_bridge"}]),
     "is not in the corpus"),
    ("conventions", "a ledger naming a convention it never defines",
     convention_corpus_files(
         entries=dict(CONVENTION_ENTRIES,
                      **{"Descent/Sub.lean::sampleNeiGst": {
                          "quantity": "fst", "convention": "nei-fst-typo"}})),
     "is not in `conventions`"),
    ("conventions", "no ledger at all",
     convention_corpus_files(ledger=False),
     "CANNOT RUN"),
    # `verified_constants` is the record of values read against a published
    # source.  Its whole purpose is that a 4 turning into a 2 fails here, so that
    # is planted directly -- on a definition carrying NO ledgered quantity, which
    # is the case the `declarations` rules cannot reach.
    ("conventions", "a source-verified constant the body no longer carries",
     convention_corpus_files(
         verified={"Descent/Sub.lean::steppingStoneMeetingTime": {
             "constants": ["4"], "source": "fixture"}}),
     "ledger records constants"),
    ("conventions", "a source-verified record naming a declaration that is gone",
     convention_corpus_files(
         verified={"Descent/Sub.lean::vanishedDef": {
             "constants": ["4"], "source": "fixture"}}),
     "is no longer a `def`"),
    # One definition recorded twice can have its two records disagree, and only
    # one of them would ever be read.  This fired on the real ledger the first
    # time it ran, on `liabilityScaleH2`.
    ("conventions", "one definition recorded in both tables",
     convention_corpus_files(
         verified={"Descent/Sub.lean::sampleHudsonFst": {
             "constants": ["1"], "source": "fixture"}}),
     "appears in both"),
    ("conventions", "a source-verified record that pins nothing",
     convention_corpus_files(
         verified={"Descent/Sub.lean::steppingStoneMeetingTime": {
             "source": "fixture"}}),
     "pins no constants"),
    # A definition NOT named for the quantity that nevertheless consumes one.
    # This is where a convention mismatch does its damage -- a caller holding a
    # Nei value feeds it to a body written for a per-branch F and nothing
    # type-errors -- and being unnamed is no protection.
    ("conventions", "a definition that CONSUMES a ledgered quantity with no entry",
     convention_corpus_files(
         entries={k: v for k, v in CONVENTION_ENTRIES.items()
                  if not k.endswith("portabilityFromDivergence")}),
     "ARGUMENT"),
    # The status vocabulary, both failure shapes.
    ("conventions", "an `Empirical status:` head in the wrong case",
     convention_corpus_files(
         lean=CONVENTION_LEAN.replace("Empirical status: UNTESTED",
                                      "Empirical status: untested")),
     "in the wrong case"),
    ("conventions", "an `Empirical status:` head outside the vocabulary",
     convention_corpus_files(
         lean=CONVENTION_LEAN.replace("Empirical status: UNTESTED",
                                      "Empirical status: PROBABLY FINE")),
     "is not in the vocabulary"),
]

# Duplication traps: mathematics that LOOKS repeated to a careless screen and is
# not.  Each is a false positive the guard would produce under an obvious
# simplification of its rules, and a duplication screen that fires on these is
# useless -- Lean proofs repeat short tactics everywhere, and a screen readers
# learn to skim past has been deleted in effect.
NEGATIVE_CASES = [
    # The message form, not the silent form, and for the reason the paragraph above
    # gives about `identifications`: `LAYER_PENDING` is a table of outstanding edges in
    # the REAL corpus, so every one of its fifteen entries is stale against a
    # three-file fixture and the guard exits nonzero no matter what this trap does.
    # Demanding a clean exit here would assert something about the fixture.
    ("layers", "a qualified name inside a string literal, which is prose",
     layers_corpus(LAYERS_IN_A_STRING), "names Core.bigM"),
    # The other half of the pair `shape-routes` is about: the record-typed route on its
    # own is the shape the guard wants, not a shape it reports.
    ("shape-routes", "a record-typed route with no raw-real twin", routes_corpus(raw=False)),
    # The other half of what a spine theorem IS. Naming the metric is not enough; a
    # theorem about a free real is the shape the record exists to replace, and counting
    # it would put this guard and `shape-routes` in opposition.
    ("shape-spine", "a theorem naming the metric about a free real",
     spine_corpus(), "have: free_real_reaches_r2"),
    # A heartbeat budget decides whether elaboration FINISHES; it cannot make the
    # kernel accept anything it would otherwise reject. Reporting it under a sentence
    # about `debug.skipKernelTC` is what the split above fixed, so the trap asserts
    # that neither of the two messages now comes back for it.
    ("identifications", "a raised elaboration budget, which changes nothing accepted",
     clean_plus("Descent/Sub.lean",
                CLEAN_SUB.replace("namespace Descent",
                                  "set_option maxHeartbeats 2000000\n\nnamespace Descent")),
     "set_option"),
    ("duplication", "two short idiomatic proofs of different statements",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem model_rate_refl (m : CleanModel) : m.rate = m.rate := rfl

theorem model_rate_le (m : CleanModel) : m.rate ≤ m.rate := le_refl m.rate
""")),
    ("duplication", "an alias whose proof cites the theorem it restates",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem panel_weight_nonneg (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ w * w + w * w * w := by
  sorry

theorem panel_weight_nonneg' (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ v * v + v * v * v :=
  panel_weight_nonneg v hv
""")),
    # The screen's own remedy, carried out: one lemma, two applications. If the two
    # call sites were reported, every successful factoring would leave a fresh
    # finding behind and the guard would push the corpus back toward copying.
    ("duplication", "two bounds that each apply one already-named corpus lemma",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem root_is_low_or_high (a x : ℝ) (hroot : (a - x) * (a + 1 - x) = 0) :
    x = a ∨ x = a + 1 := by
  sorry

theorem root_ge_one (a x : ℝ) (ha : 1 ≤ a) (hroot : (a - x) * (a + 1 - x) = 0) :
    1 ≤ x := by
  rcases root_is_low_or_high a x hroot with h | h <;> linarith

theorem root_le_three (a x : ℝ) (ha : a ≤ 2) (hroot : (a - x) * (a + 1 - x) = 0) :
    x ≤ 3 := by
  rcases root_is_low_or_high a x hroot with h | h <;> linarith
""")),
    # A run of one-line `have`s matches itself at every shift. Reporting those shifts
    # claims an eight-line block was copied when the repeat is a single line.
    ("duplication", "a run of one-line steps that matches itself at every shift",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem periodic_step_run (weightBound eventBound benefitBound harmBound netBound spanBound leadBound lagBound driftBound shiftBound slopeBound offsetBound scaleBound widthBound depthBound reachBound tiltBound span2Bound : ℝ → ℝ) (t : ℝ) : True := by
  have hweight : 0 ≤ |weightBound t| := abs_nonneg (weightBound t)
  have hevent : 0 ≤ |eventBound t| := abs_nonneg (eventBound t)
  have hbenefit : 0 ≤ |benefitBound t| := abs_nonneg (benefitBound t)
  have hharm : 0 ≤ |harmBound t| := abs_nonneg (harmBound t)
  have hnet : 0 ≤ |netBound t| := abs_nonneg (netBound t)
  have hspan : 0 ≤ |spanBound t| := abs_nonneg (spanBound t)
  have hlead : 0 ≤ |leadBound t| := abs_nonneg (leadBound t)
  have hlag : 0 ≤ |lagBound t| := abs_nonneg (lagBound t)
  have hdrift : 0 ≤ |driftBound t| := abs_nonneg (driftBound t)
  have hshift : 0 ≤ |shiftBound t| := abs_nonneg (shiftBound t)
  have hslope : 0 ≤ |slopeBound t| := abs_nonneg (slopeBound t)
  have hoffset : 0 ≤ |offsetBound t| := abs_nonneg (offsetBound t)
  have hscale : 0 ≤ |scaleBound t| := abs_nonneg (scaleBound t)
  have hwidth : 0 ≤ |widthBound t| := abs_nonneg (widthBound t)
  have hdepth : 0 ≤ |depthBound t| := abs_nonneg (depthBound t)
  have hreach : 0 ≤ |reachBound t| := abs_nonneg (reachBound t)
  have htilt : 0 ≤ |tiltBound t| := abs_nonneg (tiltBound t)
  have hspan2 : 0 ≤ |span2Bound t| := abs_nonneg (span2Bound t)
  trivial
""")),
    # `power` is two words.  An exponent taken as a natural-number argument is the
    # algebraic one, and asking a sum of q-th powers for an alpha level is asking the
    # wrong question.  `auc` is likewise a word, not the letters inside `cauchy`.
    ("identifications", "an exponent named power, and AUC's letters inside another word",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
/-- Sum of `power`-th entry powers of a matrix.

    Empirical status: UNTESTED. -/
noncomputable def entryPowerTotal (m : Matrix (Fin 2) (Fin 2) ℝ) (power : ℕ) : ℝ :=
  ∑ i, ∑ j, m i j ^ power

/-- Conditioning profile of a Cauchy matrix at parameter `theta`.

    Empirical status: UNTESTED. -/
noncomputable def cauchyProfileScale (theta : ℝ) : ℝ :=
  theta * theta
"""),
     "takes no"),
    # A `Prop` relating two metrics takes them as arguments; it computes neither.
    ("identifications", "a Prop relating two given AUC values",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
/-- Discrimination falls from source to target.

    Empirical status: UNTESTED. -/
def AucFallsAcrossPopulations (sourceAuc targetAuc : ℝ) : Prop :=
  targetAuc < sourceAuc
"""),
     "takes no"),
    ("duplication", "trivially true statements that coincide by accident",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem nat_self (n : ℕ) : n = n := rfl

theorem int_self (k : ℤ) : k = k := rfl
""")),
    # A specialisation repeats its parent's hypotheses and then applies the parent.
    # That is a claim and its instance, tied by a citation the compiler checks --
    # the same tie the statement and proof screens already credit.
    ("duplication", "a specialisation that repeats its parent's hypotheses and cites it",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem general_panel_bound
    (sampleSizePerAncestry : ℕ)
    (alleleFrequencySpectrum : ℝ)
    (effectSizeStandardError : ℝ)
    (ancestryFractionEstimate : ℝ)
    (recombinationWindowRadius : ℕ)
    (perGenerationMutationRate : ℝ)
    (h_spectrum : 0 ≤ alleleFrequencySpectrum)
    (h_error : 0 ≤ effectSizeStandardError) :
    0 ≤ alleleFrequencySpectrum + effectSizeStandardError := by
  linarith

theorem general_panel_bound_at_two
    (alleleFrequencySpectrum : ℝ)
    (effectSizeStandardError : ℝ)
    (ancestryFractionEstimate : ℝ)
    (recombinationWindowRadius : ℕ)
    (perGenerationMutationRate : ℝ)
    (h_spectrum : 0 ≤ alleleFrequencySpectrum)
    (h_error : 0 ≤ effectSizeStandardError) :
    0 ≤ alleleFrequencySpectrum + effectSizeStandardError :=
  general_panel_bound 2 alleleFrequencySpectrum effectSizeStandardError
    ancestryFractionEstimate recombinationWindowRadius perGenerationMutationRate
    h_spectrum h_error
""")),
    # Two structure instances at DIFFERENT types share a field block. The fields
    # have different types there, so no definition returns both: the copy is
    # forced by Lean rather than chosen, and asking for it to be shared asks for
    # something that cannot be written.
    ("duplication", "a field block shared by instances of two different types",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure NarrowPanel where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ

structure WidePanel where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ
  extraBandwidthEstimate : ℝ

noncomputable def narrowWitness : NarrowPanel where
  ancestryFractionEstimate := 1 / 2
  recombinationWindowRadius := 3
  perGenerationMutationRate := 1 / 4
  residualVarianceEstimate := 1 / 8
  calibrationSlopeEstimate := 1

noncomputable def wideWitness : WidePanel where
  ancestryFractionEstimate := 1 / 2
  recombinationWindowRadius := 3
  perGenerationMutationRate := 1 / 4
  residualVarianceEstimate := 1 / 8
  calibrationSlopeEstimate := 1
  extraBandwidthEstimate := 2
""")),
    # Alike in nothing but the shape of their local names. Renaming locals before
    # comparing is what catches a renamed copy; it must not make every pair of
    # `intro`-and-`exact` proofs into a clone of every other.
    ("duplication", "two proofs alike only in the shape of their local names",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem shape_only_first (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have h1 : 0 ≤ a := ha
  have h2 : 0 ≤ b := hb
  have h3 : 0 ≤ a + b := add_nonneg h1 h2
  exact h3

theorem shape_only_second (p q : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ p * 1 + q := by
  have k1 : 0 ≤ p := hp
  have k2 : 0 ≤ q := hq
  have k3 : 0 ≤ p + q := add_nonneg k1 k2
  omega
""")),
    # Five lines, but only twice: below the short bar, which exists for runs that
    # repeat often rather than runs that repeat once.
    ("duplication", "a five-line block repeated only twice",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
structure PairPanelA where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ

structure PairPanelB where
  ancestryFractionEstimate : ℝ
  recombinationWindowRadius : ℕ
  perGenerationMutationRate : ℝ
  residualVarianceEstimate : ℝ
  calibrationSlopeEstimate : ℝ
""")),
    # A tactic macro names a tactic call.  It cannot change what a theorem says
    # and the proof still closes through the kernel; refusing it would push the
    # corpus to copy the lemma list at every use site instead.
    ("identifications", "a tactic macro naming a shared unfolding",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
macro "clean_rate_simp" : tactic =>
  `(tactic| simp [cleanRate])

theorem clean_rate_via_macro (x : ℝ) : cleanRate x = x := by
  clean_rate_simp
"""),
     "installs custom syntax"),
    # Long enough to clear the token floor and made entirely of closers: a reflex,
    # not a shared argument.
    #
    # The lemma list is long ON PURPOSE.  With a shorter one this fixture cleared
    # nothing: the pair fell under the ten-token floor and was accepted without the
    # reflex rule ever being consulted, so the rule could be -- and was -- broken by
    # the `by` that opens every tactic proof while this test went on passing.
    ("duplication", "two long proofs made only of closing tactics",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
theorem closers_only_first (m : CleanModel) : m.rate * 1 = m.rate := by
  simp [CleanModel.rate, mul_one, add_zero, sub_zero, one_mul, mul_zero, zero_add]
  norm_num

theorem closers_only_second (m : CleanModel) : m.rate + 0 = m.rate := by
  simp [CleanModel.rate, mul_one, add_zero, sub_zero, one_mul, mul_zero, zero_add]
  norm_num
""")),
    # A structure instance repeats the FIELD NAMES its structure declares, and a
    # `Prop`-valued structure with four fields is four goals whatever inhabits it.
    # The names are the shape, not a shared argument, and "name the repeated script
    # and apply it" has nothing to name: the corpus's four named operating points
    # were reported for agreeing that `norm_num` discharges a numeric bound.
    ("duplication", "two structure instances whose fields are all closers",
     clean_plus("Descent/Sub.lean", CLEAN_SUB + """
namespace Descent

/-- A Prop-valued structure: inhabiting it is inhabiting its fields. -/
structure CleanBounded (m : CleanModel) : Prop where
  rate_nonneg : 0 ≤ m.rate
  rate_le_one : m.rate ≤ 1

/-- One named point. -/
noncomputable def cleanFloor : CleanModel := ⟨0⟩

/-- Another named point. -/
noncomputable def cleanCeiling : CleanModel := ⟨1⟩

theorem cleanFloor_bounded : CleanBounded cleanFloor where
  rate_nonneg := by norm_num [cleanFloor, CleanModel.rate]
  rate_le_one := by norm_num [cleanFloor, CleanModel.rate]

theorem cleanCeiling_bounded : CleanBounded cleanCeiling where
  rate_nonneg := by norm_num [cleanCeiling, CleanModel.rate]
  rate_le_one := by norm_num [cleanCeiling, CleanModel.rate]

end Descent
""")),

    # --- conventions: the traps ------------------------------------------------
    # A complete ledger over a module that legitimately mixes conventions, with
    # the bridge present.  If this fired, the guard would be demanding that no
    # module ever discuss two estimators -- which would delete `Conventions.lean`,
    # the module whose entire job is relating them.
    ("conventions", "incompatible conventions coexisting WITH a bridge theorem",
     convention_corpus_files()),
    # `steppingStoneMeetingTime` contains the letters `gSt`.  A substring matcher
    # pulls it into the F_ST family and then demands a ledger entry declaring
    # which F_ST estimator a meeting time is, which is not a question. This is the
    # trap that decides between substring and camel-case-word matching.
    #
    # Asserted against a corpus where the guard IS reporting -- the `sampleNeiGst`
    # entry is withheld so the unledgered list is non-empty. On a silent run the
    # absence of a name proves nothing, because every name is absent.
    ("conventions", "a name merely CONTAINING the quantity's letters",
     convention_corpus_files(
         entries={k: v for k, v in CONVENTION_ENTRIES.items()
                  if not k.endswith("sampleNeiGst")}),
     "steppingStoneMeetingTime"),
    # `inherited` commits to no convention, so it can sit beside anything. A guard
    # that counted it as a third convention would report every module that carries
    # a retention factor.
    # A status head may carry qualifying words of its own -- `VALIDATED in its
    # slope`, `UNTESTED as a portability law`.  A rule that demanded an exact
    # match would report 40 of those, and the corpus would lose the qualifier
    # rather than the guard losing the rule.
    ("conventions", "a vocabulary term followed by its own qualifying words",
     convention_corpus_files(
         lean=CONVENTION_LEAN.replace("Empirical status: UNTESTED",
                                      "Empirical status: UNTESTED as a rate")),
     "status head"),
    # `MEASURED` is also ordinary English inside every evidence table. A rule
    # reading the whole status text rather than its head reported 99 of these,
    # none of them a defect.
    ("conventions", "a vocabulary word used as ordinary prose in the evidence",
     convention_corpus_files(
         lean=CONVENTION_LEAN.replace(
             "Empirical status: UNTESTED",
             "Empirical status: VALIDATED against measured 0.53 and derived 0.51")),
     "status head"),
    ("conventions", "an `inherited` entry beside a committed one",
     convention_corpus_files(
         entries={k: v for k, v in CONVENTION_ENTRIES.items()
                  if not k.endswith("sampleNeiGst")}
         | {"Descent/Sub.lean::sampleNeiGst": {
             "quantity": "fst", "convention": "inherited"}}),
     "declares incompatible"),
]


def calibrate_others() -> list:
    """Both directions for every guard that has a fixture. Returns failures."""
    failures = []

    # NEGATIVE, run once per guard: the clean fixture must satisfy all of them.
    # If this fails the positives below prove nothing, because a guard that
    # reports everything reports the planted defect too.
    for guard in ("style", "regimes", "closure", "wiring", "duplication"):
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

    # NEGATIVE, per planted trap: repetition that is idiom, an explicit tie, or
    # an accident of triviality must not be reported.
    # A trap may be written two ways. With no fourth element it asserts the guard
    # is SILENT, which is the strongest form and the right one for a guard whose
    # every screen the clean fixture satisfies. With one, it asserts that this
    # particular message is absent -- necessary for `identifications`, which runs
    # a dozen screens and whose isolated-module screen a two-module fixture
    # cannot satisfy at all. Demanding a clean exit there would assert something
    # about the fixture rather than about the rule under test.
    for case in NEGATIVE_CASES:
        guard, label, files = case[0], case[1], case[2]
        forbidden = case[3] if len(case) > 3 else None
        code, out = run_guard(guard, files)
        if forbidden is None:
            if code != 0:
                failures.append(
                    f"FALSE POSITIVE  {guard}: {label}\n"
                    + "\n".join("      " + l for l in out.strip().split("\n")[:12]))
        elif forbidden in out:
            failures.append(
                f"FALSE POSITIVE  {guard}: {label} -- reported as {forbidden!r}")

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
    for guard in ("style", "identifications", "duplication", "laundering",
                  "regimes", "closure", "wiring", "conventions", "field-proofs"):
        if guard not in r.stdout:
            failures.append(f"DISPATCH        --list does not name the {guard!r} guard")

    # `field-proofs` reads the corpus from `origin/main` rather than from a tree,
    # so DESCENT_CORPUS cannot reach it and not one planted defect above tests it.
    # Its only available control is this one -- that it looked at something -- and
    # it is not a formality: the guard filtered its file list on a `proofs/` prefix,
    # `5762501 Put the corpus at the root` deleted that directory, and from that
    # commit until the filter was repaired it scanned ZERO files and printed
    # `THEOREMS WHOSE WHOLE PROOF IS A FIELD PROJECTION: 0` on every run.  Every
    # other assertion in this file passed throughout: `--list` still named it, it
    # still exited 0, and its output still looked like a clean report.  A count of
    # files scanned is the one number that distinguishes a clean corpus from a
    # screen pointed at nothing.
    repo = CHECK.resolve().parents[2]
    r = subprocess.run([sys.executable, str(CHECK), "--only", "field-proofs"],
                       capture_output=True, text=True, cwd=repo)
    m = re.search(r"scanned (\d+) \.lean files", r.stdout)
    if not m:
        failures.append(
            "CONTRACT        field-proofs did not report how many files it scanned; "
            "that line is the guard's only evidence that it could see the corpus")
    elif int(m.group(1)) == 0:
        failures.append(
            "BLIND SPOT      field-proofs scanned 0 files and still reported a count; "
            "its path filter no longer matches where the corpus lives")

    # The other direction: pointed somewhere with no such ref, it must FAIL rather
    # than report zero findings.  This is `mathlib`'s rule -- a screen that cannot
    # look is not a screen that found nothing -- and it is what the repair added.
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(["git", "init", "-q"], cwd=td, capture_output=True)
        r = subprocess.run([sys.executable, str(CHECK), "--only", "field-proofs"],
                           capture_output=True, text=True, cwd=td)
        if r.returncode == 0:
            failures.append(
                "FALSE NEGATIVE  field-proofs passed in a repository with no "
                "`origin/main`, where it can have read nothing at all")
        elif "CANNOT RUN" not in r.stdout:
            failures.append(
                "MISREPORTED     field-proofs failed with no `origin/main`, but did "
                "not say it CANNOT RUN, which is what tells a reader it is not a finding")

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

    # False positives: clean mathematics must never gate the build.  No severity flag --
    # every severity gates now, so the harness checks the whole report the gate sees.
    for bad in sorted(families(run(NEGATIVE))):
        failures.append(f"FALSE POSITIVE  {bad} reported on clean mathematics")

    # The other seven guards, both directions, against fixture corpora.
    failures.extend(calibrate_others())

    # The ninth guard, which had no calibration at all until a mutation test
    # found that silencing it left this file green.
    failures.extend(calibrate_mathlib())

    for f in failures:
        print(f"FAIL  {f}")
    if failures:
        print(f"\n{len(failures)} calibration failure(s).  Until these pass the "
              f"detector's report is not evidence, in either direction.")
        return 1
    print("guard calibration PASSED")
    print(f"  laundering: {len(POSITIVE_EXPECTED)} planted patterns, each in the right family")
    print("  laundering: 0 findings at FATAL or CONDITIONAL severity on clean mathematics")
    guards_covered = sorted({guard for guard, *_ in CASES})
    print(f"  {'/'.join(guards_covered)}: {len(CASES)} planted defects reported, "
          f"clean fixture corpus accepted by style/regimes/closure/wiring/duplication")
    print(f"  {len(NEGATIVE_CASES)} traps -- idiom, an explicit tie, a trivial "
          f"coincidence, a specialisation, a type-forced field block and a tactic "
          f"macro -- each accepted")
    conv_pos = sum(1 for guard, *_ in CASES if guard == "conventions")
    conv_neg = sum(1 for case in NEGATIVE_CASES if case[0] == "conventions")
    print(f"  conventions: {conv_pos} planted ledger defects reported -- omission "
          f"by name and by ARGUMENT, staleness in an entry and in a bridge, "
          f"contradiction, a drifted constant in each table, a convention the "
          f"ledger never defines, one definition recorded twice, a record "
          f"pinning nothing, an absent ledger, and a status head both "
          f"miscased and unknown")
    print(f"  conventions: {conv_neg} traps accepted -- a bridged module, an "
          f"`inherited` neighbour, a name that merely CONTAINS the quantity's "
          f"letters, a status term carrying its own qualifier, and a vocabulary "
          f"word used as ordinary prose inside an evidence table")
    print("  wiring --json keys asserted by name; --list names all nine guards")
    print("  mathlib: a planted name collision reported and named, a corpus "
          "declaring only its own names accepted, and an absent Mathlib "
          "reported as CANNOT RUN rather than as a clean zero")
    print("  field-proofs: it reported the number of files it read and that "
          "number is not zero, and a repository with no `origin/main` is "
          "reported as CANNOT RUN rather than as a clean zero")
    return 0


if __name__ == "__main__":
    sys.exit(main())

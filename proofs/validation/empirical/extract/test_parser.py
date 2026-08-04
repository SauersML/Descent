"""Hand-verified ground truth for the parser and the translator.

Every expectation below was read off the Lean source by eye, then written here.
This is the one place hand transcription is allowed, because it is checking the
machinery rather than being trusted by it: if the parser drifts, these fail.

    python3 validation/extract/test_parser.py
"""
from __future__ import annotations

import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import lean_parse                                                # noqa: E402

PROOFS = lean_parse.find_proofs_root(HERE)

BLOB = json.loads((HERE / "defs.json").read_text())
BY_NAME = {d["name"]: d for d in BLOB["definitions"]}

failures = []

# An empty table passes every `d["field"] == want` assertion vacuously by never
# reaching one -- it raises KeyError on the first lookup instead, which reads as
# "the corpus renamed something" rather than "the extractor produced nothing".
# Say which happened, before any expectation runs.
if not BY_NAME:
    print("defs.json contains NO definitions: the extractor produced an empty "
          "table. Run emit.py and fix that first; nothing below is meaningful.",
          file=sys.stderr)
    sys.exit(1)


def _source_line_of(relpath, line, want_prefix):
    """Does 1-indexed `line` of the corpus file actually start that declaration?

    Anchors the parser's line attribution to the source rather than to a
    constant that any edit above the definition invalidates.
    """
    p = PROOFS / relpath
    if not p.exists():
        return f"source file {relpath} not found"
    lines = p.read_text(errors="ignore").splitlines()
    if not 1 <= line <= len(lines):
        return f"line {line} is outside {relpath} ({len(lines)} lines)"
    text = lines[line - 1]
    return want_prefix in text or f"got {text.strip()!r} at line {line}"


def check(label, got, want):
    if got != want:
        failures.append(f"{label}\n     got:  {got!r}\n     want: {want!r}")


def approx(label, got, want, tol=1e-12):
    if not (isinstance(got, float) and abs(got - want) <= tol * max(1.0, abs(want))):
        failures.append(f"{label}\n     got:  {got!r}\n     want: ~{want!r}")


# ---- PopulationGeneticsFoundations.lean, read by hand ---------------------

d = BY_NAME["Calibrator.neiFst"]
check("neiFst file", d["file"], "Calibrator/PopulationGeneticsFoundations.lean")
# The recorded line is checked against the SOURCE, not against a constant.  It
# used to be pinned at 42; every edit above the definition moved it, and the
# gate failed for a reason unrelated to what it tests ("got 46, want 42"), which
# is why prover.yml lists this file as excluded and currently failing.  What the
# assertion is actually for is that the parser attributes a declaration to the
# right line, and that is checkable without a magic number.
check("neiFst line points at its own `def` in the source",
      _source_line_of("Calibrator/PopulationGeneticsFoundations.lean",
                      d["line"], "def neiFst"), True)
check("neiFst noncomputable", d["noncomputable"], True)
check("neiFst args", [(a["names"], a["type"]) for a in d["args"]],
      [(["H_T", "H_S"], "ℝ")])
check("neiFst ret", d["ret_type"], "ℝ")
check("neiFst body", d["body"].strip(), "(H_T - H_S) / H_T")
# REPOINTED: this def has since been measured (battery_bulk25) and its
# docstring now records `Empirical status: **MEASURED, and NOT interchangeable
# with Hudson's F_ST**`. It read "" here for a different reason -- the status
# regex could not skip the markdown bold -- so this expectation was failing
# against a parser bug rather than against the corpus. Both are fixed; the
# assertion now pins the parsed value, which is what it was for.
check("neiFst empirical status", d["empirical_status"], "MEASURED")
check("neiFst dependents include the unit-interval theorem",
      "Calibrator.nei_fst_in_unit" in d["mentioned_by"], True)

# RENAMED from `simpleFst` (PopulationGeneticsFoundations.lean:56 records why:
# the old name asserted no estimator).  This gate is hand-read ground truth, so
# a rename in the Lean makes it fail with a KeyError -- which is correct
# behaviour, but it must then be REPOINTED, not left red.  A red ground-truth
# gate stops being read, and the next real parser regression lands behind it.
d = BY_NAME["Calibrator.neiGstFromFrequencies"]
check("neiGstFromFrequencies body (multi-line with let)", d["body"].strip(),
      "let p_bar := (p₁ + p₂) / 2\n  (p₁ - p₂) ^ 2 / (4 * p_bar * (1 - p_bar))")
check("neiGstFromFrequencies is mentioned by at least 4 theorems",
      len(d["mentioned_by"]) >= 4, True)

d = BY_NAME["Calibrator.coalFst"]
check("coalFst args", [n for a in d["args"] for n in a["names"]], ["t", "Ne"])
check("coalFst body", d["body"].strip(), "t / (t + 2 * Ne)")
# REPOINTED: `0 < t` left this set when `coal_fst_approaches_one` dropped it as
# a redundant premise -- it follows from `100 * Ne < t` with `0 < Ne`. The
# mined set tracks the theorems that mention the definition, so a premise
# removed upstream correctly disappears here. Repointed rather than left red,
# per the note above: a red ground-truth gate stops being read.
check("coalFst hypotheses mined", sorted(d["constraints"]["hypotheses"]),
      ["0 < Ne", "0 ≤ t", "100 * Ne < t"])

d = BY_NAME["Calibrator.expectedHeterozygosity"]
check("expectedHeterozygosity body", d["body"].strip(), "θ / (1 + θ)")
check("expectedHeterozygosity docstring mentions mutation-drift",
      "mutation-drift balance" in d["docstring"], True)

# equation-compiler definition (`def f : ℕ → ℝ | 0 => ... | t+1 => ...`)
d = BY_NAME["Calibrator.hetRecurrence"]
check("hetRecurrence equations", [e["pattern"] for e in d["equations"]],
      ["0", "t + 1"])
check("hetRecurrence base case", d["equations"][0]["rhs"], "H₀")
check("hetRecurrence step case", d["equations"][1]["rhs"],
      "(1 - 1 / (2 * Ne)) * hetRecurrence Ne H₀ t")

# ---- CovarianceStructure.lean: structure projection in a body ------------

d = BY_NAME["Calibrator.R2DecompositionData.calibration"]
check("projection body", d["body"].strip(), "d.varCondE / d.varYhat")
check("projection arg type", d["args"][0]["type"], "R2DecompositionData")
sd = [s for s in BLOB["structures"] if s["short"] == "R2DecompositionData"][0]
check("structure real fields",
      [f["name"] for f in sd["fields"] if f["type"] == "ℝ"],
      ["varY", "varYhat", "varCondE"])
check("structure invariant fields carried",
      "0 < varY" in [f["type"] for f in sd["fields"]], True)

# ---- the generated executable forms agree with hand evaluation ------------

import lean_defs                                                # noqa: E402


def evaluates(label, fq, args, want, tol=1e-12):
    """Hand-checked value, with a DELETED definition reported as deletion.

    Several agents edit this corpus continuously, so a name in this file can
    stop existing.  A bare `lean_defs.foo(...)` then raises AttributeError,
    which is indistinguishable from the extractor having broken -- and the
    difference is the whole verdict.  Look the name up first and say which
    happened.
    """
    if fq not in BY_NAME:
        print(f"  SKIP {label}: {fq} is no longer in the corpus "
              f"(deleted upstream, not an extraction failure)")
        return
    fn = getattr(lean_defs, fq.replace(".", "_"), None) \
        or getattr(lean_defs, fq.split(".")[-1], None)
    if fn is None:
        failures.append(f"{label}: {fq} is in the table but has no callable; "
                        f"if its short name became ambiguous this test must use "
                        f"the fully-qualified form")
        return
    approx(label, fn(*args), want, tol)


evaluates("neiFst(0.4, 0.3)", "Calibrator.neiFst", (0.4, 0.3), (0.4 - 0.3) / 0.4)
evaluates("simpleFst(0.2, 0.6)", "Calibrator.simpleFst", (0.2, 0.6),
          (0.2 - 0.6) ** 2 / (4 * 0.4 * (1 - 0.4)))
evaluates("coalFst(100, 1000)", "Calibrator.coalFst", (100.0, 1000.0),
          100 / (100 + 2000))
evaluates("expectedHeterozygosity(0.5)", "Calibrator.expectedHeterozygosity",
          (0.5,), 1 / 3)
evaluates("equilibriumFst(0.01, 1000)", "Calibrator.equilibriumFst",
          (0.01, 1000.0), 1 / (1 + 4 * 1000 * 0.01))

# Mathlib totality: these are exactly the cases a hand transcription gets wrong
approx("Lean division by zero is 0", lean_defs.neiFst(0.0, 0.0), 0.0)
approx("Real.sqrt of a negative is 0", __import__("lean_rt").rsqrt(-1.0), 0.0)
approx("Real.log 0 is 0", __import__("lean_rt").rlog(0.0), 0.0)
approx("Real.log of a negative is log|x|", __import__("lean_rt").rlog(-math.e), 1.0)

# ---- cross-validation against the independent leanexpr extraction ---------
#
# The strongest evidence either translator is correct.  `leanexpr` (in
# validation/differential/) was written separately from the same Lean sources
# and uses the OPPOSITE arithmetic convention (strict Python, raising where
# Mathlib returns 0).  Agreement at every point means a transcription error
# would have to be the same error in both.
#
# Two failure modes are asserted against, per differential's advice:
#   - any disagreement, and
#   - any DROP in how many definitions are compared.  A definition quietly
#     leaving the comparison is how the hetDecayFactor overload bug hid.

CROSSVALIDATE_FLOOR = 40
# 43 -> 40 is NOT a regression. Four definitions in the battery take
# `Fin n -> R` or matrix arguments, which the independent translator refuses
# by design rather than guessing: cumulativeDrift, heterozygosityLossVariableNe,
# harmonicMeanNe, ldMismatchFrobenius. They are extractable by THIS tier
# alone and have no independent check, so if the vector evaluator is wrong
# about them nothing in this project would catch it. Raise this when the
# battery grows; lower it only with a recorded reason like this one.

def cross_validate():
    diffdir = str(HERE.parent / "differential")
    if not pathlib.Path(diffdir, "crossvalidate.py").exists():
        print("cross-validation: harness absent, skipped")
        return
    sys.path.insert(0, diffdir)
    try:
        import crossvalidate
        import corpus
    except Exception as e:                                       # noqa: BLE001
        print(f"cross-validation: could not import harness ({e!r}), skipped")
        return
    battery = getattr(crossvalidate, "battery_points", None)
    points = battery() if callable(battery) else getattr(
        corpus, "CROSSCHECK_POINTS", None)
    if not points:
        print("cross-validation: harness exposes no argument tuples, skipped")
        return
    names = getattr(crossvalidate, "battery_names", None)
    names = names() if callable(names) else list(points)
    agree, disagree, unavailable = crossvalidate.compare(names, points)
    n = len(agree)
    print(f"cross-validated against leanexpr: {n} definitions, "
          f"{sum(a[2] for a in agree)} points, {len(disagree)} disagreements")
    if disagree:
        for row in disagree[:5]:
            failures.append(f"cross-validation disagreement: {row}")
    if n < CROSSVALIDATE_FLOOR:
        failures.append(
            f"cross-validated definition count DROPPED to {n}, floor is "
            f"{CROSSVALIDATE_FLOOR}. A definition leaving the comparison is as "
            f"serious as a disagreement -- check for a name that stopped "
            f"resolving. unavailable={unavailable[:5]}")


cross_validate()


# ---- recall ---------------------------------------------------------------

import re                                                       # noqa: E402

grep = 0
# The root `proofs/Calibrator.lean` is a sibling of Calibrator/, not a child, so
# `rglob` misses it. See lean_parse.build's `extra` idiom.
import lean_parse                                             # noqa: E402

_PROOFS = lean_parse.find_proofs_root(HERE)
_lean_paths = sorted((_PROOFS / "Calibrator").rglob("*.lean"))
if (_PROOFS / "Calibrator.lean").exists():
    _lean_paths.append(_PROOFS / "Calibrator.lean")
for p in _lean_paths:
    for line in p.read_text(errors="ignore").splitlines():
        if re.match(r"^(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev)\s+\S",
                    line):
            grep += 1
print(f"grep-visible def/abbrev lines : {grep}")
print(f"definitions in the table      : {len(BLOB['definitions'])}")
print(f"declarations the parser failed: {len(BLOB['parse_failures'])}")

if failures:
    print(f"\n{len(failures)} HAND-CHECK FAILURES:")
    for f in failures:
        print("  " + f)
    sys.exit(1)
print("\nall hand-verified expectations hold")

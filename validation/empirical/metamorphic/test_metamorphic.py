#!/usr/bin/env python3
"""CALIBRATION of the metamorphic gate, in both directions.

    python3 validation/empirical/metamorphic/test_metamorphic.py

A detector that reports nothing is indistinguishable from a clean corpus, so
run.py's silence is not evidence until both directions are asserted:

  POSITIVE  every planted defect must be caught, one per relation kind, so a
            relation kind that silently stopped evaluating is detected.  The
            plants are the defect classes this instrument exists for: an
            allele-relabelling asymmetry, a wrong scaling exponent, an argument
            asymmetry, an ORDER dependence, and a cancellation that destroys the
            answer.
  NEGATIVE  the real corpus bodies must produce zero findings at gating
            severity, and each planted defect must be caught by the relation
            that names it and NOT by the others -- a detector that fires on
            everything is as useless as one that fires on nothing.

This runs BEFORE run.py in CI, for the same reason test_check.py runs before
check.py and test_identity_gate.py runs before the differential battery.  It
uses stub bodies only: no Lean, no generated table, well under a second.
"""

import sys
import os
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
# The workflow-path guard now lives with the other repo-generic checks under
# validation/code/; its Rust-build-flag siblings left with gnomon.
sys.path.insert(0, os.path.join(HERE, "..", "..", "code"))
sys.path.insert(0, HERE)

import relations as R      # noqa: E402
import run as G            # noqa: E402

FAILURES = []


def expect(condition, message):
    if not condition:
        FAILURES.append(message)


def check(fn, argnames, rel):
    return G.check_relation("<stub>", rel, fn, argnames)


# ---------------------------------------------------------------------------
# NEGATIVE DIRECTION: correct bodies must produce no findings.
# ---------------------------------------------------------------------------

def correct_hudson(p1, p2):
    return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))


def correct_ncp(n, b):
    return n * b ** 2


def correct_coal_fst(t, ne):
    return t / (t + 2 * ne)


def negative_direction():
    expect(not check(correct_hudson, ["p1", "p2"],
                     R.invariant_under_allele_swap(["p1", "p2"])),
           "clean Hudson F_ST was reported as violating allele-swap invariance")
    expect(not check(correct_hudson, ["p1", "p2"],
                     R.symmetric_in("p1", "p2")),
           "clean Hudson F_ST was reported as asymmetric in its populations")
    expect(not check(correct_ncp, ["n", "b"], R.scales("b", 2)),
           "clean NCP was reported as violating its quadratic effect scaling")
    expect(not check(correct_ncp, ["n", "b"], R.scales("n", 1)),
           "clean NCP was reported as violating its linear sample scaling")
    expect(not check(correct_coal_fst, ["t", "ne"],
                     R.jointly_scales(["t", "ne"], 0)),
           "clean coalescent F_ST was reported as not rescaling-invariant")
    # The two relation kinds that had no plant, in the clean direction too.
    expect(not check(lambda b, w: b * w, ["b", "w"], R.odd_under_negation(["b"])),
           "a body genuinely odd in its effect size was reported as violating "
           "odd-under-negation")
    # `t -> c*t, Ne -> Ne/c` leaves the PRODUCT alone, not the ratio, so the
    # clean body here is a function of `t * Ne` -- the scaled-time parameter
    # the corpus's reciprocal declarations are about.
    expect(not check(lambda t, ne: (t * ne) / (t * ne + 2), ["t", "ne"],
                     R.invariant_under_reciprocal_scaling(["t"], ["ne"])),
           "a body genuinely invariant under reciprocal rescaling was reported "
           "as violating it")


# ---------------------------------------------------------------------------
# POSITIVE DIRECTION: planted defects, one per relation kind.
# ---------------------------------------------------------------------------

def planted_allele_asymmetry(p1, p2):
    """Uses p1 raw where the correct body uses the symmetric combination, so
    relabelling the reference allele moves the answer. This is the shape of a
    body that reads the assembly instead of the biology."""
    return (p1 - p2) ** 2 / (p1 + p2 - 2 * p1 * p2) + p1 / 1000


def planted_wrong_exponent(n, b):
    """Linear in the effect size where the noncentrality parameter is quadratic.
    Monotone in b, so every monotonicity theorem in the corpus still passes."""
    return n * abs(b)


def planted_argument_asymmetry(p1, p2):
    """Antisymmetric in the two populations, so which one is named first moves
    the answer -- but built from `(p1-p2)(p1+p2-1)`, which IS invariant under
    the allele swap. That combination is deliberate: it lets the specificity
    assertion below distinguish the two relations instead of conflating them.
    A plant that broke both would prove nothing about localisation."""
    return ((p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))
            + Q(1, 100) * (p1 - p2) * (p1 + p2 - 1))


def planted_broken_rescaling(t, ne):
    """Drops the factor that makes time dimensionless, so the answer depends on
    the unit in which time is measured."""
    return t / (t + 2)


def planted_order_dependence(p1, p2):
    """Order dependence, made visible through argument exchange: the body
    returns a different number depending on which population is passed first,
    which is exactly what a sample-order-sensitive estimator does."""
    return p1 * 0.75 + p2 * 0.25


def planted_even_not_odd(b, w):
    """Declared ODD in its effect sizes and actually EVEN in one of them: the
    shape of a body that squared a signed effect somewhere it should not have,
    so flipping the sign of every allele's effect no longer flips the score.

    `negate` was one of two relation KINDS with 37 and 20 real declarations
    between them and no planted defect anywhere -- the transform and the
    expected-value arm for both had only ever been observed silent, which is
    indistinguishable from being unable to fire."""
    return b * b * w


def planted_lost_reciprocal(t, ne):
    """Declared invariant under `t -> c*t, Ne -> Ne/c` and actually a function
    of `t` alone: the scaled-time parameter has come apart from the pair it is
    built out of. Same defect class as `planted_broken_rescaling`, but through
    the `reciprocal_scale` transform, which multiplies one argument and divides
    the other rather than scaling both."""
    return t / (t + 2)


def planted_cancellation(h_t, h_s):
    """A ratio written so the units do NOT cancel: multiplying both
    heterozygosities by a common factor moves the answer, which is the signature
    of a body that lost a normalisation."""
    return (h_t - h_s) / (h_t * h_t)


def positive_direction():
    plants = [
        ("allele relabelling asymmetry", planted_allele_asymmetry,
         ["p1", "p2"], R.invariant_under_allele_swap(["p1", "p2"])),
        ("wrong scaling exponent", planted_wrong_exponent,
         ["n", "b"], R.scales("b", 2)),
        ("argument asymmetry", planted_argument_asymmetry,
         ["p1", "p2"], R.symmetric_in("p1", "p2")),
        ("broken coalescent rescaling", planted_broken_rescaling,
         ["t", "ne"], R.jointly_scales(["t", "ne"], 0)),
        ("order dependence", planted_order_dependence,
         ["p1", "p2"], R.symmetric_in("p1", "p2")),
        ("lost normalisation / cancellation", planted_cancellation,
         ["h_t", "h_s"], R.jointly_scales(["h_t", "h_s"], 0)),
        ("even where the corpus declares odd", planted_even_not_odd,
         ["b", "w"], R.odd_under_negation(["b"])),
        ("lost reciprocal pairing", planted_lost_reciprocal,
         ["t", "ne"], R.invariant_under_reciprocal_scaling(["t"], ["ne"])),
    ]
    for label, fn, args, rel in plants:
        expect(bool(check(fn, args, rel)),
               f"PLANTED DEFECT NOT CAUGHT: {label} "
               f"({rel['id']}) passed the gate")


# ---------------------------------------------------------------------------
# SPECIFICITY: a planted defect must be caught by the relation that names it,
# and the OTHER relations of the same body must still pass. A detector that
# fires on everything cannot localise anything.
# ---------------------------------------------------------------------------

def specificity():
    # planted_wrong_exponent breaks the effect exponent but keeps the sample
    # one, so scales("n", 1) must still hold.
    expect(not check(planted_wrong_exponent, ["n", "b"], R.scales("n", 1)),
           "the wrong-effect-exponent plant was also reported against the "
           "sample-size scaling it does not break; the gate cannot localise")
    # planted_argument_asymmetry keeps allele-swap invariance.
    expect(not check(planted_argument_asymmetry, ["p1", "p2"],
                     R.invariant_under_allele_swap(["p1", "p2"])),
           "the argument-asymmetry plant was also reported against allele-swap "
           "invariance, which it does not break")


# ---------------------------------------------------------------------------
# The table's own integrity: pinned violations must name relations that the
# table actually declares, or the pin is decoration.
# ---------------------------------------------------------------------------

class _FakeRelations:
    """A minimal stand-in for relations.py, so the gate's TABLE-level checks can
    be driven with inputs the real corpus can never produce."""
    SWEPT_MODULES = ("Fake/Mod.lean",)
    RELATIONS = {"Fake.f": [R.scales("x", 2)]}
    NO_RELATIONS = {}
    NOT_EXTRACTABLE = {}
    EXPECTED_VIOLATIONS = {}
    AGREEMENTS = ()


def _entry(module="Fake/Mod.lean", args=("x",)):
    return {"ret_type": "ℝ", "file": module,
            "args": [{"names": [a], "type": "ℝ", "implicit": False}
                     for a in args]}


def broken_table_is_not_silent():
    """THE SAFE-REGION CHECK. Everything else in this file drives the gate with
    stub BODIES, which exercises the relation arithmetic and nothing else. The
    gate's real input is a generated definition table, and a table that failed to
    build is the failure mode with no signature of its own: every downstream
    check goes quiet because there is nothing left to disagree with. Silence
    there is indistinguishable from a clean corpus, so it must be asserted
    against directly."""
    def never(_name):
        raise AssertionError("callable_for must not be reached for a missing def")

    findings, checked, agreed, _ = G.analyse({}, never, _FakeRelations)
    expect(findings,
           "AN EMPTY DEFINITION TABLE PRODUCED NO FINDINGS. A failed extraction "
           "would pass this gate silently, and every number it prints would be "
           "about a table that does not describe the corpus.")
    expect(any("EXTRACTION COLLAPSED" in f for f in findings),
           "an empty table was not diagnosed as a collapsed extraction; the "
           "operator would chase the downstream symptoms instead")
    expect(checked == 0,
           "the gate reported checking relations against an empty table")

    # A table that is plausible in size but has lost the declared definitions:
    # the DANGLING check must carry it, not the size floor.
    big = {f"Filler.d{i}": _entry("Other/Mod.lean") for i in range(600)}
    findings2, _, _, _ = G.analyse(big, never, _FakeRelations)
    expect(any("DANGLING" in f for f in findings2),
           "a large table missing every declared definition produced no "
           "DANGLING finding; a rename sweep would pass unnoticed")
    expect(not any("EXTRACTION COLLAPSED" in f for f in findings2),
           "the size floor fired on a plausibly sized table; it would mask the "
           "more specific diagnosis")


def coverage_check_fires():
    """The coverage gate -- a new in-scope def in a swept module with no
    declaration -- has only ever been exercised by real corpus data, which is to
    say only on input where it happened not to fire. Drive it directly."""
    def resolver(_name):
        return (lambda x: x * x), ["x"]

    table = {"Fake.f": _entry(), "Fake.newcomer": _entry()}
    findings, _, _, _ = G.analyse(table, resolver, _FakeRelations)
    expect(any("UNDECLARED" in f and "newcomer" in f for f in findings),
           "COVERAGE CHECK DID NOT FIRE: a new in-scope definition in a swept "
           "module with no declaration was accepted. The coverage claim is "
           "unfounded.")
    # ... and must NOT fire on the declared one.
    expect(not any("UNDECLARED" in f and "Fake.f" in f for f in findings),
           "the coverage check flagged a definition that IS declared")

    # A swept module that contributes nothing must be reported, or a renamed
    # module silently reduces coverage to zero while the gate stays green.
    findings2, _, _, _ = G.analyse({"Other.g": _entry("Other/Mod.lean")},
                                   resolver, _FakeRelations)
    expect(any("EMPTY SWEEP" in f for f in findings2),
           "a swept module contributing no definitions was not reported; a "
           "module rename would silently empty the sweep")


def vacuity_screen_fires():
    """A constant transcription satisfies every INVARIANCE relation vacuously.
    Without a non-degeneracy screen a definition declared only with invariances
    passes even when its body has collapsed."""
    class OnlyInvariances(_FakeRelations):
        RELATIONS = {"Fake.f": [R.symmetric_in("x", "y")]}

    table = {"Fake.f": _entry(args=("x", "y"))}
    collapsed = (lambda x, y: 1.0), ["x", "y"]
    findings, _, _, _ = G.analyse(table, lambda _n: collapsed, OnlyInvariances)
    expect(any("VACUOUS" in f for f in findings),
           "A COLLAPSED (CONSTANT) TRANSCRIPTION PASSED. Every invariance "
           "relation holds for a constant, so without this screen the gate "
           "certifies a body that computes nothing.")

    live = (lambda x, y: x * y), ["x", "y"]
    findings2, _, _, _ = G.analyse(table, lambda _n: live, OnlyInvariances)
    expect(not any("VACUOUS" in f for f in findings2),
           "the vacuity screen fired on a genuinely varying body")


def unevaluatable_is_not_agreement():
    """A body that cannot be EVALUATED must not be scored as satisfying its
    relations.

    `check_relation` skips a ZeroDivisionError rather than reporting it, which
    is right for an isolated pole and wrong for a body that raises across the
    whole grid: the failure list comes back empty and the caller reads that as
    "the relation holds". `constant_on_grid` does not cover the case either --
    it skips the same exceptions and returns False when fewer than two points
    evaluated. Measured before the fix: a body raising at every grid point
    passed both a `swap` and a `scale` relation with `checked=2`, and a pair of
    such bodies passed a proved cross-body equality with `agreed=1`.

    Both directions, because the skip itself is load-bearing: a body with ONE
    pole on the grid must still be checked on the rest and must still be caught
    when it violates there.
    """
    def entry(module="Fake/Mod.lean", args=("x", "y")):
        return {"ret_type": "ℝ", "file": module,
                "args": [{"names": [a], "type": "ℝ", "implicit": False}
                         for a in args]}

    class Rels(_FakeRelations):
        SWEPT_MODULES = ()
        RELATIONS = {"Fake.f": [R.symmetric_in("x", "y")]}

    table = {"Fake.f": entry()}
    table.update({f"Filler.d{i}": entry("Other/Mod.lean") for i in range(600)})

    def nowhere(_x, _y):
        raise ZeroDivisionError("planted: undefined on the whole grid")

    findings, _, _, _ = G.analyse(table, lambda _n: (nowhere, ["x", "y"]), Rels)
    expect(any("UNEVALUATED" in f and "Fake.f" in f for f in findings),
           "A BODY THAT RAISES AT EVERY GRID POINT WAS SCORED AS SATISFYING "
           "ITS RELATIONS. An unevaluatable transcription is indistinguishable "
           "here from a correct one.")

    # NEGATIVE: an isolated pole must still be skipped, and the rest of the
    # grid still checked. GRID_POINTS[0] is 3/10; this body is undefined there
    # and asymmetric everywhere else, so it must be VIOLATED, not UNEVALUATED.
    def one_pole(x, y):
        if x == float(G.GRID_POINTS[0]):
            raise ZeroDivisionError("planted: one pole")
        return 0.75 * x + 0.25 * y

    findings2, _, _, _ = G.analyse(table, lambda _n: (one_pole, ["x", "y"]), Rels)
    expect(any("VIOLATED" in f and "Fake.f" in f for f in findings2),
           "a body with a single pole on the grid was not checked on the rest "
           "of it; the skip has swallowed the whole relation")
    expect(not any("UNEVALUATED" in f for f in findings2),
           "a body evaluable at seven of eight grid points was reported as "
           "unevaluated; the floor is placed wrong")

    # The same failure at the cross-body agreement tier, where the count that
    # gets printed is `agreed`.
    class AgreeRels(_FakeRelations):
        SWEPT_MODULES = ()
        RELATIONS = {}
        AGREEMENTS = (("Fake.left", "Fake.right", "Descent.stub_agreement",
                       "a stub agreement whose note is long enough to satisfy "
                       "the substantive-reason rule asserted elsewhere in this "
                       "file"),)

    pair = {"Fake.left": entry(), "Fake.right": entry()}
    pair.update({f"Filler.d{i}": entry("Other/Mod.lean") for i in range(600)})
    fns = {"Fake.left": nowhere, "Fake.right": nowhere}
    findings3, _, agreed, _ = G.analyse(
        pair, lambda n: (fns[n], ["x", "y"]), AgreeRels)
    expect(any("UNEVALUATED AGREEMENT" in f for f in findings3),
           f"A PROVED EQUALITY WHOSE TWO SIDES BOTH RAISE EVERYWHERE WAS "
           f"COUNTED AS EXECUTED (agreed={agreed}) WITHOUT BEING EXECUTED.")

    live = {"Fake.left": lambda x, y: x + y, "Fake.right": lambda x, y: x + y}
    findings4, _, _, _ = G.analyse(
        pair, lambda n: (live[n], ["x", "y"]), AgreeRels)
    expect(not any("UNEVALUATED AGREEMENT" in f for f in findings4),
           "two genuinely agreeing bodies were reported as unevaluated")


def workflow_path_extraction():
    """Both directions for the workflow-path guard in workflow_paths.py.

    POSITIVE: a path in a `run:` block must be extracted, including through a
    `working-directory`, or the guard cannot see the break it exists for.
    NEGATIVE: a path named only in PROSE must NOT be extracted. prover.yml's
    "WHAT IS NOT WIRED UP" section lists a dozen scripts it deliberately does not
    run; a guard that flagged those would fire on the comment explaining why they
    are excluded, which is the fastest way to get a required check ignored.
    """
    import workflow_paths as B

    sample = """
jobs:
  prove:
    steps:
      - name: Install
        run: curl https://example.com/install.sh -sSf | sh -s -- -y
      - name: Direct
        run: python3 validation/code/check.py
      - name: With a working directory
        working-directory: validation/empirical/differential
        run: python3 run.py
      - name: Multi-line
        run: |
          python3 first.py
          python3 dir/second.py
      # PROSE: empirical/invariants/vacuity.py is 60s and stays out, and
      # extract/xcheck_vector.py needs numpy. Neither is run.
      - name: Last
        run: lake env lean validation/code/Check.lean
"""
    found = B.workflow_run_paths(sample)
    for want in ("validation/code/check.py",
                 "validation/empirical/differential/run.py",
                 "dir/second.py",
                 "validation/code/Check.lean"):
        expect(want in found,
               f"workflow-path guard missed {want!r}, which IS executed; it "
               f"cannot catch a step whose script is untracked")
    for unwanted in ("empirical/invariants/vacuity.py",
                     "extract/xcheck_vector.py"):
        expect(unwanted not in found,
               f"workflow-path guard extracted {unwanted!r} from a COMMENT; it "
               f"would fire on the prose explaining why that script is excluded")
    expect(not any("example.com" in p or p.startswith("//") for p in found),
           "workflow-path guard extracted a URL as if it were a repo file")


def agreements_integrity():
    """The cross-body agreement list must name real theorems and real reasons,
    and must not pair a definition with itself -- which would pass always and
    check nothing."""
    for entry in getattr(R, "AGREEMENTS", ()):
        left, right, theorem, note = entry[:4]
        order = entry[4] if len(entry) > 4 else None
        expect(left != right,
               f"AGREEMENT pairs {left} with itself; it can never fail")
        # Either it names a Lean theorem, or it says explicitly that no theorem
        # relates the pair -- a recorded FORK. What must not happen is a blank
        # or a vague field, which would read as a proof that does not exist.
        expect(("." in theorem and len(theorem) > 8)
               or theorem.startswith("NO THEOREM RELATES THESE"),
               f"AGREEMENT {left} vs {right} names neither a Lean theorem nor "
               f"an explicit absence ({theorem!r}); an executed equality must "
               f"say whether it is executing a proof or recording a fork")
        expect(len(note) > 40,
               f"AGREEMENT {left} vs {right} has no substantive note")
        expect(order is None
               or sorted(order) == list(range(len(order))),
               f"AGREEMENT {left} vs {right} has argument order {order}, which "
               f"is not a permutation")


def no_stale_excuses():
    """NOT_EXTRACTABLE must not be used as a parking space. Every entry needs a
    reason as substantive as a NO_RELATIONS one, because the two are the same
    claim -- 'this definition is not covered, and here is why that is not
    negligence'."""
    for fqn, reason in R.NOT_EXTRACTABLE.items():
        expect(len(reason) > 40,
               f"NOT_EXTRACTABLE[{fqn}] has no substantive reason")


def table_integrity():
    declared_ids = {(fqn, rel["id"])
                    for fqn, rels in R.RELATIONS.items() for rel in rels}
    for key in R.EXPECTED_VIOLATIONS:
        expect(key in declared_ids,
               f"PINNED VIOLATION {key} names a relation that is not declared "
               f"in RELATIONS; the pin can never fire.")
    overlap = set(R.RELATIONS) & set(R.NO_RELATIONS)
    expect(not overlap,
           f"{sorted(overlap)} appear in both RELATIONS and NO_RELATIONS")
    for fqn, reason in R.NO_RELATIONS.items():
        expect(len(reason) > 40,
               f"NO_RELATIONS[{fqn}] has no substantive reason; "
               f"'nobody looked' and 'none applies' must not be confusable")


def calib_tail():
    """CALIB-TAIL: a probe that must FAIL, run LAST and over the END of the real
    inputs, so that silence here voids the run.

    A calibration certifies an instrument only over the region it occupies. Every
    other probe in this file sits at the head of its input -- small stub bodies,
    short synthetic tables, a five-step sample workflow -- which is exactly where
    truncation, output caps and early loop exits cannot reach. These two probes
    live at the tail of the real inputs instead.
    """
    # (a) The real prover.yml. If the parser ever stopped early -- at the first
    #     comment block, at a step limit, at the "WHAT IS NOT WIRED UP" prose --
    #     the paths it names would vanish from the extraction and the guard would
    #     report nothing. Assert that a path from the LAST run: step is present.
    import workflow_paths as B
    import os
    wf = os.path.join(B.ROOT, ".github", "workflows", "prover.yml")
    if os.path.exists(wf):
        with open(wf, encoding="utf-8") as handle:
            text = handle.read()
        found = B.workflow_run_paths(text)
        expect(found,
               "CALIB-TAIL: the workflow-path parser extracted NOTHING from the "
               "real prover.yml. It is structurally unable to see any break.")
        # The last `run:` line in the file that names a repo script.
        last = None
        for raw in text.splitlines():
            s = raw.strip()
            if s.startswith("#") or "run:" not in s:
                continue
            for tok in B.re.findall(r"[\w./-]+\.(?:py|sh|lean|toml)\b", s):
                if "/" in tok and "://" not in s:
                    last = tok
        expect(last is None or any(p.endswith(last) for p in found),
               f"CALIB-TAIL: the LAST script named by a run: step in the real "
               f"prover.yml ({last!r}) is missing from the parser's output, so "
               f"the parser stops before the end of the file. Everything it "
               f"reports is about the head of the workflow only.")

    # (b) The relation table. A probe placed after every real declaration: if
    #     anything ever iterates only a prefix of RELATIONS, this synthetic entry
    #     appended conceptually at the end must still be reached. It is declared
    #     to VIOLATE, so a silent skip reads as a pass and is caught here.
    class TailProbe(_FakeRelations):
        SWEPT_MODULES = ()
        RELATIONS = dict(list(R.RELATIONS.items())
                         + [("ZZZ.tailProbe", [R.scales("x", 2)])])
        NO_RELATIONS = R.NO_RELATIONS
        NOT_EXTRACTABLE = R.NOT_EXTRACTABLE
        EXPECTED_VIOLATIONS = {}
        AGREEMENTS = ()

    table = {name: _entry("Fake/Mod.lean") for name in TailProbe.RELATIONS}
    table.update({n: _entry("Fake/Mod.lean") for n in TailProbe.NO_RELATIONS})
    table.update({n: _entry("Fake/Mod.lean") for n in TailProbe.NOT_EXTRACTABLE})
    table.update({f"Filler.d{i}": _entry("Other/Mod.lean") for i in range(600)})

    def linear(_name):
        return (lambda *a: sum(a)), ["x"]          # linear: violates scale x^2

    findings, _, _, _ = G.analyse(table, linear, TailProbe)
    expect(any("ZZZ.tailProbe" in f for f in findings),
           "CALIB-TAIL: the probe declared LAST in the relation table was not "
           "reported, although it is declared to violate its relation. The gate "
           "does not reach the end of the table, so every entry after the cut "
           "is being scored as passing.")

    # (c) The unevaluatable-body floor, placed at the tail of the real table as
    #     well. `analyse` sorts RELATIONS, so this name is reached last; a
    #     failure that only ever fires on a short synthetic table would not be
    #     evidence about the run CI performs.
    def nowhere(*_a):
        raise ZeroDivisionError("planted: undefined on the whole grid")

    findings2, _, _, _ = G.analyse(
        table, lambda name: ((nowhere, ["x"]) if name == "ZZZ.tailProbe"
                             else (lambda *a: sum(a), ["x"])), TailProbe)
    expect(any("UNEVALUATED" in f and "ZZZ.tailProbe" in f for f in findings2),
           "CALIB-TAIL: a body that raises at every grid point, declared LAST "
           "in the real relation table, was scored as satisfying its relation.")


def main():
    negative_direction()
    positive_direction()
    specificity()
    table_integrity()
    agreements_integrity()
    no_stale_excuses()
    unevaluatable_is_not_agreement()
    workflow_path_extraction()
    broken_table_is_not_silent()
    coverage_check_fires()
    vacuity_screen_fires()
    calib_tail()
    if FAILURES:
        print(f"metamorphic gate calibration FAILED ({len(FAILURES)}):\n")
        for f in FAILURES:
            print("  " + f)
        return 1
    print("metamorphic gate calibration passed: 8 planted defects all caught, "
          "5 clean bodies all silent, specificity holds, table integrity, "
          f"{len(getattr(R, 'AGREEMENTS', ()))} cross-body agreements "
          "well-formed, no stale excuses; and the table-level probes -- empty "
          "extraction diagnosed rather than silent, coverage check fires on an "
          "undeclared def, empty sweep reported, vacuity screen catches a "
          "collapsed body, a body that raises across the whole grid is "
          "UNEVALUATED rather than satisfied while a single pole is still "
          "skipped, every forbidden build flag is reported and the scan reaches "
          "subdirectory crates, CALIB-TAIL reaches the end of both the relation "
          "table and the real prover.yml.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

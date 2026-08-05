"""Calibration for map_check.py, in BOTH directions.

A detector that reports nothing is indistinguishable from a verified
correspondence, which is the failure mode this whole lane exists to catch: the
executable correctability contract was a required CI step that could not compile
for as long as it had existed, and it looked exactly like a passing check.

So this asserts two things:

  * the real tree produces ZERO findings, and
  * each of seven planted defects -- one per finding class, plus the empty-corpus
    case -- is reported.

Each planted defect is a minimal, one-place change: a single character in a Lean
transcription, a single character in a Rust body, one renamed declaration, one
extra guard call.  If a bigger perturbation were needed to make the check fire,
the check would not be sensitive enough to catch a real convention error.

Run:  python3 test_map_check.py
"""

import copy
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import lean_bodies  # noqa: E402
import map_check  # noqa: E402

FAILURES = []


def expect(condition, message):
    if not condition:
        FAILURES.append(message)
    print(f"  {'ok  ' if condition else 'FAIL'}  {message}")


def kinds(results):
    return sorted({kind for kind, _, _ in results})


def main():
    print("CALIBRATION: the clean tree must be silent")
    clean = map_check.load_sources()
    baseline = map_check.findings(clean)
    expect(baseline == [],
           f"clean tree yields no findings (got {len(baseline)}: {kinds(baseline)})")

    print()
    print("CALIBRATION: each planted defect must be caught")

    # 1. CODE-STALE: one character of a mapped Rust body.
    mutated = copy.deepcopy(clean)
    path = "map/correctability.rs"
    text = mutated["code_text"][path]
    needle = "input.subgroup_size * (input.sample_size - input.subgroup_size)"
    assert needle in text, "the anchor for the CODE-STALE mutation is gone; re-pick it"
    mutated["code_text"][path] = text.replace(
        needle, "input.subgroup_size * (input.sample_size + input.subgroup_size)", 1)
    result = map_check.findings(mutated)
    expect("CODE-STALE" in kinds(result),
           f"a one-character change to effective_subgroup_size is CODE-STALE "
           f"(got {kinds(result)})")

    # 2. CODE-MISSING: a mapped function that no longer exists under that name.
    mutated = copy.deepcopy(clean)
    mutated["code_text"][path] = mutated["code_text"][path].replace(
        "fn require_finite_positive", "fn require_finite_positive_renamed", 1)
    result = map_check.findings(mutated)
    expect("CODE-MISSING" in kinds(result),
           f"a renamed mapped function is CODE-MISSING (got {kinds(result)})")

    # 3. GUARD-SURFACE: a new numerical guard inside a mapped body.
    mutated = copy.deepcopy(clean)
    mutated["code_text"][path] = mutated["code_text"][path].replace(
        "let residual_axis_fraction = 1.0 - removed_axis_fraction;",
        "let residual_axis_fraction = (1.0 - removed_axis_fraction).clamp(0.0, 1.0);", 1)
    result = map_check.findings(mutated)
    expect({"GUARD-SURFACE", "CODE-STALE"} <= set(kinds(result)),
           f"a newly introduced clamp in mapped code is GUARD-SURFACE "
           f"(got {kinds(result)})")

    # 4. CORPUS-MISSING: a mapped Lean declaration that is no longer there.
    mutated = copy.deepcopy(clean)
    mutated["corpus"].pop("Calibrator.demographicSpike", None)
    result = map_check.findings(mutated)
    expect("CORPUS-MISSING" in kinds(result),
           f"a deleted mapped Lean declaration is CORPUS-MISSING (got {kinds(result)})")

    # 5. CORPUS-STALE: a mapped Lean body that changed.
    mutated = copy.deepcopy(clean)
    mutated["corpus"]["Calibrator.samplePCOverlapSq"] = "sha256:" + "0" * 32
    result = map_check.findings(mutated)
    expect("CORPUS-STALE" in kinds(result),
           f"an edited mapped Lean body is CORPUS-STALE (got {kinds(result)})")

    # 6. REFPOINT and EXPECTED-STALE: one character of a Lean transcription.
    #    This is the mutation that matters most. The corpus's own reference
    #    points did NOT catch the analogous spike-constant error, because they
    #    were evaluated where the body collapses; the fixture grid did.
    original = lean_bodies.effectiveSubgroupSize
    try:
        lean_bodies.effectiveSubgroupSize = lambda n, m: lean_bodies.ldiv(m * (n + m), n)
        result = map_check.findings(clean)
        expect("REFPOINT" in kinds(result),
               f"a one-character change to the effectiveSubgroupSize transcription "
               f"is REFPOINT (got {kinds(result)})")
        expect("EXPECTED-STALE" in kinds(result),
               f"the same change moves the committed expected values "
               f"(got {kinds(result)})")
    finally:
        lean_bodies.effectiveSubgroupSize = original

    #    ... and the spike constant, which the corpus's reference points could
    #    not see until they were moved off `m = n`. The grid catches it
    #    independently of that repair, which is the point: the grid does not
    #    depend on anyone having chosen a good evaluation point.
    original = lean_bodies.demographicSpike
    try:
        lean_bodies.demographicSpike = \
            lambda n, F, m: 2 * F * lean_bodies.effectiveSubgroupSize(n, m)
        result = map_check.findings(clean)
        expect("EXPECTED-STALE" in kinds(result),
               f"a 4 -> 2 spike constant is caught by the fixture grid "
               f"(got {kinds(result)})")
    finally:
        lean_bodies.demographicSpike = original

    # 7. DEGENERATE-REFERENCE: a reference evaluation in a mapped module that
    #    states a value where its body is zero. This is the category the arc
    #    actually shipped -- `demographicSpike 1 1 1 = 0` at `m = n` -- and the
    #    planted row reproduces it inside the scope the table owns.
    mutated = copy.deepcopy(clean)
    owned = sorted(mutated["mapped_lean_files"])[0]
    mutated["reference_points"].append(
        ("Calibrator.plantedBody_at_reference_point", "DEGENERATE",
         "planted: body is 0 at its own reference point", owned))
    result = map_check.findings(mutated)
    expect("DEGENERATE-REFERENCE" in kinds(result),
           f"a vacuous reference evaluation in a mapped module is "
           f"DEGENERATE-REFERENCE (got {kinds(result)})")

    #    ... and one OUTSIDE the mapped modules must not be gated here, or this
    #    lane would start failing on 25 theorems other lanes own.
    mutated = copy.deepcopy(clean)
    mutated["reference_points"].append(
        ("Calibrator.elsewhere_at_reference_point", "DEGENERATE",
         "planted: outside the mapped modules",
         "Calibrator/SomeOtherModule.lean"))
    result = map_check.findings(mutated)
    expect("DEGENERATE-REFERENCE" not in kinds(result),
           f"a vacuous reference evaluation outside the mapped modules is "
           f"reported but not gated here (got {kinds(result)})")

    # 8. CODE-PATH: an instrument naming its subject by path arithmetic, with
    #    the path one level short. This is the `#[path]` defect verbatim: the
    #    required contract step could not compile and executed nothing.
    mutated = copy.deepcopy(clean)
    mutated["include_paths"].append(
        ("proofs/validation/empirical/correctability_calculator/lib.rs",
         "../../../map/correctability.rs",
         "/nonexistent/proofs/map/correctability.rs", False))
    result = map_check.findings(mutated)
    expect("CODE-PATH" in kinds(result),
           f"a #[path] that does not resolve is CODE-PATH (got {kinds(result)})")

    # 9. A census that read nothing must not pass. Same standard as the empty
    #    corpus below: the failure mode is looking healthy while measuring
    #    nothing, and it is the state the extraction tier was actually in.
    mutated = copy.deepcopy(clean)
    mutated["reference_points"] = [
        (name, "UNREADABLE", "planted", source_file)
        for name, _, _, source_file in mutated["reference_points"]]
    result = map_check.findings(mutated)
    expect("DEGENERATE-REFERENCE" in kinds(result),
           f"a reference-evaluation census that reads nothing is a finding "
           f"(got {kinds(result)})")

    # 10. THE FALSE-POSITIVE DIRECTION, which is the one that damages the corpus.
    #
    #     Every other case here plants a defect and checks it fires. This census
    #     is different in kind: other lanes act on its output and cannot
    #     independently check it, so a theorem wrongly called DEGENERATE
    #     dispatches somebody to move a reference point that was already live --
    #     breaking a sound theorem and booking it as progress. The
    #     both-directions rule applies with more force here than anywhere else
    #     in this file.
    #
    #     These are self-consistency properties rather than fixed expected
    #     verdicts, so they keep working as lanes repair reference points and the
    #     corpus-wide counts move underneath them.
    print()
    print("CALIBRATION: the census must not report a live reference point as degenerate")
    import degenerate
    import api

    mislabelled = []
    for name, verdict, _, _ in clean["reference_points"]:
        if verdict != "DEGENERATE":
            continue
        proposition = degenerate._proposition(api.theorems()[name].get("statement", ""))
        conjuncts = degenerate._conjuncts(proposition)
        values, unread = [], 0
        for conjunct in conjuncts:
            value, _ = degenerate._evaluate_conjunct(api, conjunct)
            if value is None:
                unread += 1
            else:
                values.append(value)
        if unread or not values or any(value != 0 for value in values):
            mislabelled.append((name, values, unread))
    expect(not mislabelled,
           f"every DEGENERATE verdict re-evaluates to all-zero with nothing unread "
           f"(mislabelled: {mislabelled[:3]})")

    unsupported = []
    for name, verdict, _, _ in clean["reference_points"]:
        if verdict != "LIVE":
            continue
        proposition = degenerate._proposition(api.theorems()[name].get("statement", ""))
        values = [v for v, _ in
                  (degenerate._evaluate_conjunct(api, c)
                   for c in degenerate._conjuncts(proposition)) if v is not None]
        if not any(value != 0 for value in values):
            unsupported.append(name)
    expect(not unsupported,
           f"every LIVE verdict has a nonzero evaluation behind it "
           f"(unsupported: {unsupported[:3]})")

    #     A partially-read theorem must NOT be degenerate. This is the concrete
    #     shape the false positive would take: a conjunction whose zero-valued
    #     half this reader can evaluate and whose live half it cannot.
    partial = ": stubZeroBody 0 = 0 ∧ stubLiveBody (Matrix.of ![![1]]) = 1"
    conjuncts = degenerate._conjuncts(degenerate._proposition(partial))
    expect(len(conjuncts) == 2,
           f"the two-conjunct stub splits into two conjuncts (got {len(conjuncts)})")
    readable = [degenerate._evaluate_conjunct(api, c)[0] for c in conjuncts]
    expect(any(value is None for value in readable),
           "the stub's second conjunct is genuinely unreadable, as the case requires")

    # 11. An empty corpus must be an error, never a silent pass. A check that
    #    cannot report its own absence reports someone else's answer as its own.
    print()
    print("CALIBRATION: an unreadable corpus must not pass")
    empty = copy.deepcopy(clean)
    empty["corpus"] = {}
    result = map_check.findings(empty)
    expect(len(result) > 0,
           f"an empty corpus table produces findings rather than silence "
           f"(got {len(result)})")

    print()
    if FAILURES:
        print(f"FAIL: {len(FAILURES)} calibration assertion(s) failed")
        for message in FAILURES:
            print(f"  {message}")
        return 1
    print("PASS: the correspondence guard is calibrated in both directions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

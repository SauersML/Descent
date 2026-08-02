"""Run the whole extraction pipeline and check it, in one command.

    python3 validation/extract/verify.py

Exits non-zero on any failure.  Pure Python, no dependencies, seconds to run
except for coverage (a few minutes).  Use --quick to skip coverage.

The adversarial cases below exist because the first version of the vector
feature was verified with three examples that were all the same shape -- a bare
`∑` over indexed scalars -- and both of its bugs lived in shapes that shape
cannot reach.  Verification examples are now chosen to exercise the awkward
case, not the convenient one: a body that USES its dimension variable, and a
body that does ARITHMETIC on whole vectors.
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
PROOFS = HERE.parent.parent
sys.path.insert(0, str(HERE))

QUICK = "--quick" in sys.argv
failures = []

# Python can serve bytecode from before a regeneration, and the symptom is
# indistinguishable from "the fix was never applied".  Clear it before anything
# imports the generated module, so a green run cannot be a stale one.
import shutil
shutil.rmtree(HERE / "__pycache__", ignore_errors=True)


def step(label, fn):
    print(f"\n=== {label} ===")
    try:
        fn()
    except Exception as e:                                       # noqa: BLE001
        failures.append(f"{label}: {type(e).__name__}: {e}")
        print(f"  FAILED: {type(e).__name__}: {e}")


def run(script, *args):
    r = subprocess.run([sys.executable, str(HERE / script), *args],
                       cwd=str(PROOFS), capture_output=True, text=True)
    print(r.stdout[-4000:] or r.stderr[-2000:])
    if r.returncode != 0:
        raise RuntimeError(f"{script} exited {r.returncode}\n{r.stderr[-2000:]}")


def close(label, got, want, tol=1e-9):
    if not isinstance(got, float) or abs(got - want) > tol * max(1.0, abs(want)):
        raise AssertionError(f"{label}: got {got!r}, want ~{want!r}")
    print(f"  ok  {label} = {got!r}")


step("regenerate the table and the executable module", lambda: run("emit.py"))


def staleness():
    import api
    api.refresh()
    complaints = api.staleness()
    if complaints:
        raise AssertionError("; ".join(complaints))
    print("  ok  generated module is current with the table, no stale bytecode")


step("generated artifacts are current", staleness)
step("hand-verified ground truth + cross-validation", lambda: run("test_parser.py"))


def adversarial_vectors():
    import api
    api.refresh()

    # SHAPE 1: the body uses its own DIMENSION variable, which is an implicit
    # binder and so absent from the signature.  `(T : ℝ) / ∑ i, (1 / Ne i)`.
    fn, args = api.callable_for("Calibrator.harmonicMeanNe")
    print(f"  harmonicMeanNe args={args}")
    got = fn([100.0, 200.0])
    close("harmonicMeanNe([100,200])", got, 2.0 / (1 / 100 + 1 / 200))

    # SHAPE 2: ARITHMETIC ON WHOLE MATRICES, then a sum over the result.
    # `frobeniusNormSq (Sig_S - Sig_T)`.
    fn, args = api.callable_for("Calibrator.ldMismatchFrobenius")
    print(f"  ldMismatchFrobenius args={args}")
    got = fn([[1.0, 0.5], [0.5, 1.0]], [[1.0, 0.1], [0.1, 1.0]])
    close("ldMismatchFrobenius", got, 2 * (0.4 ** 2))

    # SHAPE 3: the previously-passing shape, to prove nothing regressed.
    import lean_defs
    close("dominanceVariance([0.1,0.5],[1,2])",
          lean_defs.dominanceVariance([0.1, 0.5], [1.0, 2.0]),
          (2 * 0.1 * 0.9 * 1.0) ** 2 + (2 * 0.5 * 0.5 * 2.0) ** 2)
    close("cumulativeDrift([100,200])",
          lean_defs.cumulativeDrift([100.0, 200.0]), 1 / 200 + 1 / 400)
    close("frobeniusNormSq([[1,2],[3,4]])",
          lean_defs.frobeniusNormSq([[1.0, 2.0], [3.0, 4.0]]), 30.0)

    # SHAPE 4: scalar-only definitions must be untouched by the vector feature.
    close("coalFst(100,1000)", lean_defs.coalFst(100.0, 1000.0), 100 / 2100)
    close("neiFst(0.4,0.3)", lean_defs.neiFst(0.4, 0.3), 0.25)
    assert api.vector_args("Calibrator.coalFst") is None, \
        "scalar-only definition reported as taking vectors"
    print("  ok  scalar-only signatures unchanged")

    # Every vector definition must at least evaluate.  Arguments come from the
    # same sampler the accounting uses -- structure-typed and function-typed
    # arguments need real inhabitants, and feeding them a bare float tests the
    # sampler rather than the feature.
    import admissible
    import random
    import json as _json
    structs = {s["short"]: s
               for s in _json.loads((HERE / "defs.json").read_text())["structures"]}
    broken = []
    for name in api.definition_table():
        spec = api.vector_args(name)
        if not spec:
            continue
        try:
            f, argnames = api.callable_for(name)
        except api.NotExtractable:
            continue
        d = api.definition(name)
        structval = {}
        for a in d["args"]:
            head = a["type"].split()[0].split(".")[-1] if a["type"].split() else ""
            if head in structs:
                for n in a["names"]:
                    import translate
                    structval[translate.pyname(n)] = structs[head]
        rng = random.Random(7)
        box = api.admissible_box(name)
        pt = {k: (lo + hi) / 2 for k, (lo, hi) in box.items()}
        import translate
        pt = {translate.pyname(k): v for k, v in pt.items()}
        try:
            vals = admissible.build_args(argnames, pt, structval, spec, rng, structs)
            out = f(*vals)
        except Exception as e:                                   # noqa: BLE001
            broken.append((name, f"{type(e).__name__}: {e}"))
            continue
        if isinstance(out, (int, float)) and out != out:
            broken.append((name, "returned nan"))
    print(f"  vector definitions evaluated: "
          f"{sum(1 for n in api.definition_table() if api.vector_args(n))}, "
          f"errors: {len(broken)}")
    for n, why in broken[:15]:
        print(f"    {n}: {why}")
    if broken:
        raise AssertionError(f"{len(broken)} vector definitions raise or return nan")


step("ADVERSARIAL vector cases (dimension variable, whole-vector arithmetic)",
     adversarial_vectors)


def totality():
    import lean_rt as rt
    close("x/0 = 0", rt.rdiv(1.0, 0.0), 0.0)
    close("log 0 = 0", rt.rlog(0.0), 0.0)
    close("log(-e) = 1", rt.rlog(-2.718281828459045), 1.0, tol=1e-12)
    close("sqrt(-1) = 0", rt.rsqrt(-1.0), 0.0)
    close("inv 0 = 0", rt.rinv(0.0), 0.0)
    close("Phi(0) = 0.5", rt.Phi(0.0), 0.5)
    close("Phi(-inf-ish)", rt.Phi(-40.0), 0.0, tol=1e-9)
    # elementwise lifting must agree with scalar arithmetic
    assert rt.sub([[1.0, 2.0]], [[0.5, 0.5]]) == [[0.5, 1.5]], "matrix sub"
    assert rt.mul([1.0, 2.0], 3.0) == [3.0, 6.0], "scalar broadcast"
    print("  ok  elementwise arithmetic")


step("Mathlib totality conventions", totality)


def no_swallowed_declarations():
    """Every declaration visible in the source must appear in the table.

    A declaration can be visible to grep and absent from the table -- that is
    what a name-keyed dict does to two declarations sharing a fully-qualified
    name, and the symptom is a well-formed-looking namesake row standing in for
    the missing one.  Counting per file catches it whatever the mechanism.
    """
    import api
    import collections
    import re as _re
    api.refresh()
    DECL = _re.compile(
        r"^(?:(?:noncomputable|private|protected|partial|unsafe|scoped|local|nonrec)\s+)*"
        r"(?:def|abbrev)\s+\S")
    raw = collections.Counter()
    sources = sorted((PROOFS / "Calibrator").rglob("*.lean"))
    root = PROOFS / "Calibrator.lean"
    if root.exists():
        sources.append(root)          # the root module declares defs too
    for path in sources:
        src = path.read_text(errors="ignore")
        # strip docstrings and block comments: a `def` inside one is prose, not
        # a declaration (Identification.lean has exactly this).
        import lean_parse
        clean, _docs = lean_parse.strip_comments(src)
        rel = str(path.relative_to(PROOFS))
        for line in clean.splitlines():
            if line[:1] not in (" ", "\t") and DECL.match(line):
                raw[rel] += 1
    have = collections.Counter()
    for d in api.all_rows():
        have[d["file"]] += 1
    # Two-sided on purpose.  A table with FEWER rows than the source has
    # swallowed a declaration; a table with MORE has invented one, and a check
    # that only looks one way would call the second case clean.
    bad = []
    for f in sorted(set(raw) | set(have)):
        if raw.get(f, 0) != have.get(f, 0):
            bad.append((f, raw.get(f, 0), have.get(f, 0)))
    print(f"  files checked: {len(raw)}, source declarations: {sum(raw.values())}, "
          f"table rows: {sum(have.values())}")
    for f, n, h in bad[:15]:
        print(f"    MISMATCH {f}: source {n}, table {h}")
    if bad:
        raise AssertionError(f"{len(bad)} file(s) where the table and the source "
                             f"disagree on how many declarations exist")
    print("  ok  no declaration is missing from the table")


step("no swallowed declarations (per-file count reconciliation)",
     no_swallowed_declarations)


def collision_handling_actually_works():
    """The collision path must be exercised even when the corpus has none.

    Shipping an unexercised code path is how the last two bugs got in.  This
    injects a synthetic duplicate and asserts the table refuses to pick.
    """
    import json as _json
    import lean_parse

    class Fake:
        pass

    rows = []
    for file, line in (("Calibrator/A.lean", 10), ("Calibrator/B.lean", 20)):
        f = Fake()
        f.name, f.file, f.line, f.signature = "Calibrator.dup", file, line, "(x : R) : R"
        rows.append(f)
    got = lean_parse.find_collisions(rows)
    assert "Calibrator.dup" in got, "find_collisions missed a real duplicate"
    assert len(got["Calibrator.dup"]) == 2, got
    print(f"  ok  duplicate detected: {got['Calibrator.dup']}")

    # and a table built over that blob must exclude it and raise on lookup
    import api
    real = api._blob()
    patched = dict(real)
    patched["collisions"] = {"Calibrator.dup": got["Calibrator.dup"]}
    patched["definitions"] = real["definitions"] + [
        {**real["definitions"][0], "name": "Calibrator.dup"}]
    api._blob.cache_clear()
    api.definition_table.cache_clear()
    api.collisions.cache_clear()
    orig = api._blob
    try:
        api._blob = lambda: patched
        assert "Calibrator.dup" not in api.definition_table(), \
            "a collided name leaked into the table"
        try:
            api.definition("Calibrator.dup")
        except KeyError as e:
            assert "DECLARED TWICE" in str(e), str(e)
            print("  ok  definition() refuses to pick between duplicates")
        else:
            raise AssertionError("definition() silently returned one of two duplicates")
    finally:
        api._blob = orig
        api._blob.cache_clear()
        api.definition_table.cache_clear()
        api.collisions.cache_clear()

    live = api.collisions()
    print(f"  live corpus collisions: {len(live)}"
          + (f" -- {list(live)}" if live else " (corpus compiles)"))


step("collision handling is exercised, not assumed", collision_handling_actually_works)
step("mechanical extraction ceiling", lambda: run("ceiling.py"))
step("parser reconciliation against the other tables", lambda: run("reconcile.py"))
if not QUICK:
    step("falsifiable coverage (internal consistency)",
         lambda: run("coverage_v2.py", "--json", str(HERE / "coverage.json")))
step("model validation (regime metric)", lambda: run("regime.py"))

print("\n" + "=" * 74)
if failures:
    print(f"{len(failures)} STEP(S) FAILED")
    for f in failures:
        print(f"  {f}")
    sys.exit(1)
print("all steps passed")

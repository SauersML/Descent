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

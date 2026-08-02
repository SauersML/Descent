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
            vals = admissible.build_args(argnames, pt, structval, spec, rng,
                                        structs, admissible.arg_types(d))
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


def shape_directed_inhabitants_are_right():
    """POSITIVE CONTROLS for `admissible.type_value` and `lean_rt.VecFn`.

    Every value below is known independently of the code under test: the
    cardinalities come from the Lean declarations (`Pop` has two constructors,
    `DiploidGenotype` three), and the linear-algebra answers are computed by
    hand.  The point of the controls is that a *wrong* inhabitant is silent --
    a scalar where a vector belongs does not crash, it makes the definition
    return a plausible number -- so the shapes have to be asserted, not
    observed.
    """
    import random
    import admissible
    import lean_rt as _rt
    import api
    api.refresh()
    structs = api.structures()
    rng = random.Random(11)

    # -- the runtime's linear algebra, against arithmetic done by hand
    close("dotProduct([1,2,3],[4,5,6])",
          float(_rt.dotProduct([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])), 32.0)
    assert list(_rt.mulVec([[1.0, 2.0], [3.0, 4.0]], [1.0, 1.0])) == [3.0, 7.0]
    print("  ok  mulVec [[1,2],[3,4]] [1,1] = [3,7]")
    assert list(_rt.vecMul([1.0, 1.0], [[1.0, 2.0], [3.0, 4.0]])) == [4.0, 6.0]
    print("  ok  vecMul [1,1] [[1,2],[3,4]] = [4,6]")
    close("trace [[1,2],[3,4]]", float(_rt.trace([[1.0, 2.0], [3.0, 4.0]])), 5.0)
    for bad, why in (((lambda: _rt.dotProduct([1.0], [1.0, 2.0])), "length mismatch"),
                     ((lambda: _rt.trace([[1.0, 2.0]])), "non-square trace")):
        try:
            bad()
        except ValueError:
            print(f"  ok  refuses: {why}")
        else:
            raise AssertionError(f"{why} was accepted instead of refused")

    # -- VecFn: one value, two readings, and a loud edge
    v = _rt.VecFn([10.0, 20.0, 30.0])
    assert v(1) == v[1] == 20.0 and len(v) == 3
    print("  ok  VecFn: v(1) == v[1] == 20.0, len 3")
    m = _rt.VecFn([_rt.VecFn([1.0, 2.0]), _rt.VecFn([3.0, 4.0])])
    assert m(1, 0) == m[1][0] == 3.0
    print("  ok  VecFn: m(1,0) == m[1][0] == 3.0")
    try:
        v(3)
    except IndexError:
        print("  ok  VecFn refuses an index outside its dimension")
    else:
        raise AssertionError("VecFn returned a value for an out-of-range index")

    # -- cardinalities read from the corpus's own inductives
    cards = admissible.enum_cards(structs)
    assert cards.get("Pop") == 2, cards.get("Pop")
    assert cards.get("DiploidGenotype") == 3, cards.get("DiploidGenotype")
    print("  ok  enum cardinalities: Pop=2, DiploidGenotype=3 (from the Lean)")

    # -- shapes, asserted against the Lean types they were built from
    D = admissible.VECTOR_DIM
    beta = admissible.type_value("Pop \u2192 Fin q \u2192 \u211d", rng, structs)
    assert len(beta) == 2, "a Pop-indexed table must have exactly 2 entries"
    assert len(beta[0]) == D and all(isinstance(x, float) for x in beta[0])
    print(f"  ok  `Pop \u2192 Fin q \u2192 \u211d` is 2 x {D} reals")
    try:
        beta(2)
    except IndexError:
        print("  ok  there is no third population to read")
    else:
        raise AssertionError("a Pop-indexed table invented a third population")

    M = admissible.type_value(
        "Matrix (Fin p) (Fin q) \u211d", rng, structs)
    assert len(M) == D and len(M[0]) == D and M(1, 2) == M[1][2]
    print(f"  ok  `Matrix (Fin p) (Fin q) \u211d` is {D} x {D}, M(1,2)==M[1][2]")

    # A functional must actually depend on its argument: a constant here would
    # make `totalVariance arch c` independent of `c` and hide every error in it.
    F = admissible.type_value("(Fin k \u2192 \u211d) \u2192 \u211d", rng, structs)
    a, b = F([1.0, 0.0, 0.0]), F([0.0, 0.0, 1.0])
    assert isinstance(a, float) and a != b, (a, b)
    print("  ok  `(Fin k \u2192 \u211d) \u2192 \u211d` is a NON-constant functional")

    # `\u2115 \u2192 Fin p \u2192 \u211d`: unbounded outer index, and the same
    # generation must give the same vector every time it is asked for.
    G = admissible.type_value("\u2115 \u2192 Fin p \u2192 \u211d", rng, structs)
    assert G(3, 1) == G(3, 1) and len(G(7)) == D
    assert G(3, 1) != G(4, 1), "a generation-indexed field must vary with t"
    print("  ok  `\u2115 \u2192 Fin p \u2192 \u211d` is stable in t and varies with t")

    # -- and the refusals, which are the safety property
    for ty in ("Measure \u211d", "Set \u03b1", "List \u03b9"):
        try:
            admissible.type_value(ty, rng, structs)
        except admissible.Uninhabitable:
            print(f"  ok  refuses to inhabit {ty!r}")
        else:
            raise AssertionError(f"invented an inhabitant of {ty!r}")


def finite_index_types_translate_correctly():
    """POSITIVE CONTROLS for the finite-index-type translation.

    Enumerations (`Pop`, `DiploidGenotype`) are index types in this corpus, and
    an ordinal is assigned in two independent places -- emit.py's `enums` table
    and admissible.type_value's tables.  If those two ever disagreed,
    `m.beta Pop.target` would silently read the SOURCE population's entry and
    hand back a number from the wrong population.  Nothing else in this project
    would notice, so it is asserted here against the Lean declaration order.
    """
    import api
    import lean_rt as _rt
    api.refresh()

    # `def Pop.pair (s t : α) : Pop → α | Pop.source => s | Pop.target => t`
    # -- a case split, so the answers are the arguments themselves.
    fn, argnames = api.callable_for("Calibrator.Pop.pair")
    assert fn(11.0, 22.0, 0) == 11.0, "Pop.source must be ordinal 0"
    assert fn(11.0, 22.0, 1) == 22.0, "Pop.target must be ordinal 1"
    print(f"  ok  Pop.pair{tuple(argnames)}: source->first, target->second")
    try:
        fn(11.0, 22.0, 2)
    except IndexError:
        print("  ok  Pop.pair refuses a third population")
    else:
        raise AssertionError("Pop.pair answered for a constructor that does "
                             "not exist")

    # A ∑ whose index has no type annotation and no `Fin n` argument to read a
    # dimension from: the range comes from what the index is APPLIED to.
    # `haplotypeHomozygosity (freq : α → ℝ) := ∑ i, freq i ^ 2`, so a uniform
    # frequency vector of length n gives n * (1/n)^2 = 1/n -- known by hand.
    fn, _a = api.callable_for("Calibrator.haplotypeHomozygosity")
    for n in (2, 4, 5):
        close(f"haplotypeHomozygosity(uniform {n}) = 1/{n}",
              float(fn([1.0 / n] * n)), 1.0 / n)

    # ... and if two things the index runs over have different lengths, the
    # range is ambiguous and the sum must REFUSE, not pick one.
    try:
        _rt.sumdim("i", 4, 5)
    except ValueError as e:
        assert "DIFFERENT lengths" in str(e), str(e)
        print("  ok  a ∑ over mismatched dimensions refuses instead of choosing")
    else:
        raise AssertionError("sumdim silently chose between 4 and 5")
    close("sumdim agrees with itself", float(_rt.sumdim("i", 3, 3, 3)), 3.0)

    # A RANK-2 abstract index: `gramForm (A : Matrix ι ι ℝ) (x y : ι → ℝ) :=
    # ∑ i, ∑ j, x i * A i j * y j`.  Neither index is annotated and neither
    # argument is a `Fin n`, so both ranges are inferred; picking e_0 and e_1
    # makes the answer a single matrix entry, which is checkable by eye.
    fn, argnames = api.callable_for("Calibrator.gramForm")
    A = [[1.0, 2.0], [3.0, 4.0]]
    close("gramForm(A, e0, e1) = A[0][1]", float(fn(A, [1.0, 0.0], [0.0, 1.0])), 2.0)
    close("gramForm(A, e1, e0) = A[1][0]", float(fn(A, [0.0, 1.0], [1.0, 0.0])), 3.0)
    close("gramForm(A, 1, 1) = sum of A", float(fn(A, [1.0, 1.0], [1.0, 1.0])), 10.0)
    assert api.vector_args("Calibrator.gramForm")["A"]["rank"] == 2, \
        "a Matrix over an abstract index must be reported as rank 2"
    print("  ok  api.vector_args reports the abstract-index Matrix as rank 2")


step("finite index types: enums, inferred ∑ ranges, Mathlib linear algebra",
     finite_index_types_translate_correctly)


step("shape-directed inhabitants (positive controls)",
     shape_directed_inhabitants_are_right)


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

"""Detect a de-duplication that silently permuted a definition's arguments.

    python3 validation/extract/permutation_check.py [--commits 60]

THE HAZARD.  When four names for one formula are collapsed into one, the
survivor may take its arguments in a different order.  Every call site rewritten
from the name alone then computes the right function on the wrong arguments --
and if both arguments are real-valued, the result is finite, well-typed and
wrong.  No type checker catches it and a range check is unlikely to, because
both orderings usually land in the same plausible interval.

THE ONLY THING WORTH REPORTING IS ASYMMETRY.  A permuted absorption where the
body is symmetric in the permuted slots is harmless: `1 / (1 + 4 * Ne * m)` is
the same function whichever slot you fill first, so a name-only repoint still
computes the right number.  This actually happened, and an alarm was raised on
it -- by inferring "different order, therefore different result" WITHOUT READING
THE BODY.  The warning was more dangerous than the thing it warned about: acting
on it would have swapped arguments on two sibling definitions that do NOT
reorder, introducing the exact bug being warned about.

So the asymmetry test is not a refinement of this detector, it is the whole
detector.  A version that flagged every permuted absorption would be ignored
within a day, which is the same as not existing.

HOW ASYMMETRY IS DECIDED.  Numerically, by evaluating the survivor at random
admissible points with the arguments in both orders.  A point where the two
differ is a WITNESS: conclusive proof the permutation matters.  Finding no such
point is NOT proof of symmetry -- it is failure to find a witness, and the
report says so rather than claiming the pair is safe.

POSITIVE CONTROL.  A detector that reports nothing over the existing history is
uninformative unless it is known capable of firing.  `--self-test` runs a
synthetic asymmetric pair -- `f a b := a - 2 * b` absorbed into `g b a` -- and
fails loudly if the detector does not flag it.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import random
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import lean_parse                                          # noqa: E402
from translate import Untranslatable, pyname, translate_def  # noqa: E402

REPO = HERE.parent.parent.parent
PROBE_POINTS = 24


def git(*args, cwd=REPO):
    r = subprocess.run(["git", *args], cwd=str(cwd), capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def parse_revision_file(rev, path):
    """Parse one .lean file as it stood at `rev`.  Returns {fq name: decl dict}."""
    src = git("show", f"{rev}:{path}")
    if not src.strip():
        return {}
    with tempfile.TemporaryDirectory() as td:
        p = pathlib.Path(td) / pathlib.Path(path).name
        p.write_text(src)
        try:
            decls, _fail = lean_parse.parse_file(p, pathlib.Path(td))
        except Exception:                                       # noqa: BLE001
            return {}
    return {d.name: d for d in decls if d.kind in ("def", "abbrev")}


def explicit_args(d):
    return [n for a in d.args if not a["implicit"] for n in a["names"]]


def compile_body(d, fname="_probe"):
    """A callable from a parsed declaration, or None."""
    rec = {"short": fname, "args": d.args, "body": d.body, "equations": d.equations}
    try:
        src, argnames = translate_def(rec, fname=fname)
    except (Untranslatable, Exception):                         # noqa: BLE001
        return None, None
    ns = {}
    try:
        exec(compile("import lean_rt as _rt\n" + src, "<probe>", "exec"), ns)
    except Exception:                                           # noqa: BLE001
        return None, None
    return ns.get(fname), argnames


def asymmetry_witness(fn, n_args, rng):
    """A point where permuting the first two arguments changes the value.

    Returns (point, value_in_order, value_swapped) or None.  A witness is
    conclusive; its absence is not.
    """
    for _ in range(PROBE_POINTS):
        pt = [rng.uniform(0.05, 3.0) for _ in range(n_args)]
        swapped = list(pt)
        swapped[0], swapped[1] = swapped[1], swapped[0]
        try:
            a, b = fn(*pt), fn(*swapped)
        except Exception:                                       # noqa: BLE001
            continue
        if not isinstance(a, (int, float)) or not isinstance(b, (int, float)):
            continue
        if a != a or b != b:
            continue
        if abs(a - b) > 1e-12 * max(1.0, abs(a), abs(b)):
            return pt, a, b
    return None


def is_permutation(a1, a2):
    """True only when a2 REORDERS a1 -- same names, different order.

    A rename is not a permutation.  `f (m) -> g (p)` maps positionally with no
    hazard at all, and reporting it wastes the reader's attention on the one
    thing this detector must not do.  The first version of this check compared
    the lists for inequality, so every rename fired; two of the two "findings"
    over 60 commits were renames of unrelated quantities that happened to share
    a body shape.
    """
    return len(a1) > 1 and a1 != a2 and sorted(a1) == sorted(a2)


def bodies_equivalent(d1, d2):
    """Same body up to renaming the explicit arguments positionally."""
    a1, a2 = explicit_args(d1), explicit_args(d2)
    if len(a1) != len(a2) or not a1:
        return False
    b1 = " ".join(d1.body.split())
    b2 = " ".join(d2.body.split())
    if b1 == b2:
        return True
    # rename d2's arguments to d1's, positionally, then compare
    import re
    ren = b2
    for src, dst in zip(a2, a1):
        ren = re.sub(rf"(?<![\w']){re.escape(src)}(?![\w'])", f"\x00{dst}\x00", ren)
    ren = ren.replace("\x00", "")
    return " ".join(ren.split()) == b1


_TREE_CACHE = {}


def full_tree(rev):
    """Every definition in the corpus at `rev`, cached per revision."""
    if rev in _TREE_CACHE:
        return _TREE_CACHE[rev]
    out = {}
    listing = git("ls-tree", "-r", "--name-only", rev, "proofs/Calibrator").split()
    for f in listing:
        if f.endswith(".lean"):
            out.update(parse_revision_file(rev, f))
    _TREE_CACHE[rev] = out
    return out


def scan(n_commits):
    findings, examined, permuted = [], 0, 0
    log = git("log", "--format=%H", f"-{n_commits}", "--", "proofs/Calibrator").split()
    rng = random.Random(20260802)

    for rev in log:
        files = [f for f in git("show", "--name-only", "--format=", rev).split()
                 if f.endswith(".lean") and "Calibrator" in f]
        if not files:
            continue
        before, after = {}, {}
        for f in files:
            before.update(parse_revision_file(f"{rev}^", f))
            after.update(parse_revision_file(rev, f))
        # The survivor of an absorption is very often in a DIFFERENT file, which
        # the collapsing commit need not have touched -- `equilibriumFst` lived
        # in AncestrySpecificArchitecture and its survivor in PortabilityDrift.
        # Searching only the changed files misses exactly the cross-file case
        # this detector exists for, so fall back to the whole tree.
        # Fall back to the whole tree ONLY for removals with no survivor among
        # the changed files.  Parsing the full corpus at every removal commit is
        # correct and unusably slow -- the first version did that and produced
        # no output in ten minutes, which is the same as not having the check.
        removed_here = set(before) - set(after)
        needs_wide = [n for n in removed_here
                      if explicit_args(before[n])
                      and not any(bodies_equivalent(before[n], s2)
                                  for k2, s2 in after.items() if k2 != n)]
        if needs_wide:
            after.update(full_tree(rev))
        # a definition present before and absent after was removed by this commit
        for name in set(before) - set(after):
            gone = before[name]
            if not explicit_args(gone):
                continue
            examined += 1
            for sname, surv in after.items():
                if sname == name or not bodies_equivalent(gone, surv):
                    continue
                ga, sa = explicit_args(gone), explicit_args(surv)
                if not is_permutation(ga, sa):
                    continue        # identical order, or a rename: no hazard
                permuted += 1
                fn, argnames = compile_body(surv)
                if fn is None or len(argnames) < 2:
                    findings.append({
                        "commit": rev[:9], "removed": name, "survivor": sname,
                        "removed_args": ga, "survivor_args": sa,
                        "verdict": "UNTESTED", "why": "survivor body not evaluable",
                    })
                    break
                w = asymmetry_witness(fn, len(argnames), rng)
                findings.append({
                    "commit": rev[:9], "removed": name, "survivor": sname,
                    "removed_args": ga, "survivor_args": sa,
                    "body": " ".join(surv.body.split())[:100],
                    "verdict": "ASYMMETRIC -- ORDER MATTERS" if w else
                               "no witness found (probably symmetric)",
                    "witness": None if w is None else
                               {"point": [round(x, 6) for x in w[0]],
                                "in_order": w[1], "swapped": w[2]},
                })
                break
    return findings, examined, permuted


def self_test():
    """Positive control: the detector must flag a known asymmetric permutation."""
    class D:
        kind = "def"
        equations = []

    gone, surv = D(), D()
    gone.name, surv.name = "Test.f", "Test.g"
    gone.args = [{"names": ["a", "b"], "type": "ℝ", "implicit": False,
                  "binder": "()"}]
    surv.args = [{"names": ["b", "a"], "type": "ℝ", "implicit": False,
                  "binder": "()"}]
    gone.body, surv.body = "a - 2 * b", "a - 2 * b"

    ok = True
    if not bodies_equivalent(gone, surv):
        print("  SELF-TEST FAIL: equivalent bodies not recognised")
        ok = False
    fn, argnames = compile_body(surv)
    if fn is None:
        print("  SELF-TEST FAIL: synthetic body did not compile")
        return False
    w = asymmetry_witness(fn, len(argnames), random.Random(1))
    if w is None:
        print("  SELF-TEST FAIL: `a - 2 * b` reported as symmetric")
        ok = False
    else:
        print(f"  ok  synthetic asymmetric pair flagged: f{tuple(explicit_args(gone))}"
              f" -> g{tuple(explicit_args(surv))}, witness {[round(x,3) for x in w[0]]}"
              f" gives {w[1]:.6g} vs {w[2]:.6g}")

    # negative control: a symmetric body must NOT be flagged
    surv.body = "1 / (1 + 4 * a * b)"
    gone.body = "1 / (1 + 4 * a * b)"
    fn2, an2 = compile_body(surv)
    if fn2 is not None and asymmetry_witness(fn2, len(an2), random.Random(1)):
        print("  SELF-TEST FAIL: `1/(1+4ab)` reported as asymmetric")
        ok = False
    else:
        print("  ok  symmetric body correctly not flagged "
              "(this is the real case that was over-reported)")
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--commits", type=int, default=60)
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args(argv)

    print("=" * 74)
    print("ARGUMENT-PERMUTATION DETECTOR")
    print("=" * 74)
    print("positive control:")
    if not self_test():
        print("\nDETECTOR IS NOT KNOWN CAPABLE OF FIRING -- results below mean nothing")
        return 2
    if a.self_test:
        return 0

    findings, examined, permuted = scan(a.commits)
    print(f"\ncommits scanned            : {a.commits}")
    print(f"removed definitions examined: {examined}")
    print(f"absorbed WITH a permutation : {permuted}")

    real = [f for f in findings if f["verdict"].startswith("ASYMMETRIC")]
    print(f"\nASYMMETRIC permutations (order matters, silent wrong number): {len(real)}")
    for f in real:
        print(f"  {f['commit']}  {f['removed']}{tuple(f['removed_args'])}")
        print(f"            -> {f['survivor']}{tuple(f['survivor_args'])}")
        print(f"            body: {f['body']}")
        w = f["witness"]
        print(f"            witness {w['point']}: in-order {w['in_order']:.6g}"
              f" vs swapped {w['swapped']:.6g}")

    benign = [f for f in findings if not f["verdict"].startswith("ASYMMETRIC")]
    print(f"\npermuted but no asymmetry witness found: {len(benign)}")
    for f in benign:
        print(f"  {f['commit']}  {f['removed']}{tuple(f['removed_args'])}"
              f" -> {f['survivor']}{tuple(f['survivor_args'])}  [{f['verdict']}]")
    if benign:
        print("  NOTE: absence of a witness is not proof of symmetry. These are")
        print("  unflagged, not cleared.")

    (HERE / "permutation_check.json").write_text(json.dumps(
        {"commits": a.commits, "examined": examined, "permuted": permuted,
         "findings": findings}, indent=1))
    print(f"\nwritten: {HERE / 'permutation_check.json'}")
    return 1 if real else 0


if __name__ == "__main__":
    sys.exit(main())

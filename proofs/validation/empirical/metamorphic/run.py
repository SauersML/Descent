#!/usr/bin/env python3
"""Metamorphic gate: evaluate every declared relation on a FIXED input grid.

    python3 proofs/validation/empirical/metamorphic/run.py
    python3 proofs/validation/empirical/metamorphic/run.py --coverage

Exit 0 iff:
  * every relation in relations.RELATIONS holds on the whole grid, except those
    pinned in EXPECTED_VIOLATIONS;
  * every pinned violation STILL violates -- a pinned exception that starts
    holding is a regression, exactly as in the differential battery;
  * every declared name still exists in the corpus (catches renames and
    deletions, without pinning a line number);
  * every extractable scalar definition in a SWEPT module is declared somewhere.

WHY THIS CAN GATE, when most of empirical/ cannot.  There is no sampling and no
oracle: the inputs are literals in this file, the transformation is exact, and
the expected relation is an identity. Re-running cannot change the verdict.  The
tolerance below is NOT a statistical allowance -- see TOL.

WHAT IT CONSUMES.  `extract/api.py`, the single parse of proofs/Calibrator/ that
every checker shares.  Building a second idea of what the corpus contains is how
two checkers come to disagree about which definitions exist, so this one has no
parser of its own; `emit.py` must have run first, exactly as for the
differential battery.
"""

import sys
import os
from fractions import Fraction as Q

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "extract"))
sys.path.insert(0, HERE)

import api  # noqa: E402
import relations as R  # noqa: E402

# The relation is an exact identity over the reals; the transcribed bodies
# evaluate in float64, so the two sides differ by rounding and nothing else.
# A GENUINE violation -- a flipped sign, an inverted ratio, a wrong exponent --
# is O(1), twelve orders of magnitude away from this. This is a float-equality
# tolerance, not a confidence interval: no sample size is involved and no
# re-run moves it.
TOL = 1e-9

# The fixed grid. Chosen so that no denominator in a swept body vanishes, no
# `max 0` clip binds, and allele frequencies stay strictly inside (0,1) where
# the complement is another legal frequency. Literals, not draws.
GRID_POINTS = (
    Q(3, 10), Q(7, 10), Q(1, 5), Q(9, 10), Q(1, 2), Q(2, 5), Q(3, 5), Q(4, 5),
)
# Scale factors for the scaling relations. Kept away from 1 (which makes every
# scaling relation trivially true) and away from 0.
SCALE_FACTORS = (Q(2), Q(1, 2), Q(3), Q(7, 5))


class Violation(Exception):
    pass


# `extract/api.py` ASCII-ises Unicode subscripts when it builds a Python
# callable, so the Lean argument `p₁` arrives as `p_1`. The table is written in
# the corpus's own spelling; this maps between them. Greek letters are Python
# identifiers already and pass through untouched.
_SUBSCRIPTS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def _normalise(name):
    out = []
    for ch in name:
        if ch in "₀₁₂₃₄₅₆₇₈₉":
            out.append("_" + ch.translate(_SUBSCRIPTS))
        else:
            out.append(ch)
    return "".join(out)


def resolve_args(rel, argnames):
    """Map the argument names the table uses onto the callable's own names.

    Raises Violation naming the argument if the table refers to a parameter the
    definition does not have. That is not a nuisance: an argument rename or
    reorder silently changes what a relation is asserting, and this is where it
    surfaces.
    """
    lookup = {}
    for actual in argnames:
        lookup[actual] = actual
        lookup[_normalise(actual)] = actual
    resolved = {}
    for key in ("freq", "effect", "args", "up", "down"):
        if key in rel:
            resolved[key] = tuple(_lookup(lookup, a, rel, argnames)
                                  for a in rel[key])
    for key in ("arg", "a", "b"):
        if key in rel:
            resolved[key] = _lookup(lookup, rel[key], rel, argnames)
    merged = dict(rel)
    merged.update(resolved)
    return merged


def _lookup(lookup, name, rel, argnames):
    norm = _normalise(name)
    if name in lookup:
        return lookup[name]
    if norm in lookup:
        return lookup[norm]
    raise Violation(
        f"relation {rel['id']} names argument {name!r}, but the definition's "
        f"parameters are {list(argnames)}. An argument was renamed or reordered.")


def _assign(argnames, k):
    """Deterministic point k of the grid, one value per argument."""
    return {a: GRID_POINTS[(k + i) % len(GRID_POINTS)]
            for i, a in enumerate(argnames)}


def _call(fn, argnames, point):
    return fn(*[float(point[a]) for a in argnames])


def _close(x, y):
    if x != x or y != y:            # NaN on either side is never agreement
        return False
    scale = max(abs(x), abs(y), 1.0)
    return abs(x - y) <= TOL * scale


def _transform(rel, argnames, point, c):
    """Apply the relation's input transformation; return (new_point, factor)."""
    p = dict(point)
    kind = rel["kind"]
    if kind == "allele_swap":
        for a in rel["freq"]:
            p[a] = 1 - p[a]
        for a in rel["effect"]:
            p[a] = -p[a]
        return p, Q(1)
    if kind == "scale":
        p[rel["arg"]] = p[rel["arg"]] * c
        return p, c ** rel["exp"] if rel["exp"].denominator == 1 else None
    if kind in ("joint_scale",):
        for a in rel["args"]:
            p[a] = p[a] * c
        return p, c ** rel["exp"] if rel["exp"].denominator == 1 else None
    if kind == "reciprocal_scale":
        for a in rel["up"]:
            p[a] = p[a] * c
        for a in rel["down"]:
            p[a] = p[a] / c
        return p, Q(1)
    if kind == "swap":
        p[rel["a"]], p[rel["b"]] = p[rel["b"]], p[rel["a"]]
        return p, Q(1)
    if kind == "negate":
        for a in rel["args"]:
            p[a] = -p[a]
        return p, Q(1)
    raise Violation(f"unknown relation kind {kind!r}")


def _expected(rel, base, factor, c):
    """The value the transformed call must produce."""
    if rel["kind"] == "allele_swap":
        if rel["rel"] == "invariant":
            return base
        if rel["rel"] == "negated":
            return -base
        if rel["rel"] == "complement":
            return 1.0 - base
    if rel["kind"] == "negate":
        return -base
    if rel["kind"] in ("swap", "reciprocal_scale"):
        return base
    if rel["kind"] in ("scale", "joint_scale"):
        return float(c) ** float(rel["exp"]) * base
    raise Violation(f"unknown relation kind {rel['kind']!r}")


def check_relation(fqn, rel, fn, argnames):
    """Return list of failure strings (empty if the relation holds)."""
    fails = []
    rel = resolve_args(rel, argnames)
    factors = SCALE_FACTORS if rel["kind"] in ("scale", "joint_scale",
                                               "reciprocal_scale") else (Q(1),)
    for k in range(len(GRID_POINTS)):
        point = _assign(argnames, k)
        for c in factors:
            try:
                base = _call(fn, argnames, point)
                tp, _ = _transform(rel, argnames, point, c)
                got = _call(fn, argnames, tp)
                want = _expected(rel, base, None, c)
            except ZeroDivisionError:
                continue
            except (ValueError, OverflowError) as exc:
                fails.append(f"grid[{k}] c={c}: evaluation error {exc}")
                continue
            if not _close(got, want):
                fails.append(
                    f"grid[{k}] c={c} at "
                    + ", ".join(f"{a}={float(point[a]):g}" for a in argnames)
                    + f": f(T x)={got!r} but relation requires {want!r}")
    return fails


def in_scope_defs(table):
    """Extractable scalar real->real definitions, by module."""
    out = {}
    for name, d in table.items():
        if d.get("ret_type", "").strip() != "ℝ":
            continue
        ex = [a for a in d.get("args", []) if not a["implicit"]]
        argnames = [n for a in ex for n in a["names"]]
        if not argnames or not all(a["type"].strip() == "ℝ" for a in ex):
            continue
        out.setdefault(d.get("file", "?"), []).append(name)
    return out


def main(argv):
    table = api.definition_table()
    scope = in_scope_defs(table)
    findings = []

    if "--coverage" in argv:
        swept = sum(len(scope.get(m, [])) for m in R.SWEPT_MODULES)
        total = sum(len(v) for v in scope.values())
        print(f"scalar real->real definitions in the corpus: {total}")
        print(f"  in swept modules:  {swept}")
        print(f"  visible debt:      {total - swept} in "
              f"{len(scope) - len(R.SWEPT_MODULES)} unswept modules")
        for m in sorted(scope, key=lambda k: -len(scope[k]))[:15]:
            mark = "SWEPT" if m in R.SWEPT_MODULES else "     "
            print(f"  {mark} {len(scope[m]):4d}  {m}")
        return 0

    declared = (set(R.RELATIONS) | set(R.NO_RELATIONS)
                | set(R.NOT_EXTRACTABLE))

    # 1. every declared name must still exist -- catches renames and deletions
    #    without pinning a line number.
    for name in sorted(declared):
        if name not in table:
            findings.append(
                f"DANGLING: {name} is declared in relations.py but no longer "
                f"exists in the corpus. Rename or remove the declaration.")

    # 2. every in-scope definition of a swept module must be declared.
    for module in R.SWEPT_MODULES:
        if module not in scope:
            findings.append(
                f"EMPTY SWEEP: {module} is listed as swept but contributes no "
                f"in-scope definitions; the module was probably renamed.")
        for name in scope.get(module, []):
            if name not in declared:
                findings.append(
                    f"UNDECLARED: {name} ({module}) is a new in-scope "
                    f"definition with no metamorphic relations declared. Add it "
                    f"to RELATIONS, or to NO_RELATIONS with the reason none "
                    f"applies.")

    # 3. NOT_EXTRACTABLE must really be inextractable, or the excuse is stale.
    for name in sorted(R.NOT_EXTRACTABLE):
        if name not in table:
            continue
        try:
            api.callable_for(name)
        except Exception:
            continue
        findings.append(
            f"STALE EXCUSE: {name} is listed NOT_EXTRACTABLE but api.callable_for "
            f"now succeeds. Move it to RELATIONS and declare its relations.")

    # 4. the relations themselves.
    checked = 0
    for fqn, rels in sorted(R.RELATIONS.items()):
        if fqn not in table:
            continue                                    # already reported above
        try:
            fn, argnames = api.callable_for(fqn)
        except Exception as exc:
            findings.append(
                f"NOT EXECUTABLE: {fqn} is in RELATIONS but api.callable_for "
                f"raised {type(exc).__name__}: {exc}")
            continue
        for rel in rels:
            key = (fqn, rel["id"])
            try:
                fails = check_relation(fqn, rel, fn, argnames)
            except Violation as exc:
                findings.append(f"BAD DECLARATION: {fqn}: {exc}")
                continue
            checked += 1
            if key in R.EXPECTED_VIOLATIONS:
                if not fails:
                    findings.append(
                        f"UNEXPECTED AGREEMENT: {fqn} now SATISFIES "
                        f"{rel['id']}, which is pinned as a deliberate "
                        f"violation. The body changed. Reason on record: "
                        f"{R.EXPECTED_VIOLATIONS[key]}")
                continue
            if fails:
                findings.append(
                    f"VIOLATED: {fqn} does not satisfy {rel['id']}\n    "
                    + "\n    ".join(fails[:3])
                    + (f"\n    ... and {len(fails) - 3} more grid points"
                       if len(fails) > 3 else ""))

    swept_n = sum(len(scope.get(m, [])) for m in R.SWEPT_MODULES)
    print(f"metamorphic gate: {checked} relations over {len(R.RELATIONS)} "
          f"definitions; {swept_n} in-scope definitions across "
          f"{len(R.SWEPT_MODULES)} swept modules; "
          f"{len(R.EXPECTED_VIOLATIONS)} pinned violations.")
    if findings:
        print(f"\n{len(findings)} FINDING(S):\n")
        for f in findings:
            print("  " + f)
        return 1
    print("all declared relations hold; all pinned violations still violate.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

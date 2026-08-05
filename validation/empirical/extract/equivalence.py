"""Find definitions that compute the SAME FUNCTION under different names.

    python3 validation/extract/equivalence.py [--json out.json]

Identical output on every input is DECIDABLE.  It needs no simulation, no
ground truth, and no judgement about what a name asserts -- only the callables
the extractor already produces and a shared set of points.  That makes it the
one detector here that scales to the whole corpus.

WHY IT EXISTS.  Four names in the AUC family turned out to be one function:

    targetExactGaussianAUCFromNeutralAFBenchmark
    targetGaussianAUCFromNeutralAFBenchmark
    presentDayGaussianAUC
    presentDayEqualVarianceGaussianAUC

agreeing to 0.000e+00 across the admissible box.  That was found by a human
reading delegation chains and then evaluating four functions at eight points.
This finds that class mechanically, over every definition at once.

It also produced a headline theorem that was `rfl`:
`neutralAF_benchmark_discrimination_preserved_calibration_lost` asserts, as its
first conjunct, that one of those names equals another -- `f x = f x` in two
costumes.  The docstring reads "AUC is unchanged"; the statement would have held
just as well had AUC been wildly not preserved.  So this script also crosses the
equivalence classes against theorem statements, which is a mechanical vacuity
detector for theorems.

THREE THINGS IT IS CAREFUL ABOUT.

  1. It GROUPS, it does not compare pairwise.  Pairwise over ~1200 definitions
     is ~735k comparisons; hashing each definition's output vector and bucketing
     is linear and gives the equivalence classes directly.

  2. It separates AGREES-EVERYWHERE from AGREES-ON-THE-BOX.  Two definitions
     that agree on the admissible box but diverge outside it are a different
     finding from two that are definitionally equal: the first may be a genuine
     theorem about the admissible region, the second is a naming question.  Both
     are reported, under different headings, never merged.

  3. IT NEVER PICKS A WINNER.  A definition agreeing with another under a rename
     is the signal, not noise -- and it is not automatically a defect.
     `neiGstFromFrequencies` is algebraically identical to a Nei G_ST written
     the other way round, and it is CORRECTLY named.  The output is a list for a
     human to read, exactly as in verify_transcriptions.py.  Nothing here
     proposes a deletion.

WHAT IT CANNOT SEE.  Agreement at a finite sample of points is not proof of
equality; two genuinely different functions could agree at every sampled point.
The sample is fixed and reasonably large, and the extended-range pass makes an
accidental match much less likely, but a class reported here is a HYPOTHESIS
that two names denote one function, to be confirmed by reading the bodies.  The
converse is solid: definitions in different classes are definitely different.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import math
import pathlib
import random
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import admissible                                                # noqa: E402
import api                                                       # noqa: E402

N_POINTS = 24
SIGDIG = 10

# The two ranges.  BOX is the region the corpus treats as admissible for almost
# every quantity it defines -- rates, frequencies, variances.  WIDE deliberately
# leaves it, including negatives, so that two definitions which agree only
# because the box is narrow are separated from two that are the same function.
BOX = (0.05, 0.95)
WIDE = (-4.0, 9.0)


def _sig(name, d):
    """A shape key: only definitions of the same shape can be compared."""
    spec = api.vector_args(name) or {}
    try:
        _fn, argnames = api.callable_for(name)
    except Exception:                                            # noqa: BLE001
        return None, None
    parts = []
    for a in argnames:
        s = spec.get(a)
        parts.append(f"v{s['rank']}" if s else "s")
    return tuple(parts), argnames


def _points(shape, lo, hi, seed):
    rng = random.Random(seed)
    pts = []
    for _ in range(N_POINTS):
        row = []
        for kind in shape:
            if kind == "s":
                row.append(rng.uniform(lo, hi))
            elif kind == "v1":
                row.append([rng.uniform(lo, hi) for _ in range(4)])
            else:
                row.append([[rng.uniform(lo, hi) for _ in range(4)]
                            for _ in range(4)])
        pts.append(row)
    return pts


def _quant(v):
    """Round to SIGDIG significant digits so float noise does not split a class."""
    if isinstance(v, bool):
        return f"b{v}"
    if isinstance(v, (int, float)):
        if math.isnan(v):
            return "nan"
        if math.isinf(v):
            return f"inf{'+' if v > 0 else '-'}"
        if v == 0:
            return "0"
        return f"{v:.{SIGDIG}e}"
    if isinstance(v, (list, tuple)):
        return "[" + ",".join(_quant(x) for x in v) + "]"
    return "?" + type(v).__name__


def _fingerprint(fn, pts):
    out = []
    for row in pts:
        try:
            out.append(_quant(fn(*row)))
        except Exception:                                        # noqa: BLE001
            out.append("ERR")
    if all(x == "ERR" for x in out):
        return None, out
    h = hashlib.sha256("|".join(out).encode()).hexdigest()[:24]
    return h, out


def classes(verbose=False):
    api.refresh()
    table = api.definition_table()
    by_shape = collections.defaultdict(list)
    for name in table:
        shape, argnames = _sig(name, table[name])
        if shape is None or not argnames:
            continue
        by_shape[shape].append((name, argnames))

    box_groups = collections.defaultdict(list)
    wide_groups = collections.defaultdict(list)
    evaluated = 0
    for shape, members in by_shape.items():
        pts_box = _points(shape, *BOX, seed=20260803)
        pts_wide = _points(shape, *WIDE, seed=987654321)
        for name, _argnames in members:
            try:
                fn, _ = api.callable_for(name)
            except Exception:                                    # noqa: BLE001
                continue
            hb, _ = _fingerprint(fn, pts_box)
            hw, _ = _fingerprint(fn, pts_wide)
            if hb is None:
                continue
            evaluated += 1
            box_groups[(shape, hb)].append(name)
            wide_groups[(shape, hb, hw)].append(name)

    everywhere, on_box = [], []
    for key, names in box_groups.items():
        if len(names) < 2:
            continue
        sub = collections.defaultdict(list)
        for n in names:
            for k2, v2 in wide_groups.items():
                if k2[0] == key[0] and k2[1] == key[1] and n in v2:
                    sub[k2[2]].append(n)
                    break
        if len(sub) == 1:
            everywhere.append(sorted(names))
        else:
            on_box.append((sorted(names), [sorted(v) for v in sub.values()]))
    return evaluated, sorted(everywhere), sorted(on_box)


def normal_form(name):
    """The Lean body with argument names replaced by their POSITION.

    THE DISCRIMINATOR THAT MAKES THE OUTPUT READABLE.  Sixteen definitions --
    `snpH2`, `costEffectiveness`, `numBlocks`, `portabilityRatio`, ... -- land in
    one equivalence class because each of them is `x / y`.  They ARE the same
    function, so the detector is right, but they are not a naming defect: a
    ratio is a ratio, and nothing is collapsed.  Reporting them the same way as
    the AUC family would bury the finding under the arithmetic.

    So a class is split by whether its members share a body:

      SAME FORM      all bodies identical once argument names are positional.
                     Expected; two definitions of `a / b` are not a defect.
      DIFFERENT FORM different bodies, identical output.  THIS is the finding:
                     either a delegation chain that collapses two names onto one
                     computation, or an algebraic identity worth knowing about.
    """
    d = api.definition(name)
    body = " ".join((d["body"] or "").split())
    if not body:
        body = " ; ".join(f"{e['pattern']} => {e['rhs']}" for e in d["equations"])
    args = [n for a in d["args"] if not a["implicit"] for n in a["names"]]
    for i, a in enumerate(sorted(args, key=len, reverse=True)):
        body = re.sub(rf"(?<![\w'₀-₉]){re.escape(a)}(?![\w'₀-₉])", f"@{args.index(a)}", body)
    # Type ascriptions carry no computation: `(@0 : ℝ) / (@1 : ℝ)` is `@0 / @1`.
    # Leaving them in split the ratio class into three "distinct bodies" and
    # promoted fifteen definitions of `a / b` into the findings list.
    body = re.sub(r"\(\s*(@\d+)\s*:\s*[^)]*\)", r"\1", body)
    return " ".join(body.split())


def is_delegation(form, grp):
    """Is this body just a call to another member of the same class?

    That is the AUC pattern exactly: `targetExact… := targetGaussian…`, a name
    whose entire content is another name.  It is the single most likely shape
    for a genuine naming collapse, so classes containing one are reported first.
    """
    head = form.split()[0] if form.split() else ""
    return head in {n.split(".")[-1] for n in grp}


def split_by_form(grp):
    forms = collections.defaultdict(list)
    for n in grp:
        try:
            forms[normal_form(n)].append(n)
        except Exception:                                        # noqa: BLE001
            forms[f"<unreadable {n}>"].append(n)
    return forms


EQ = re.compile(r"=")


def vacuous_theorems(everywhere):
    """Theorems whose statement equates two members of one equivalence class.

    Such a statement is `rfl` -- true because both sides are the same function,
    not because of anything it claims.  Reported as CANDIDATES: a theorem may
    mention two equivalent definitions without asserting they are equal, so each
    hit needs reading.
    """
    member_of = {}
    for i, grp in enumerate(everywhere):
        for n in grp:
            member_of[n.split(".")[-1]] = i
    hits = []
    for tname, t in api.theorems().items():
        stmt = " ".join(t["statement"].split())
        if not EQ.search(stmt):
            continue
        seen = collections.defaultdict(set)
        for m in t.get("mentions", []):
            if m in member_of:
                seen[member_of[m]].add(m)
        for gi, names in seen.items():
            if len(names) >= 2:
                hits.append((tname, sorted(names), everywhere[gi], stmt))
    return hits


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=None)
    a = ap.parse_args(argv)
    api.require_fresh()
    # PRINT THE RESOLVED PATH AND REVISION OF EVERY INPUT.  The freshness gate
    # refuses on a stale table, but it cannot tell that someone pointed this at
    # the right file in the wrong tree.  A run that names its inputs can be
    # checked by a reader; one that does not has to be trusted.
    st = api.stamp()
    print(f"table   : {(HERE / 'defs.json').resolve()}")
    print(f"module  : {(HERE / 'lean_defs.py').resolve()}")
    print(f"corpus  : {st['source_digest_on_disk']} over {st['source_files']} "
          f"files, {st['n_definitions']} definitions")
    print(f"current : {st['table_is_current']}\n")
    evaluated, everywhere, on_box = classes()

    print("=" * 78)
    print("DEFINITIONS THAT AGREE AT EVERY SAMPLED POINT, ON AND OFF THE BOX")
    print("=" * 78)
    print(f"  {len(everywhere)} class(es).  These are candidates for 'two names,")
    print("  one function'.  Some are correct aliases; none is automatically a")
    print("  defect.  Read the bodies before concluding anything.")
    same_form, diff_form = [], []
    for grp in everywhere:
        (same_form if len(split_by_form(grp)) == 1 else diff_form).append(grp)

    def rank(g):
        forms = split_by_form(g)
        return (-sum(is_delegation(f, g) for f in forms), -len(forms))

    print(f"\n  {len(diff_form)} class(es) where the BODIES DIFFER -- these are the")
    print("  findings: different source text, identical output at every point.")
    print("  Classes containing a DELEGATION (a body that is just a call to")
    print("  another member) come first: that is the AUC pattern.")
    for grp in sorted(diff_form, key=rank):
        forms = split_by_form(grp)
        ndel = sum(is_delegation(f, grp) for f in forms)
        tag = "  <-- DELEGATION" if ndel else ""
        print(f"\n  --- {len(grp)} names, {len(forms)} distinct bodies{tag}")
        for form, names in sorted(forms.items(), key=lambda kv: -len(kv[1])):
            mark = "DELEGATES: " if is_delegation(form, grp) else ""
            print(f"        {mark}body: {form[:130]}")
            if len(names) <= 4 or is_delegation(form, grp):
                for n in names:
                    c = api.classification(n)
                    print(f"           {n}   ({c['file']}:{c['line']})")
            else:
                print(f"           {len(names)} names: "
                      + ", ".join(n.split('.')[-1] for n in names)[:200])

    print(f"\n  {len(same_form)} class(es) where every member has the SAME BODY once")
    print("  argument names are made positional.  Expected, not a defect: two")
    print("  definitions of `a / b` are both `a / b`.  Listed compactly.")
    for grp in sorted(same_form, key=len, reverse=True):
        form = next(iter(split_by_form(grp)))
        print(f"    [{len(grp)}] {form[:60]}")
        print(f"         {', '.join(n.split('.')[-1] for n in grp)[:300]}")

    print("\n" + "=" * 78)
    print("DEFINITIONS THAT AGREE ONLY ON THE ADMISSIBLE BOX")
    print("=" * 78)
    print("  These diverge outside it, so they are NOT the same function.  An")
    print("  agreement here may be a genuine theorem about the admissible")
    print("  region rather than a naming problem.")
    for grp, subs in on_box:
        print(f"\n  --- {len(grp)} names, splitting into {len(subs)} off-box:")
        for n in grp:
            print(f"        {n}")

    hits = vacuous_theorems(everywhere)
    print("\n" + "=" * 78)
    print("THEOREMS THAT EQUATE TWO NAMES FOR ONE FUNCTION  (rfl candidates)")
    print("=" * 78)
    print("  A statement relating two members of one equivalence class is true")
    print("  because the two sides are the same function.  Whatever its docstring")
    print("  claims, it would hold just as well if the claim were false.")
    for tname, names, _grp, stmt in hits:
        print(f"\n  {tname}")
        print(f"     equates: {', '.join(names)}")
        print(f"     statement: {stmt[:220]}")
    if not hits:
        print("  none found")

    print("\n" + "=" * 78)
    print(f"  definitions evaluated            : {evaluated}")
    print(f"  classes agreeing everywhere      : {len(everywhere)}")
    print(f"  classes agreeing only on the box : {len(on_box)}")
    print(f"  rfl-candidate theorems           : {len(hits)}")
    print("=" * 78)

    if a.json:
        pathlib.Path(a.json).write_text(json.dumps({
            "stamp": api.stamp(),
            "n_evaluated": evaluated,
            "agree_everywhere": everywhere,
            "agree_everywhere_different_bodies": [
                g for g in everywhere if len(split_by_form(g)) > 1],
            "agree_on_box_only": [g for g, _ in on_box],
            "rfl_candidate_theorems": [
                {"theorem": t, "equated": n, "class": g, "statement": s}
                for t, n, g, s in hits],
        }, indent=1, ensure_ascii=False))
        print(f"written: {a.json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

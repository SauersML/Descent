"""FAMILY 2 -- metamorphic invariants.

An invariant relates a definition's value at one input to its value at
another.  It needs no reference implementation and no simulation, which is why
it scales to a whole corpus.  Six kinds are derived here, all of them from the
definition's own name, docstring, signature and adjacent theorems:

  SYMMETRY      a between-population quantity is unchanged when the two
                populations are swapped.
  SCALE         a dimensionless quantity is unchanged when every second-moment
                argument is multiplied by the same positive constant.
  LIMIT         a quantity with a stated limit attains it: F_ST -> 0 as Ne
                grows, heterozygosity -> 0 as a frequency approaches fixation,
                a decay -> its equilibrium as the rate goes to zero.
  ABSORBING     loss and fixation are absorbing.  An allele at frequency 0
                stays at 0; at frequency 1 it stays at 1.  A smooth formula
                that leaves the boundary is a qualitative error.
  MONOTONE      a direction the docstring or an adjacent theorem name asserts
                actually holds.
  IDENTITY      a value the docstring pins at a specific input.

Every registration records WHY it applies.  Where nothing can be derived, the
definition is recorded with `reason` and counted in the residue, never
silently skipped.
"""
from __future__ import annotations

import math
import random
import re

from backends import FLOAT
from semantics import admissible_box, param_box, result_name

INF = math.inf

# --------------------------------------------------------------------------
# which quantities must be symmetric under swapping the two populations

SYMMETRIC_NAME = re.compile(
    r"fst|divergence|distance|similarity|overlap|shared|coancestry|"
    r"differentiation|betweenpop|crosspop|jaccard|concordance", re.I
)
# ... and which must NOT be: an ordered quantity names its own direction
ORDERED_NAME = re.compile(
    r"fromsource|totarget|sourceto|targetto|transfer|portab|gain|loss|"
    r"improvement|regret|ratio|relative|shift|drop|delta", re.I
)

# role suffixes that distinguish the two members of a pair
PAIR_SUFFIX = [
    ("source", "target"), ("src", "tgt"), ("a", "b"), ("1", "2"),
    ("₁", "₂"), ("i", "j"),
    # NOT ("s","t") or ("x","y"): `ETss`/`ETst` are a within- and a
    # between-population coalescence time, not the same quantity twice.
    ("pop1", "pop2"), ("popa", "popb"), ("first", "second"),
    ("eur", "afr"), ("train", "test"), ("disc", "repl"),
]

DIMENSIONLESS = re.compile(
    r"fst|r2|rsq|correlation|proportion|fraction|share|portability|"
    r"heritability|ratio|probability|retention|attenuation|auc|index", re.I
)
SECOND_MOMENT = re.compile(
    # `tau`/`τ` are deliberately absent: in this corpus they are coalescent
    # branch lengths already measured in units of 2Ne generations, so scaling
    # one is not a change of units and `tau/(1+tau)` is right to depend on it.
    r"var(?!iate)|sigma|σ|cov(?!ariate)|moment|noise|signal|mse|"
    r"v_[a-z]|^v[A-Z]", re.I
)
# A name ending in `_sq` is a SQUARED second moment: it scales as c², not c,
# so it cannot be pooled with plain variances in one scaling transformation.
# `tagR2 (D_sq var_tag var_causal)` is dimensionless, but only under
# `D_sq -> c² D_sq`, and scaling all three by `c` breaks it legitimately.
DEGREE_TWO = re.compile(r"(sq|squared)$", re.I)

FREQ_PARAM = re.compile(r"^(p|q|p[₀₁₂0-9]|p_\w+|freq\w*|alleleFreq\w*)$", re.I)
NE_PARAM = re.compile(r"^(ne|n_e|nₑ|ne\w*|effectiveN\w*|popSize)$", re.I)
# A forward map of an allele frequency.  `meanAlleleFreq` and
# `alleleFreqAfterMigration`'s CONTINENT frequency are not state variables, so
# neither the name test nor the parameter test alone is enough.
MAP_NAME = re.compile(r"step|update|next|iterate|recurrence", re.I)
STATE_PARAM = re.compile(r"^(p|p₀|p0|p_t|freq|pCurrent)$", re.I)
# Mutation reintroduces a lost allele and migration pulls a fixed one back
# down, so neither boundary is absorbing when those forces are present.
MUTATION_PARAM = re.compile(r"^(mu|μ|u|mutationRate|theta|θ)$", re.I)
MIGRATION_PARAM = re.compile(r"^(m|m₁₂|m₂₁|mig\w*|migrationRate|p_c)$", re.I)


def _stem_pairs(names):
    """Pairs of parameters that name the same quantity for two populations."""
    out = []
    low = [n.lower() for n in names]
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            a, b = low[i], low[j]
            for sa, sb in PAIR_SUFFIX:
                if a.endswith(sa) and b.endswith(sb) and a[: -len(sa)] == b[: -len(sb)]:
                    if a[: -len(sa)] or len(names) == 2:
                        out.append((i, j, f"`{names[i]}`/`{names[j]}` are the "
                                          f"same quantity for two populations"))
                        break
    return out


def _sample(box, names, rng, n=400):
    from search import _draw

    pts = []
    for _ in range(n):
        pts.append([_draw(rng, box[nm]) for nm in names])
    return pts


def _ev(c, x):
    try:
        v = c(FLOAT, *x)
    except Exception:
        return None
    if v is None or isinstance(v, bool) or v != v or math.isinf(v):
        return None
    return float(v)


def _rel(a, b):
    return abs(a - b) / max(1.0, abs(a), abs(b))


# --------------------------------------------------------------------------


def derive(c, feasible=None, seed=None, n=400):
    """Return (checks, skipped) for one compiled definition.

    Each check is a dict with `kind`, `why` (the evidence that it applies) and
    `run(c)` producing (ok, detail).
    """
    d = c.d
    names = c.names
    box, _ = admissible_box(d)
    blind = [nm for nm in names if box[nm]["source"] == "none"]
    import seeds as _s
    rng = random.Random(_s.sub("invariants") if seed is None else seed)
    pts = _sample(box, names, rng, n)
    if feasible is not None:
        pts = [p for p in pts if _safe(feasible, p)]
    checks, skipped = [], []
    rname = result_name(d)
    doc = d.get("doc", "") or ""

    # ---- SYMMETRY -------------------------------------------------------
    pairs = _stem_pairs(names)
    if pairs and SYMMETRIC_NAME.search(rname) and not ORDERED_NAME.search(rname):
        for i, j, why in pairs:
            checks.append(_symmetry_check(c, pts, i, j, why))
    elif not pairs:
        skipped.append(("symmetry", "no two parameters name the same quantity "
                                    "for two populations"))
    else:
        skipped.append(("symmetry", f"`{rname}` does not name a symmetric "
                                    "between-population quantity"))

    # ---- SCALE INVARIANCE ----------------------------------------------
    mom = [k for k, nm in enumerate(names) if SECOND_MOMENT.search(nm)]
    deg2 = [k for k in mom if DEGREE_TWO.search(names[k])]
    if len(mom) != len(names) or deg2:
        skipped.append(("scale",
                        "the scaling transformation is only well defined when "
                        "every argument is a second moment of the same degree; "
                        f"here moments are {[names[k] for k in mom]} of "
                        f"{list(names)}"
                        + (f" and {[names[k] for k in deg2]} are squared"
                           if deg2 else "")))
    elif mom and DIMENSIONLESS.search(rname):
        checks.append(_scale_check(c, pts, mom,
                                   f"`{rname}` is dimensionless and "
                                   f"{[names[k] for k in mom]} are second "
                                   "moments, so scaling them together must "
                                   "leave the value unchanged"))
    elif not mom:
        skipped.append(("scale", "no second-moment argument to scale"))
    else:
        skipped.append(("scale", f"`{rname}` is not evidently dimensionless"))

    # ---- ABSORBING BOUNDARY --------------------------------------------
    fq = [k for k, nm in enumerate(names) if FREQ_PARAM.match(nm)]
    state = [k for k, nm in enumerate(names) if STATE_PARAM.match(nm)]
    has_mut = any(MUTATION_PARAM.match(nm) for nm in names)
    has_mig = any(MIGRATION_PARAM.match(nm) for nm in names)
    if state and MAP_NAME.search(d["name"]) and not blind:
        k = state[0]
        ends = []
        if not has_mut:
            ends.append((0.0, 0.0, "loss"))
        if not has_mut and not has_mig:
            ends.append((1.0, 1.0, "fixation"))
        if ends:
            checks.append(_absorbing_check(
                c, pts, k, ends,
                f"`{d['name']}` steps an allele frequency forward in `{names[k]}`"
                f"; {' and '.join(e[2] for e in ends)} "
                f"{'is' if len(ends) == 1 else 'are'} absorbing"
                + (" (mutation reintroduces a lost allele, so only fixation "
                   "would be at issue)" if has_mut else "")
                + (" (migration pulls a fixed allele back, so fixation is not "
                   "absorbing here)" if has_mig and not has_mut else "")))
        else:
            skipped.append(("absorbing", "mutation is present, so neither "
                                         "boundary is absorbing"))
    elif not state:
        skipped.append(("absorbing", "no allele-frequency state argument"))
    elif blind:
        skipped.append(("absorbing", f"cannot place a physically meaningful "
                                     f"box on {blind}"))
    else:
        skipped.append(("absorbing", f"`{d['name']}` is not a one-generation "
                                     "frequency map"))

    # ---- LIMITS ---------------------------------------------------------
    ne = [k for k, nm in enumerate(names) if NE_PARAM.match(nm)]
    if blind:
        skipped.append(("limit-Ne", f"cannot place a physically meaningful box "
                                    f"on {blind}"))
    elif ne and re.search(r"fst|differentiation", rname, re.I) \
            and not re.search(r"step|next|update|iterate", d["name"], re.I):
        # With NO gene flow the demes are independent and F_ST tends to one,
        # not zero, however large Ne is.  That is correct behaviour, so the
        # degenerate m = 0 slice is excluded rather than reported.
        mig = [k for k, nm in enumerate(names) if MIGRATION_PARAM.match(nm)]
        lpts = [x for x in pts if all(x[k] > 0 for k in mig)]
        checks.append(_tendsto_check(
            c, lpts, ne[0],
            f"`{rname}` is an equilibrium differentiation and gene flow "
            f"overwhelms drift as `{names[ne[0]]}` grows without bound, so the "
            "value must decrease to zero"))
    elif not ne:
        skipped.append(("limit-Ne", "no effective-population-size argument"))
    elif ne and re.search(r"step|next|update|iterate", d["name"], re.I):
        skipped.append(("limit-Ne", f"`{d['name']}` is a one-generation step, "
                                    "not an equilibrium; its large-Ne limit is "
                                    "the no-drift map, not zero"))
    else:
        skipped.append(("limit-Ne", f"`{rname}` is not an F_ST-like quantity; "
                                    "a retention or drift FACTOR tends to one, "
                                    "not zero, so the direction is not "
                                    "derivable from the name alone"))

    if fq and re.search(r"heterozygosity|^het|diversity", rname, re.I):
        for k in fq:
            checks.append(_limit_check(
                c, pts, k, 0.0, 0.0,
                f"heterozygosity vanishes when `{names[k]}` reaches loss"))
            checks.append(_limit_check(
                c, pts, k, 1.0, 0.0,
                f"heterozygosity vanishes when `{names[k]}` reaches fixation"))
    else:
        skipped.append(("limit-freq", "not a heterozygosity of a frequency"))

    # ---- MONOTONICITY ---------------------------------------------------
    # ---- BOUNDARY CONTINUITY (Lean junk values) -------------------------
    # Lean totalises partial operations: `x / 0 = 0`, `Real.sqrt x = 0` for
    # x < 0, `Real.log x = 0` for x <= 0.  A definition whose denominator
    # vanishes at an endpoint of its own admissible box therefore returns 0
    # there, silently, and the surrounding theorems still typecheck.  This is
    # the mechanism behind `equalVarianceGaussianAUCFromExplainedR2` returning
    # 0.5 -- chance-level AUC -- at r2 = 1, where the AUC should be 1.
    if not blind:
        for k in range(len(names)):
            checks.append(_continuity_check(c, pts, k, box, names[k],
                          f"`{names[k]}` reaches {box[names[k]]['lo']:g} and "
                          f"{box[names[k]]['hi']:g} inside the admissible box, "
                          "so the value there must agree with the limit from "
                          "inside; a jump means a Lean junk value is being "
                          "returned as if it were the quantity"))
    else:
        skipped.append(("continuity", f"cannot place a physically meaningful "
                                      f"box on {blind}"))

    claims = _monotone_claims(d, names)
    if claims and blind:
        skipped.append(("monotone", f"a direction is asserted but no "
                                    f"physically meaningful box exists on "
                                    f"{blind}, so a violation could not be "
                                    "distinguished from an out-of-domain input"))
        claims = []
    for k, direction, why in claims:
        checks.append(_monotone_check(c, pts, k, direction, why, box))
    if not claims and not blind:
        skipped.append(("monotone", "neither the docstring nor an adjacent "
                                    "theorem name asserts a direction"))

    return checks, skipped


def _safe(f, x):
    try:
        return bool(f(*x))
    except Exception:
        return False


# --------------------------------------------------------------------------
# individual check constructors.  Each returns a dict with a `run` closure.


def _mk(kind, why, run, param=None):
    return dict(kind=kind, why=why, run=run, param=param)


def _symmetry_check(c, pts, i, j, why):
    def run(cc):
        worst, wx = 0.0, None
        for x in pts:
            y = list(x)
            y[i], y[j] = y[j], y[i]
            a, b = _ev(cc, x), _ev(cc, y)
            if a is None or b is None:
                continue
            r = _rel(a, b)
            if r > worst:
                worst, wx = r, (list(x), y, a, b)
        return worst <= 1e-9, dict(max_relative_asymmetry=worst, witness=wx)

    return _mk("symmetry", why, run, param=(i, j))


def _scale_check(c, pts, mom, why):
    def run(cc):
        worst, wx = 0.0, None
        for x in pts:
            for s in (2.0, 7.5, 0.1):
                y = list(x)
                for k in mom:
                    y[k] = x[k] * s
                a, b = _ev(cc, x), _ev(cc, y)
                if a is None or b is None:
                    continue
                r = _rel(a, b)
                if r > worst:
                    worst, wx = r, (list(x), y, a, b, s)
        return worst <= 1e-9, dict(max_relative_change=worst, witness=wx)

    return _mk("scale", why, run, param=tuple(mom))


def _absorbing_check(c, pts, k, ends, why):
    def run(cc):
        bad = []
        for x in pts[:60]:
            for p, want, label in ends:
                y = list(x)
                y[k] = p
                v = _ev(cc, y)
                if v is None:
                    continue
                if abs(v - want) > 1e-9:
                    bad.append(dict(at=y, got=v, expected=want, boundary=label))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("absorbing", why, run, param=k)  # noqa: E501


def _tendsto_check(c, pts, k, why, ladder=(1e3, 1e6, 1e9, 1e12)):
    """The value decreases along a ladder in `k` and ends near zero.

    Checking equality with zero at one huge value of Ne only measures the rate
    of approach and fails on slowly-converging but perfectly correct formulas
    (`d / (d + 4 Ne m σ²)` needs a very large Ne when σ² is small).  The
    ladder tests the LIMIT rather than the rate.
    """
    def run(cc):
        bad = []
        for x in pts[:60]:
            vals = []
            for v in ladder:
                y = list(x)
                y[k] = v
                r = _ev(cc, y)
                if r is None:
                    break
                vals.append(r)
            if len(vals) < len(ladder):
                continue
            decreasing = all(b <= a + 1e-12 for a, b in zip(vals, vals[1:]))
            vanishing = abs(vals[-1]) <= max(1e-3 * abs(vals[0]), 1e-8)
            if not (decreasing and vanishing):
                bad.append(dict(at=x, ladder=list(ladder), values=vals,
                                decreasing=decreasing, vanishing=vanishing))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("limit", why, run, param=k)


def _limit_check(c, pts, k, at, want, why, tol=1e-6):
    def run(cc):
        bad = []
        for x in pts[:60]:
            y = list(x)
            y[k] = at
            v = _ev(cc, y)
            if v is None:
                continue
            if abs(v - want) > tol:
                bad.append(dict(at=y, got=v, expected=want))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("limit", why, run, param=k)


MONO_DOC = re.compile(
    r"(increas\w*|decreas\w*|grows|declines|rises|falls|larger|smaller)\s+"
    r"(?:monotonically\s+)?(?:with|in)\s+`?([A-Za-z_][\w'₀-₉]*)`?", re.I
)
MONO_THM = re.compile(
    r"(increas\w*|decreas\w*)_(?:with|in)_([A-Za-z_][\w'₀-₉]*)", re.I
)


def _monotone_claims(d, names):
    """(param_index, +1/-1, evidence) for every asserted direction."""
    out = []
    doc = d.get("doc", "") or ""
    for m in MONO_DOC.finditer(doc):
        word, p = m.group(1).lower(), m.group(2)
        if p not in names:
            continue
        sign = 1 if word.startswith(("increas", "grow", "rise", "larger")) else -1
        out.append((names.index(p), sign,
                    f"the docstring says the value {m.group(1)} with `{p}`"))
    stem = d["name"].lower()
    for t in d.get("theorem_hyps", []):
        # A theorem may mention several definitions; only one of them is the
        # subject of its name.  `recurrence_derived_R2_increases_with_m` is
        # about an R², not about the F_ST it happens to reference, and F_ST
        # moves the other way.
        if stem not in t["thm"].lower().replace("_", ""):
            continue
        for m in MONO_THM.finditer(t["thm"]):
            word, p = m.group(1).lower(), m.group(2)
            p = (t.get("argmap") or {}).get(p, p)
            if p not in names:
                continue
            sign = 1 if word.startswith("increas") else -1
            out.append((names.index(p), sign,
                        f"theorem `{t['thm']}` asserts the direction"))
    # dedupe on (index, sign)
    seen, ded = set(), []
    for i, s, w in out:
        if (i, s) in seen:
            continue
        seen.add((i, s))
        ded.append((i, s, w))
    return ded


def _monotone_check(c, pts, k, sign, why, box):
    def run(cc):
        bad = []
        lo, hi = box[c.names[k]]["lo"], box[c.names[k]]["hi"]
        for x in pts[:120]:
            y = list(x)
            step = max(abs(x[k]) * 0.5, (hi - lo) * 1e-3, 1e-9)
            y[k] = min(x[k] + step, hi)
            if y[k] == x[k]:
                continue
            a, b = _ev(cc, x), _ev(cc, y)
            if a is None or b is None:
                continue
            if sign * (b - a) < -1e-12 * max(1.0, abs(a)):
                bad.append(dict(at=list(x), then=y, f_at=a, f_then=b))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("monotone", why, run, param=k)


def _continuity_check(c, pts, k, box, pname, why):
    """Detect a JUMP at a box endpoint, not merely a steep approach.

    Three points: the endpoint itself and two interior points at 1e-4 and 1e-6
    of the box width.  A smooth-but-steep function moves a lot between the two
    interior points and only a little more over the final, hundred-fold
    smaller step.  A junk value does the opposite: the two interior points
    nearly agree and the endpoint sits somewhere else entirely.  Requiring the
    final step to dominate the earlier, much longer one is what separates the
    two, and it is why `1/(1-x)` near x=1 is not reported while
    `Phi(sqrt(r2/(2*(1-r2))))` at r2=1 is.
    """
    lo, hi = box[pname]["lo"], box[pname]["hi"]
    w = hi - lo
    logscale = box[pname]["scale"] in ("log", "log1p")
    if not math.isfinite(w) or w <= 0:
        def run(cc):
            return None, dict(skipped="unbounded coordinate")

        return _mk("continuity", why, run, param=k)

    def probe(end, sign, frac):
        """A point just inside the box, on the coordinate's own scale.

        On a log-scale coordinate spanning nine orders of magnitude, a
        fraction of the box WIDTH is nowhere near the lower endpoint: for a
        variance in [1e-6, 1e3], `lo + 1e-4 * w` is 0.1.  Probing has to be
        multiplicative there or the check compares two unrelated points and
        reports every steep function as discontinuous.
        """
        if logscale and end > 0:
            return end * (1.0 + sign * frac)
        # A linear box can still have an endpoint many orders of magnitude
        # smaller than its width (a heterozygosity in [1e-9, 1]).  Stepping by
        # a fraction of the WIDTH then lands a thousand-fold away from the
        # endpoint, so the step is taken relative to whichever is smaller.
        base = min(w, abs(end)) if end != 0.0 else w
        return end + sign * frac * base

    def run(cc):
        bad = []
        for x in pts[:40]:
            for end, sign in ((lo, +1.0), (hi, -1.0)):
                y = list(x)
                y[k] = end
                at = _ev(cc, y)
                if at is None:
                    continue
                near = []
                for frac in (1e-4, 1e-6, 1e-8):
                    z = list(x)
                    z[k] = probe(end, sign, frac)
                    v = _ev(cc, z)
                    if v is None:
                        break
                    near.append(v)
                if len(near) < 3:
                    continue
                v4, v6, v8 = near
                # A merely STEEP function still converges: each closer probe
                # moves less and approaches the endpoint value.  A junk value
                # is the opposite -- the interior probes settle on a limit and
                # the endpoint sits somewhere else.  Requiring convergence of
                # the interior sequence is what separates `exp(-t/tau)` at
                # t = 0 from `Phi(sqrt(r2/(2*(1-r2))))` at r2 = 1.
                converging = abs(v8 - v6) <= 0.5 * abs(v6 - v4) + 1e-300
                jump = abs(at - v8)
                scale = max(1.0, abs(at), abs(v8))
                if converging and jump / scale > 1e-6 and \
                        jump > 100.0 * abs(v8 - v6):
                    bad.append(dict(at=y, endpoint=f"{pname}={end:g}",
                                    value_at_endpoint=at,
                                    limit_from_inside=v8,
                                    interior_probes=[v4, v6, v8],
                                    jump=jump))
        return not bad, dict(violations=bad[:5], n_violations=len(bad))

    return _mk("continuity", why, run, param=k)

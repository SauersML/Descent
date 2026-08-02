"""Find definitions that leave their declared range where no theorem guards them.

THE GAP THIS SEARCHES FOR
-------------------------
`neutralAFBenchmarkRatio` is declared an F_ST-like ratio in [0,1] and returns
2.4.  Every theorem about it is true, because the one that bounds it below 1
(`neutralAFBenchmarkRatio_lt_one`) requires `fstSource < fstTarget`, and 2.4
happens where that precondition fails.  The proofs are all correct; the region
is simply unguarded.

Range-based coverage scores such a definition as covered, on the strength of
the bounds it does satisfy.  Mutation testing does not see it either: the body
is exactly what its author intended.  So this is a third blind spot alongside
the two already on record, and unlike those two it can be searched for
mechanically.

WHAT IS AND IS NOT A DEFECT
---------------------------
A definition leaving a bound is only interesting relative to WHO CLAIMED the
bound, so every hit is classified by the provenance of the claim -- the two
kinds are never merged:

  UNGUARDED-DOCSTRING  the value leaves a range mined from PROSE, and no
                       theorem proves that bound anywhere. The docstring claims
                       something the corpus never established. Real finding,
                       but it is a documentation defect until someone decides
                       which of the two is wrong.

  UNGUARDED-PROVEN     the value leaves a bound that IS proven by some theorem,
                       at a point where that theorem's preconditions do not
                       hold. The theorem is true and the region is unguarded.
                       This is the neutralAFBenchmarkRatio shape and the most
                       interesting class: it says the proved scope is narrower
                       than the name implies.

  IN-SCOPE-VIOLATION   the value leaves a proven bound at a point where the
                       proving theorem's preconditions DO hold. That cannot
                       happen if Lean is consistent and the extraction is
                       faithful, so it indicts the extraction or this scanner,
                       never the corpus. Reported loudly and separately.

Points are scanned inside `api.admissible_box`, and Mathlib totality applies
throughout because the callables come from extract (`lean_rt`).
"""

from __future__ import annotations

import itertools
import math
import sys

import corpus

api = corpus.api

# Definitions whose declared range is a units/kind label rather than a claim
# about every input (a "probability" that is only a probability on part of its
# domain would be caught here as noise).  Nothing is excluded yet; the list
# exists so exclusions must be named rather than silently applied.
EXCLUDE: set[str] = set()

GRID_PER_AXIS = 7


def _axis_points(lo: float, hi: float, n: int = GRID_PER_AXIS) -> list[float]:
    """Points across [lo, hi], including the endpoints and interior spread.

    Endpoints matter: the AUC-at-r2=1 artefact and the F_ST-at-t=0 degeneracies
    both live exactly there, and an interior-only grid misses them.
    """
    if hi <= lo:
        return [lo]
    return [lo + (hi - lo) * i / (n - 1) for i in range(n)]


def _proving_theorems(con: dict) -> dict[str, list[str]]:
    """Which theorem proves the low bound, and which the high bound."""
    out = {}
    for key, side in (("range_lo_thm", "lo"), ("range_hi_thm", "hi")):
        v = con.get(key)
        if isinstance(v, (list, tuple)) and v:
            out[side] = v[0]
    return out


def scan_definition(fq: str) -> dict | None:
    """Scan one definition's admissible box for out-of-range values."""
    try:
        d = api.definition(fq)
        con = d.get("constraints") or {}
    except Exception:
        return None
    if api.vector_args(fq):
        return None  # sequence-valued: the box has no scalar grid
    lo, hi = con.get("declared_lo"), con.get("declared_hi")
    if lo is None and hi is None:
        return None
    try:
        fn, argnames = api.callable_for(fq)
        box = api.admissible_box(fq)
    except Exception:
        return None
    if not argnames or not box or any(a not in box for a in argnames):
        return None

    axes = [_axis_points(*box[a]) for a in argnames]
    if math.prod(len(a) for a in axes) > 20000:
        return None

    prov = _proving_theorems(con)
    hits = []
    for combo in itertools.product(*axes):
        point = dict(zip(argnames, combo))
        try:
            v = fn(*combo)
        except Exception:
            continue
        if not isinstance(v, (int, float)) or not math.isfinite(v):
            continue
        for side, bound, out in (("lo", lo, v < lo if lo is not None else False),
                                 ("hi", hi, v > hi if hi is not None else False)):
            if not out:
                continue
            thm = prov.get(side)
            if thm is None:
                kind = "UNGUARDED-DOCSTRING"
                thm_holds = None
            else:
                try:
                    thm_holds = api.satisfies(fq, point, thm)
                except Exception:
                    thm_holds = None
                kind = "IN-SCOPE-VIOLATION" if thm_holds else "UNGUARDED-PROVEN"
            hits.append({
                "point": point, "value": v, "side": side, "bound": bound,
                "kind": kind, "proving_theorem": thm,
                "theorem_preconditions_hold": thm_holds,
            })
    if not hits:
        return None
    worst = max(hits, key=lambda h: abs(h["value"] - h["bound"]))
    kinds = {h["kind"] for h in hits}
    return {
        "definition": fq,
        "source": f"{d['file']}:{d['line']}",
        "declared_kind": con.get("declared_kind"),
        "declared_range": [lo, hi],
        "declared_provenance": "mined from prose; NOT machine-checked",
        "range_proving_theorems": prov,
        "n_points_scanned": math.prod(len(a) for a in axes),
        "n_out_of_range": len(hits),
        "kinds": sorted(kinds),
        "worst": worst,
        "empirical_status": d.get("empirical_status"),
    }


def scan_all(limit: int | None = None) -> list[dict]:
    out = []
    names = sorted(api.definition_table())
    for fq in names[:limit] if limit else names:
        if fq in EXCLUDE:
            continue
        r = scan_definition(fq)
        if r:
            out.append(r)
    return out


if __name__ == "__main__":
    import json

    res = scan_all()
    order = {"IN-SCOPE-VIOLATION": 0, "UNGUARDED-PROVEN": 1, "UNGUARDED-DOCSTRING": 2}
    res.sort(key=lambda r: (order.get(r["kinds"][0], 9),
                            -abs(r["worst"]["value"] - r["worst"]["bound"])))
    print(f"{len(res)} definitions leave their declared range somewhere in their box\n")
    for r in res:
        w = r["worst"]
        print(f"{w['kind']:<20} {r['definition']:<52} "
              f"declared {r['declared_range']} -> {w['value']:.6g}")
        print(f"    {r['source']}  at {w['point']}  "
              f"({r['n_out_of_range']}/{r['n_points_scanned']} points)")
        if w["proving_theorem"]:
            print(f"    bound proven by {w['proving_theorem']}, "
                  f"preconditions hold: {w['theorem_preconditions_hold']}")
    json.dump(res, open("unguarded.json", "w"), indent=1, default=str)
    print(f"\n-> unguarded.json")

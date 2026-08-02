"""Run the differential battery and emit machine-readable results.

    python3.13 run.py [--json results.json]

No sampling, no build, no Lean invocation.  Runtime is under a second.
"""

from __future__ import annotations

import argparse
import inspect
import json
import math
import os
import sys

import checks
import contracts
import corpus


def _wants_corpus(fn) -> bool:
    params = list(inspect.signature(fn).parameters)
    return bool(params) and params[0] == "D"


def _eval(fn, D, params):
    return fn(D, **params) if _wants_corpus(fn) else fn(**params)


def evaluate(chk: checks.Check, D) -> dict:
    """Evaluate one check over its grid.  Returns per-point rows and a summary."""
    rows = []
    worst = None
    for p in chk.grid:
        try:
            lv = _eval(chk.lean, D, p)
            rv = _eval(chk.ref, D, p)
        except Exception as e:  # a missing dependency must be loud, not silent
            rows.append({"params": p, "error": f"{type(e).__name__}: {e}"})
            continue
        err = checks._relerr(lv, rv, chk.atol)
        row = {"params": p, "lean": lv, "ref": rv, "rel_err": err}
        rows.append(row)
        if worst is None or err > worst["rel_err"]:
            worst = row
    errs = [r["rel_err"] for r in rows if "rel_err" in r]
    return {
        "rows": rows,
        "max_rel_err": max(errs) if errs else None,
        "min_rel_err": min(errs) if errs else None,
        "worst_point": worst,
        "n_errors": sum(1 for r in rows if "error" in r),
    }


# --------------------------------------------------------------------------
# Non-vacuity: does this check have the power to fail?
# --------------------------------------------------------------------------
def _mutants(D: dict) -> list[tuple[str, dict]]:
    """Corpus tables in which every definition is deliberately wrong.

    If a check still passes against one of these, the check is vacuous: it is
    not actually constraining the definition it names.
    """
    def scaled(factor):
        return {k: (lambda f=v, c=factor: (lambda *a, **kw: f(*a, **kw) * c))()
                for k, v in D.items()}

    def transposed():
        out = {}
        for k, v in D.items():
            def t(*a, _f=v, **kw):
                if len(a) >= 2:
                    a = (a[1], a[0]) + a[2:]
                return _f(*a, **kw)
            out[k] = t
        return out

    return [
        ("scale x1.05", scaled(1.05)),
        ("scale x0.5", scaled(0.5)),
        ("transpose first two args", transposed()),
    ]


def prove_can_fail(chk: checks.Check, D) -> dict:
    """Confirm the check separates the real definition from wrong ones."""
    broke = []
    for name, MD in _mutants(D):
        try:
            res = evaluate(chk, MD)
        except Exception:
            broke.append(name)
            continue
        if res["max_rel_err"] is None or res["n_errors"] == len(chk.grid):
            broke.append(name + " (raised)")
            continue
        if res["max_rel_err"] > chk.tol:
            broke.append(name)
    return {"can_fail": bool(broke), "mutants_detected": broke}


def classify(chk: checks.Check, res: dict) -> str:
    if res["n_errors"] == len(chk.grid):
        return "ERROR"
    if res["max_rel_err"] is None:
        return "ERROR"
    if res["max_rel_err"] <= chk.tol:
        return "AGREE"
    return {
        "model": "MODEL",
        "scope": "SCOPE",
        "convention": "CONVENTION-DIFFERS",
        "internal": "INTERNAL-INCONSISTENT",
        "identity": "IDENTICAL-BODIES",
        "selftest": "REFERENCE-SELFTEST-DIFFERS",
    }.get(chk.kind, "FORMULA")


def _definitions_used(D) -> list[str]:
    """Which corpus definitions does the battery actually evaluate?"""
    import collections
    seen = set()

    class Recorder(dict):
        def __getitem__(self, k):
            seen.add(k)
            f = D[k]
            return lambda *a, **kw: f(*a, **kw)

    R = Recorder()
    for chk in checks.CHECKS:
        for p in chk.grid:
            for fn in (chk.lean, chk.ref):
                try:
                    _eval(fn, R, p)
                except Exception:
                    pass
    return sorted(seen)


def _call_points(D):
    """Every (definition, argument tuple) the battery actually evaluates."""
    import collections

    pts = collections.defaultdict(set)

    class Recorder(dict):
        def __getitem__(self, k):
            f = D[k]

            def w(*a, **kw):
                pts[k].add(tuple(a))
                return f(*a, **kw)

            return w

    R = Recorder()
    for chk in checks.CHECKS:
        for p in chk.grid:
            for fn in (chk.lean, chk.ref):
                try:
                    _eval(fn, R, p)
                except Exception:
                    pass
    return {k: sorted(v) for k, v in pts.items()}


def _cross_validate(D, used) -> dict:
    """Re-run the independent leanexpr translation over the same call points.

    Two separately written translators agreeing bit-for-bit is the only
    protection this battery has against a mistranslated definition producing a
    confident finding about nothing.
    """
    import crossvalidate as X

    pts = _call_points(D)
    agree, dis, unav = X.compare(used, pts)

    def row(n, fq, pt, a, b):
        return {"name": n, "fq": fq, "args": list(pt), "leanexpr": a, "extract": b}

    known = [row(*d) for d in dis if d[0] in corpus.QUARANTINE]
    unresolved = [row(*d) for d in dis if d[0] not in corpus.QUARANTINE]
    return {
        "method": "leanexpr.py vs extract/api.py over every evaluated argument tuple",
        "n_definitions_compared": len(agree),
        "n_arg_tuples": sum(len(v) for v in pts.values()),
        "n_agree_all_points": len(agree),
        "agree": {fq: n for _n, fq, n, _a, _c in agree},
        "quarantined_disagreements": known,
        "unresolved_disagreements": unresolved,
        "not_comparable": dict(unav),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default="results.json")
    args = ap.parse_args()

    D, prov, unavailable = corpus.load()
    used = _definitions_used(D)

    out = {
        "environment": {
            "python": sys.version.split()[0],
            "sampling": False,
            "note": "all references are closed form; no Monte Carlo error",
        },
        "corpus_stamp": corpus.api.stamp(),
        "extraction": {
            "primary_source": "proofs/validation/extract/api.py",
            "n_callables": len(D),
            "n_unavailable": len(unavailable),
            "unavailable": unavailable,
            "quarantined": corpus.QUARANTINE,
            "provenance": {prov[n]["fq"]: prov[n] for n in used if n in prov},
        },
        "cross_validation": _cross_validate(D, used),
        "contract_totality": contracts.totality_audit(
            corpus._leanexpr_table()[0], _call_points(D)
        ),
        "checks": {},
    }

    for chk in checks.CHECKS:
        res = evaluate(chk, D)
        vac = prove_can_fail(chk, D)
        verdict = classify(chk, res)
        bare = chk.fqn.split(".")[-1]
        out["checks"][chk.id] = {
            "definition": prov.get(bare, {}).get("fq", chk.fqn),
            "definition_source": prov.get(bare, {}).get("source"),
            "definition_checksum": prov.get(bare, {}).get("checksum"),
            "translator": prov.get(bare, {}).get("translator"),
            "claim": chk.claim,
            "model_definition": chk.model_lean,
            "model_reference": chk.model_ref,
            "reference": chk.reference,
            "tol": chk.tol,
            "verdict": verdict,
            "kind": chk.kind,
            "vacuous": not vac["can_fail"],
            "mutants_detected": vac["mutants_detected"],
            "canfail_clause": chk.canfail_clause,
            "note": chk.note,
            "max_rel_err": res["max_rel_err"],
            "min_rel_err": res["min_rel_err"],
            "worst_point": res["worst_point"],
            "worst_point_admissibility": (
                contracts.admissibility(
                    prov.get(bare, {}).get("fq", chk.fqn), res["worst_point"]["params"]
                )
                if res["worst_point"] and verdict != "AGREE"
                else None
            ),
            "n_grid": len(chk.grid),
            "rows": res["rows"],
        }

    with open(args.json, "w") as fh:
        json.dump(out, fh, indent=1, default=str)

    # ---- console summary --------------------------------------------------
    cv = out["cross_validation"]
    print(
        f"{len(D)} callables (primary: extract); "
        f"cross-validated {cv['n_definitions_compared']} defs over "
        f"{cv['n_arg_tuples']} arg tuples, "
        f"{len(cv['unresolved_disagreements'])} unresolved disagreements "
        f"({len(cv['quarantined_disagreements'])} quarantined)"
    )
    print(f"{'verdict':<22} {'vac':<4} {'max rel err':>12}  check")
    print("-" * 96)
    for cid, c in out["checks"].items():
        e = c["max_rel_err"]
        print(
            f"{c['verdict']:<22} {'VAC' if c['vacuous'] else '':<4} "
            f"{(f'{e:.3e}' if e is not None else 'n/a'):>12}  {cid}"
        )
    n_vac = sum(
        1 for c in out["checks"].values()
        if c["vacuous"] and c["kind"] not in ("identity", "selftest")
    )
    print(
        f"\n{len(out['checks'])} checks, {n_vac} vacuous "
        f"(identity and reference self-test checks are excluded) -> {args.json}"
    )
    tot = out["contract_totality"]
    print(
        f"totality audit: {tot['points_checked']} points, "
        f"{len(tot['totality_boundary_points'])} on a Mathlib boundary, "
        f"{len(tot['value_mismatches'])} value mismatches -> "
        f"{'CLEAN' if tot['clean'] else 'REVIEW'}"
    )
    n_unresolved = len(out["cross_validation"]["unresolved_disagreements"])
    if n_unresolved:
        print(
            f"FAIL: {n_unresolved} translation disagreements are unresolved. "
            "No verdict below is trustworthy until they are."
        )
    return 1 if (n_vac or n_unresolved) else 0


if __name__ == "__main__":
    raise SystemExit(main())

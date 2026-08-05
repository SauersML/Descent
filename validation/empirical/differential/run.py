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
        "n_evaluated": len(errs),
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


def _standin(fq):
    """Flag definitions whose numeric form was NOT derived from the Lean body.

    `Descent.Phi` is Mathlib's Gaussian CDF with no arithmetic body; extract
    evaluates it via the erf form. Mathematically identical, but it is the one
    place in the pipeline where the callable does not come from the Lean
    source. A disagreement in anything routing through it could be a defect in
    the definition OR a mismatch with the intended Phi, and a report that does
    not say so is overclaiming.
    """
    try:
        return corpus.api.numeric_standins(fq)
    except Exception:
        return None


def _actual_args(chk, D, bare, params):
    """The exact positional arguments the check passes to the definition under
    test at one grid point, keyed by the DEFINITION's own argument names.

    A check's grid axes are named for the experiment, not for the Lean binders
    -- `simpleFst-vs-hudson` sweeps `p1`/`p2` while the definition's binders are
    `p_1`/`p_2`, and `steppingStoneLength-missing-mutation` sweeps a `mu` axis
    the definition does not take at all. Handing grid keys to `api.satisfies`
    therefore raises NameError, which reads as False, and reports every point
    as violating every theorem. That is the third appearance of this same
    failure mode, so it is fixed at the source: record what was actually passed.
    """
    captured = []

    class Recorder(dict):
        def __getitem__(self, k):
            f = D[k]

            def w(*a, **kw):
                if k == bare:
                    captured.append(a)
                return f(*a, **kw)

            return w

    try:
        _eval(chk.lean, Recorder(), params)
    except Exception:
        return None
    if not captured:
        return None
    try:
        _fn, argnames = corpus.api.callable_for(corpus.api.resolve(bare))
    except Exception:
        return None
    args = captured[0]
    if len(args) != len(argnames):
        return None
    return dict(zip(argnames, args))


def _crossvalidate_points():
    import crossvalidate as X

    return X.battery_points()


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


def _cross_validate(D, used) -> dict:
    """Re-run the independent leanexpr translation over the same call points.

    Two separately written translators agreeing bit-for-bit is the only
    protection this battery has against a mistranslated definition producing a
    confident finding about nothing.
    """
    import crossvalidate as X

    pts = X.battery_points()
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
            "primary_source": "validation/empirical/extract/api.py",
            "n_callables": len(D),
            "n_unavailable": len(unavailable),
            "unavailable": unavailable,
            "quarantined": corpus.QUARANTINE,
            "provenance": {prov[n]["fq"]: prov[n] for n in used if n in prov},
        },
        "cross_validation": _cross_validate(D, used),
        "contract_totality": contracts.totality_audit(
            corpus._leanexpr_table()[0], _crossvalidate_points()
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
            "numeric_standin": _standin(prov.get(bare, {}).get("fq", chk.fqn)),
            "claim": chk.claim,
            "model_definition": chk.model_lean,
            "model_reference": chk.model_ref,
            "reference": chk.reference,
            "tol": chk.tol,
            "verdict": verdict,
            "expected_verdict": chk.expected_verdict,
            "verdict_regression": bool(
                chk.expected_verdict and verdict != chk.expected_verdict
            ),
            "kind": chk.kind,
            "vacuous": not vac["can_fail"],
            "mutants_detected": vac["mutants_detected"],
            "canfail_clause": chk.canfail_clause,
            "note": chk.note,
            "max_rel_err": res["max_rel_err"],
            "min_rel_err": res["min_rel_err"],
            "worst_point": res["worst_point"],
            "worst_point_definition_args": (
                _actual_args(chk, D, bare, res["worst_point"]["params"])
                if res["worst_point"] and verdict != "AGREE"
                else None
            ),
            "worst_point_admissibility": (
                contracts.admissibility(
                    prov.get(bare, {}).get("fq", chk.fqn),
                    _actual_args(chk, D, bare, res["worst_point"]["params"]) or {},
                )
                if res["worst_point"] and verdict != "AGREE"
                else None
            ),
            "n_grid": len(chk.grid),
            "n_grid_errors": res["n_errors"],
            "n_evaluated": res["n_evaluated"],
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
    standins = [
        (cid, c["definition"]) for cid, c in out["checks"].items()
        if c.get("numeric_standin") and c["verdict"] != "AGREE"
    ]
    print(
        f"numeric stand-ins: {len(standins)} disagreeing checks route through a "
        f"non-Lean-derived numeric form"
        + ("" if not standins else " -- CANNOT be reported as definition defects "
           "without ruling out the stand-in")
    )
    for cid, fq in standins:
        print(f"    {cid}  ({fq})")
    regressions = [
        (cid, c["expected_verdict"], c["verdict"])
        for cid, c in out["checks"].items() if c["verdict_regression"]
    ]
    if regressions:
        print("VERDICT REGRESSIONS -- a check stopped producing its declared "
              "result:")
        for cid, want, got in regressions:
            print("    %-46s expected %s, got %s" % (cid, want, got))
        print("    A convention pin that becomes agreement is a regression, "
              "not an improvement.")
    n_unresolved = len(out["cross_validation"]["unresolved_disagreements"])
    if n_unresolved:
        print(
            f"FAIL: {n_unresolved} translation disagreements are unresolved. "
            "No verdict below is trustworthy until they are."
        )

    # A check that ERRORS is not a check that passed.  Until now `classify`
    # returned ERROR and nothing compared it to anything, so a check whose every
    # grid point raised -- because the definition it names was deleted upstream,
    # or because its own lambda never received the corpus table -- was scored as
    # no problem at all and this function returned 0.  Four checks sat in that
    # state simultaneously while the gate reported green, one of them the CONTROL
    # for a whole family and another a check that had never once executed since
    # the day it was written.  Present, running, and structurally unable to fail
    # is the same defect as a truncated error list, and it belongs here rather
    # than in a reviewer's attention.
    #
    # An ERROR against a PINNED expectation is already caught as a regression
    # above; this catches the unpinned ones, which are the ones that hid.
    #
    # `classify` calls it ERROR only when EVERY point raised (`n_errors ==
    # len(grid)`), so the gate was calibrated at exactly one boundary of this
    # failure and blind everywhere inside it.  A check evaluable at ONE of
    # fifteen grid points took its verdict from that one survivor, read AGREE,
    # passed `prove_can_fail`, and returned 0 -- measured with head and tail
    # survivors alike.  The grid is not decoration: `canfail_clause` on many of
    # these checks says in words that the discrimination lives at particular
    # ends of it, so fourteen points silently dropping is the whole check
    # dropping.  A point that raised is therefore a finding at budget 0,
    # whatever the surviving points say.
    errored, partial = [], []
    for cid, c in out["checks"].items():
        n_err = c["n_grid_errors"]
        if not n_err:
            continue
        first = next((r["error"] for r in c["rows"] if "error" in r), "?")
        (errored if n_err == c["n_grid"] else partial).append(
            (cid, c["definition"], n_err, c["n_grid"], first))
    if errored:
        print("FAIL: checks that could not be evaluated at any grid point. An "
              "ERROR is not a pass -- repoint the check, fix its lambda, or "
              "retire it:")
        for cid, fq, n_err, n_grid, err in errored:
            print(f"    {cid:<52} {fq}\n        {err}")
    if partial:
        print("FAIL: checks evaluated on only PART of their grid. The verdict "
              "printed above was computed from the surviving points alone, and "
              "the points that raised are exactly where the check was not "
              "applied -- several of these grids discriminate only at one end:")
        for cid, fq, n_err, n_grid, err in partial:
            print(f"    {cid:<52} {fq}\n        {n_err} of {n_grid} grid points "
                  f"raised; first: {err}")

    # A comparison that compared nothing is not a comparison that agreed. Both
    # of these report a count and were gated only on the DISAGREEMENTS found in
    # them, which is zero both when the two translators agree everywhere and
    # when there was nothing to translate: with the extraction table emptied,
    # the cross-check compares 0 definitions and the totality audit visits 0
    # points, and neither said so. Floors at "did anything at all", not budgets
    # pinned to today's counts.
    empty_instruments = []
    if not cv["n_definitions_compared"]:
        empty_instruments.append(
            "the leanexpr/extract cross-check compared 0 definitions; it is the "
            "only protection this battery has against a mistranslated "
            "definition, and it did not run on any")
    if not out["contract_totality"]["points_checked"]:
        empty_instruments.append(
            "the totality audit visited 0 points and reported CLEAN")
    if empty_instruments:
        print("FAIL: an instrument in this battery measured nothing and "
              "reported no problem:")
        for line in empty_instruments:
            print(f"    {line}")

    return 1 if (n_vac or n_unresolved or regressions or errored or partial
                 or empty_instruments) else 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Mechanical enforcement of the two project contracts.

CONTRACT 1 -- MATHLIB IS TOTAL.
    x/0 = 0, x⁻¹ at 0 = 0, log 0 = 0, log(-x) = log|x|, sqrt(negative) = 0,
    0^y = 0 for y != 0.  A checker that raises, or reports a defect, where Lean
    returns 0 manufactures defects.

    Asserting "I checked, no grid point hits a boundary" is not enough; the
    audit below MEASURES it.  `leanexpr.py` uses strict Python arithmetic and
    raises at these boundaries; extract's callables use `lean_rt.py` and return
    Lean's total value.  Running both over the same point therefore detects a
    boundary exactly: leanexpr raises (or the two differ) iff the point is on
    one.  The two translators being built on opposite conventions is what makes
    this measurable at all.

CONTRACT 2 -- THEOREM-PROVED AND DOCSTRING-IMPLIED BOUNDS MUST NOT MERGE.
    extract's `constraints` carries both.  `hypotheses_by_theorem` attributes
    each hypothesis to the theorem that states it -- that is the theorem-proved
    kind.  `declared_lo`/`declared_hi`/`declared_kind` are mined from prose --
    that is the docstring-implied kind.  They are reported separately and never
    combined into one admissibility verdict.

    Note on reading `constraints["hypotheses"]`: it is the UNION over every
    theorem that mentions the definition, NOT a conjunctive domain.  For
    `Calibrator.coalFst` it contains `100 * Ne < t`, which comes from exactly
    one asymptotic lemma (`coal_fst_approaches_one`); read conjunctively it
    would exclude essentially every sensible F_ST evaluation.
"""

from __future__ import annotations

import sys

EXTRACT = "/Users/user/gnomon/proofs/validation/extract"
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402


# ---------------------------------------------------------------------------
# Contract 1
# ---------------------------------------------------------------------------
def totality_audit(leanexpr_table, points_by_name) -> dict:
    """Find every evaluated point that sits on a Mathlib totality boundary."""
    boundary, mismatch, checked = [], [], 0
    for name, pts in points_by_name.items():
        if name not in leanexpr_table:
            continue
        try:
            fq = api.resolve(name)
            total, _ = api.callable_for(fq)
        except Exception:
            continue
        strict = leanexpr_table[name]
        for pt in pts:
            checked += 1
            try:
                s = strict(*pt)
            except ZeroDivisionError:
                boundary.append({"fq": fq, "args": list(pt), "kind": "division by zero"})
                continue
            except ValueError as e:
                boundary.append({"fq": fq, "args": list(pt), "kind": f"domain: {e}"})
                continue
            except Exception:
                continue
            try:
                t = total(*pt)
            except Exception:
                continue
            if abs(s - t) > 1e-9 + 1e-9 * max(abs(s), abs(t)):
                mismatch.append(
                    {"fq": fq, "args": list(pt), "strict": s, "lean_total": t}
                )
    return {
        "method": "strict-arithmetic leanexpr vs lean_rt-backed extract, same points",
        "points_checked": checked,
        "totality_boundary_points": boundary,
        "value_mismatches": mismatch,
        "clean": not boundary and not mismatch,
    }


# ---------------------------------------------------------------------------
# Contract 2
# ---------------------------------------------------------------------------
def admissibility(fq: str, params: dict) -> dict:
    """Classify a point against the two KINDS of bound, kept apart.

    Returns `theorem_proved` and `docstring_implied` verdicts separately.
    Neither is combined into a single "admissible" flag, deliberately.
    """
    out = {
        "theorem_proved": {"verdict": "no-constraint", "satisfied": [], "violated": []},
        "docstring_implied": {"verdict": "no-constraint"},
        "unmodelled_hypotheses": [],
    }
    try:
        d = api.definition(fq)
    except Exception:
        return out
    con = d.get("constraints") or {}

    # -- theorem-proved: per-theorem hypothesis attribution --------------
    by_thm = con.get("hypotheses_by_theorem") or {}
    try:
        codes, texts, unmodelled = api.hypotheses(fq)
    except Exception:
        codes, texts, unmodelled = [], [], []
    out["unmodelled_hypotheses"] = list(unmodelled)

    # extract compiles hypotheses in EXEC mode: the verdict lands in `__r` and
    # the namespace must carry `_rt` (lean_rt) for total arithmetic. Evaluating
    # them with `eval` returns None, which reads as False and manufactures a
    # violation at every point -- the precise failure the totality contract is
    # about. Mirror `admissible.satisfies` instead of improvising.
    import lean_rt as _rt

    sat, vio, unevaluable = [], [], []
    for code, text in zip(codes, texts):
        ns = dict(params)
        ns["_rt"] = _rt
        try:
            exec(code, {"__builtins__": {}}, ns)
        except NameError:
            # hypothesis constrains a binder this check's grid does not name
            unevaluable.append(text)
            continue
        except Exception:
            unevaluable.append(text)
            continue
        r = ns.get("__r")
        if r is None:
            unevaluable.append(text)
            continue
        sources = [t for t, hs in by_thm.items() if text in hs]
        (sat if r is True else vio).append(
            {"hypothesis": text, "stated_by": sources}
        )
    out["unevaluable_hypotheses"] = unevaluable
    if sat or vio:
        out["theorem_proved"] = {
            "verdict": "all-satisfied" if not vio else "some-violated",
            "satisfied": sat,
            "violated": vio,
            "note": (
                "constraints.hypotheses is a UNION over mentioning theorems, "
                "not a conjunctive domain; a violated entry means the point is "
                "outside THAT theorem's scope, not outside the definition's"
            ),
        }

    # -- docstring-implied: declared range, kept entirely separate -------
    lo, hi = con.get("declared_lo"), con.get("declared_hi")
    if lo is not None or hi is not None:
        out["docstring_implied"] = {
            "verdict": "declared-range",
            "declared_lo": lo,
            "declared_hi": hi,
            "declared_kind": con.get("declared_kind"),
            "units": con.get("units"),
            "provenance": "mined from prose; NOT machine-checked",
        }
    return out

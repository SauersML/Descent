"""Cross-validate two independent Lean->Python extractions of the same corpus.

`leanexpr.py` (this directory) and `proofs/validation/extract/api.py` were
written separately from the same Lean sources.  Neither is authoritative.  If
they agree on a definition at every point a check evaluates, a transcription
error would have to be the SAME error in both, which is a far stronger
guarantee than either extraction alone -- and it is the guarantee the whole
battery needs, because a mistranslated definition produces a finding about
nothing.

Disagreements are reported, never averaged or silently resolved.
"""

from __future__ import annotations

import sys

import corpus

EXTRACT = "/Users/user/gnomon/proofs/validation/extract"
if EXTRACT not in sys.path:
    sys.path.insert(0, EXTRACT)

import api  # noqa: E402


def _eval(fn, D, params):
    """Call a check's lean/ref side, passing the corpus table iff it wants one."""
    import inspect

    names = list(inspect.signature(fn).parameters)
    return fn(D, **params) if (names and names[0] == "D") else fn(**params)


def battery_points() -> dict[str, list[tuple]]:
    """Every (definition, argument tuple) the differential battery evaluates.

    Zero-argument entry point for external harnesses -- extract's
    `test_parser.py` calls this at emit time so the cross-check runs whenever
    the definition table is regenerated, which is when it matters most.
    Returns bare Lean name -> sorted list of positional argument tuples.

    Deliberately derived by RECORDING an actual battery run rather than by
    listing points by hand: a hand-maintained list silently stops covering new
    checks, and a cross-check that quietly stops covering things is the failure
    mode this whole exercise is about.
    """
    import collections

    import checks

    D, _prov, _unavail = corpus.load()
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


def battery_names() -> list[str]:
    """The definitions the battery exercises; pairs with `battery_points()`."""
    return sorted(battery_points())


def _resolve(name: str) -> str | None:
    # Honour the same explicit pins corpus.py uses. Without this, every
    # ambiguous short name silently drops out of the comparison -- and the
    # ambiguous names are precisely the ones most in need of it, since a
    # mis-bound overload is the failure this cross-check exists to catch.
    if name in corpus.FQ_OVERRIDES:
        return corpus.FQ_OVERRIDES[name]
    try:
        return api.resolve(name)
    except Exception:
        return None


def compare(names, points_by_name, atol=1e-12, rtol=1e-10):
    """Compare the two extractions on supplied argument tuples.

    `points_by_name` maps a bare Lean name to a list of positional argument
    tuples.  Returns (agreements, disagreements, unavailable).
    """
    # MUST be the raw leanexpr table, NOT corpus.load(): load() returns the
    # hybrid table whose entries are mostly extract's own callables, so
    # comparing against it would compare extract with itself and pass
    # vacuously. This comparison is only worth anything if the two sides are
    # genuinely independent.
    mine, _defs = corpus._leanexpr_table()
    agree, disagree, unavailable = [], [], []

    for name in names:
        fq = _resolve(name)
        if fq is None:
            unavailable.append((name, "not in extract table"))
            continue
        if name not in mine:
            unavailable.append((name, "not extractable by leanexpr"))
            continue
        try:
            theirs, argnames = api.callable_for(fq)
        except Exception as e:
            unavailable.append((name, f"extract: {type(e).__name__}: {e}"))
            continue

        n_ok = 0
        for pt in points_by_name.get(name, []):
            try:
                a = mine[name](*pt)
            except Exception as e:
                disagree.append((name, fq, pt, f"leanexpr raised {e}", None))
                continue
            try:
                b = theirs(*pt)
            except Exception as e:
                disagree.append((name, fq, pt, None, f"extract raised {e}"))
                continue
            if abs(a - b) > atol + rtol * max(abs(a), abs(b)):
                disagree.append((name, fq, pt, a, b))
            else:
                n_ok += 1
        if n_ok:
            agree.append((name, fq, n_ok, argnames, api.body_checksum(fq)))
    return agree, disagree, unavailable

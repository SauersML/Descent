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


def _resolve(name: str) -> str | None:
    try:
        return api.resolve(name)
    except Exception:
        return None


def compare(names, points_by_name, atol=1e-12, rtol=1e-10):
    """Compare the two extractions on supplied argument tuples.

    `points_by_name` maps a bare Lean name to a list of positional argument
    tuples.  Returns (agreements, disagreements, unavailable).
    """
    mine, _defs, _fail = corpus.load()
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

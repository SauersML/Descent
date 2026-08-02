"""Repo-relative paths, derived from this file's own location.

Every path in this directory used to be an absolute /Users/... string, which
meant the whole pipeline silently produced empty results the first time it ran
anywhere else: `leanparse.py` reported "parsed 0 defs, 0 theorems" and exited 0
rather than failing.  Deriving them from __file__ removes a class of error that
does not announce itself.
"""

from __future__ import annotations

from pathlib import Path

HERE = Path(__file__).resolve().parent          # .../proofs/validation/symbolic
VALIDATION = HERE.parent                        # .../proofs/validation
PROOFS = VALIDATION.parent                      # .../proofs
REPO = PROOFS.parent                            # repo root
CALIBRATOR = PROOFS / "Calibrator"
EXTRACT = VALIDATION / "extract"


def require(p: Path, what: str) -> Path:
    """Fail loudly rather than yielding an empty result from a missing tree."""
    if not p.exists():
        raise SystemExit(f"FATAL: {what} not found at {p}. "
                         f"Paths are derived from {HERE}; is the layout intact?")
    return p

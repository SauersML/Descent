"""Repo-relative paths, derived from this file's own location.

Every path in this directory used to be an absolute /Users/... string, which
meant the whole pipeline silently produced empty results the first time it ran
anywhere else: `leanparse.py` reported "parsed 0 defs, 0 theorems" and exited 0
rather than failing.  Deriving them from __file__ removes a class of error that
does not announce itself.
"""

from __future__ import annotations

from pathlib import Path

HERE = Path(__file__).resolve().parent    # .../proofs/validation/empirical/symbolic
EMPIRICAL = HERE.parent                   # .../proofs/validation/empirical
VALIDATION = EMPIRICAL.parent             # .../proofs/validation
PROOFS = VALIDATION.parent                # .../proofs
REPO = PROOFS.parent                            # repo root
CALIBRATOR = PROOFS / "Calibrator"
EXTRACT = EMPIRICAL / "extract"

# ---------------------------------------------------------------- artifacts
#
# Generated result JSONs are BUILD PRODUCTS: derived, regenerable in about
# fifteen minutes, and large.  They are not in git.  Committing them created a
# standing problem -- the cluster checkout cannot push, so the in-repo copies
# went stale every run, and a stale artifact that still parses is
# indistinguishable from a current one.
#
# They are written to shared cluster storage instead, which every tier can
# reach now that every tier runs on the cluster.  Resolution order:
#   1. $GNOMON_ARTIFACTS          explicit override
#   2. the shared cluster path, if it exists
#   3. this directory             so a local run still works and is obvious
#
# For a frozen snapshot, copy one deliberately with the revision in the
# filename.  Do not commit these.
SHARED_ARTIFACTS = Path("/projects/standard/hsiehph/sauer354/gnomon-artifacts/symbolic")


def _resolve_artifacts() -> Path:
    import os
    override = os.environ.get("GNOMON_ARTIFACTS")
    if override:
        p = Path(override)
        p.mkdir(parents=True, exist_ok=True)
        return p
    # Predicate is the shared PROJECT root, not the artifacts directory itself,
    # which will not exist before the first run.  Testing the directory would
    # make the fallback permanent and silently keep writing beside the source.
    if SHARED_ARTIFACTS.parents[1].exists():
        SHARED_ARTIFACTS.mkdir(parents=True, exist_ok=True)
        return SHARED_ARTIFACTS
    return HERE


ARTIFACTS = _resolve_artifacts()


def require(p: Path, what: str) -> Path:
    """Fail loudly rather than yielding an empty result from a missing tree."""
    if not p.exists():
        raise SystemExit(f"FATAL: {what} not found at {p}. "
                         f"Paths are derived from {HERE}; is the layout intact?")
    return p

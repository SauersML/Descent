"""One master seed for every tier, so draw-dependence can be tested.

REPRODUCIBILITY IS NOT STABILITY.  A checker that always draws the same points
gives the same answer every run, which says nothing about whether the answer
survives drawing DIFFERENT points.  Determinism answers the easy question.

Every tier here samples: the range search draws start points, the invariant
checks draw sample points, the theorem checks draw points satisfying
hypotheses, and the simulation tier draws both point-sets and oracle replicates.
None of those seeds was variable until now, so none of those verdicts had ever
been tested under a different draw.

    GNOMON_SEED=977 python3 check_ranges.py

Sub-seeds are derived by crc32 of a label, NOT by `hash()`: Python salts string
hashing per process, so a seed derived from `hash(name)` silently differs
between runs.  That bug made this tier's simulation verdicts irreproducible and
was invisible until a re-run for an unrelated reason flipped a verdict.
"""
from __future__ import annotations

import os
import zlib

MASTER = int(os.environ.get("GNOMON_SEED", "0"))


def sub(label: str, i: int = 0) -> int:
    """A stable sub-seed for `label`, varying with the master seed."""
    return (zlib.crc32(f"{label}:{i}".encode()) + MASTER * 2654435761) % (2 ** 31)

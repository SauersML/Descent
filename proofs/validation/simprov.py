"""Provenance and error bars for the Python simulation sweeps.

WHY THIS EXISTS.  Every results file under `proofs/validation/` that a Python
sweep wrote was a bare JSON list of numbers.  It could not say which revision it
described, when it ran, how many replicates stood behind each number, or what
seed produced it.  That is exactly the failure `Shared/Results.lean` was written
to stop on the Lean side, and it is the reason several circulating numbers could
not be re-checked: `port.json` holds eighteen records with no error bar and no
revision, and three replicates in a cell whose scatter is comparable to the
effect is an anecdote wearing a decimal point.

So this module supplies two things, and the sweeps are expected to use both.

  1.  `stamp()` -- the same fields `Shared.Results.write` writes, with the same
      names where they mean the same thing: `revision`, `workingTreeClean`,
      `workingTreeDirtyPaths`, `runAt`.  A reader who can compare a Lean
      detector's output against a Python sweep's without a translation table is
      a reader who will actually do it.  The sweeps add `seed`, `replicates`
      and their own config block, because a simulation has an uncertainty that
      a static corpus scan does not.

  2.  `summarize()` -- mean, standard deviation and STANDARD ERROR over the
      replicates of a cell.  A record without an error bar cannot falsify
      anything: it cannot distinguish "the law is wrong" from "we drew three
      samples".

A results file also carries EVERY REPLICATE, not only the cell aggregates.  The
aggregate is what hides the scatter, and the scatter is the measurement that
told us the portability cells were noisy in the first place.

Never throws on a missing `git`: a degraded provenance stamp is a nuisance, but
losing an expensive cluster measurement to a subprocess error is a disaster.

KEPT TO PYTHON 3.6.  `fam_permeability.py` says in its own header that it is
written for 3.6.8 with numpy only, because that is what the cluster's `python3`
is, and this module is imported by it.  So: no `from __future__ import
annotations`, no `capture_output=`, no walrus.  The popgen sweeps run under a
newer interpreter and would not have cared; the one that would have broken is
the one whose results file does not exist yet.
"""

import json
import math
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]

# The sweeps write their own JSON, so a sweep that runs after another one would
# otherwise see the first one's output and report a dirty tree that has nothing
# to do with the code under test.  Same exclusion, same reason, as
# `Shared.Results.gitDirtyPaths`.
_EXCLUDE = ":(exclude)proofs/validation/**/*.json"


def _git(*args, default=""):
    try:
        r = subprocess.run(["git", "-C", str(REPO)] + list(args),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=30)
        if r.returncode != 0:
            return default
        return r.stdout.decode("utf-8", "replace").strip()
    except Exception:
        return default


def _version(mod):
    try:
        return __import__(mod).__version__
    except Exception:
        return None


def stamp(generator: str, config: dict, seed, replicates) -> dict:
    """The provenance header.

    `config` is the full resolved parameter grid, not a summary of it: a sweep
    that records "split times: 8 values" cannot be re-run from its own output.
    """
    porcelain = _git("status", "--porcelain", "--", _EXCLUDE, default=None)
    dirty = (None if porcelain is None
             else [ln.strip() for ln in porcelain.split("\n") if ln.strip()])
    return {
        "generator": generator,
        "revision": _git("rev-parse", "HEAD", default="unknown"),
        "revisionShort": _git("rev-parse", "--short", "HEAD", default="unknown"),
        "workingTreeClean": None if dirty is None else (dirty == []),
        "workingTreeDirtyPaths": dirty,
        "runAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "host": platform.node(),
        "python": sys.version.split()[0],
        "numpy": _version("numpy"),
        "msprime": _version("msprime"),
        "seed": seed,
        "replicates": replicates,
        "argv": sys.argv,
        "config": config,
    }


def summarize(values) -> dict:
    """Mean, sd and standard error of the mean over replicates.

    NaNs are dropped and COUNTED, not silently averaged around: a cell where
    half the replicates failed is a different measurement from a cell where
    none did, and a bare mean cannot tell them apart.
    """
    vals = list(values)
    xs = [float(v) for v in vals
          if v is not None and not (isinstance(float(v), float)
                                    and math.isnan(float(v)))]
    n_all = len(vals)
    n = len(xs)
    if n == 0:
        return {"n": 0, "n_dropped": n_all, "mean": None, "sd": None, "se": None,
                "min": None, "max": None}
    mean = sum(xs) / n
    if n > 1:
        var = sum((x - mean) ** 2 for x in xs) / (n - 1)
        sd = math.sqrt(var)
        se = sd / math.sqrt(n)
    else:
        sd = se = None
    return {"n": n, "n_dropped": n_all - n, "mean": mean, "sd": sd, "se": se,
            "min": min(xs), "max": max(xs)}


def write(path, generator: str, config: dict, seed, replicates,
          cells, records) -> Path:
    """Write a sweep result: provenance, per-cell aggregates, per-replicate rows.

    Both lists are required.  `cells` without `records` is the aggregate-only
    format this module exists to retire; `records` without `cells` makes every
    reader re-derive the error bars and get them subtly different.
    """
    obj = {
        "_provenance": stamp(generator, config, seed, replicates),
        "cells": list(cells),
        "records": list(records),
    }
    p = Path(path)
    if str(p.parent) not in ("", "."):
        os.makedirs(p.parent, exist_ok=True)
    p.write_text(json.dumps(obj, indent=1, ensure_ascii=False) + "\n")
    return p


def log_grid(lo, hi, n):
    """`n` log-spaced values from `lo` to `hi` inclusive, as plain floats.

    Used by every sweep whose axis spans orders of magnitude.  Kept here so the
    grids in different scripts are spaced the same way and a reader comparing
    two sweeps is comparing like with like.
    """
    if n < 2:
        return [float(lo)]
    r = (float(hi) / float(lo)) ** (1.0 / (n - 1))
    out = [float(lo) * r ** i for i in range(n)]
    # Snap the endpoints: float(lo) * r ** (n-1) lands a few ulps off `hi`, and
    # a grid whose top cell reads 0.49999999999999967 makes every table that
    # quotes it look like it came from somewhere else.
    out[0], out[-1] = float(lo), float(hi)
    return out


def int_log_grid(lo, hi, n):
    """`log_grid` rounded to distinct increasing integers."""
    seen, out = set(), []
    for v in log_grid(lo, hi, n):
        i = int(round(v))
        if i not in seen:
            seen.add(i)
            out.append(i)
    return out


def add_sweep_args(parser, default_reps, default_out, default_seed):
    """The three flags every sweep must have: replicates, seed, output.

    Rule 3 of the sweep contract: the current values stay the defaults so a
    laptop run still works, and a large run is one flag away.
    """
    parser.add_argument("--reps", type=int, default=default_reps,
                        help="replicates per cell (default %d)" % default_reps)
    parser.add_argument("--seed", type=int, default=default_seed,
                        help="master seed (default %d)" % default_seed)
    parser.add_argument("--output", default=default_out,
                        help="results JSON (default %s)" % default_out)
    parser.add_argument("--jobs", type=int,
                        default=int(os.environ.get("NPROC", "8")),
                        help="worker processes; the cluster node is SHARED, so "
                             "this defaults to 8 rather than to the core count")
    return parser


def parse_floats(s):
    """Comma-separated float list, for grid flags."""
    return [float(x) for x in str(s).replace(",", " ").split()]


def parse_ints(s):
    return [int(float(x)) for x in str(s).replace(",", " ").split()]

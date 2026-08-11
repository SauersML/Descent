#!/usr/bin/env python3
"""The cross-deme LD-retention surface, evaluated exactly rather than fitted.

WHAT THIS IS.  `moments.LD` (Ragsdale & Gravel) integrates the two-locus moment
system of a demography exactly, so it returns the cross-deme second moments
`E[D_1 D_2]` at a given scaled recombination distance without simulating
anything and without fitting a rate.  The quantity the corpus needs is the
CORRELATION of D across the two demes,

    Corr(D)(rho) = E[D_1 D_2] / sqrt(E[D_1 D_1] * E[D_2 D_2]),

which is the fraction of the source population's between-locus LD that survives
in the target -- the surface `CrossPopulationGenerationalModel.ldRetentionAt`
supplies, in the rate variable `rho = 4*Ne*c`.

WHY IT IS COMMITTED RATHER THAN QUOTED.  A witness in the corpus reads two of
these numbers, and a number in a docstring cannot be re-derived.  Running this
file reproduces them, together with the demography they belong to.

WHAT IT IS NOT.  This is not a battery: nothing here has an oracle, a competitor
or a verdict, because there is no corpus body of this surface to agree or
disagree with -- that closed form is what the corpus owes.  It is a prediction,
recorded so a derivation has something exact to be checked against.

F_ST IS MEASURED FROM THE SAME OBJECT, not read off the migration rate.  The
heterozygosity statistics come out of the same integration, so the F_ST reported
beside each curve is Hudson's `1 - H_within / H_between` on that run's own
numbers.  A nominal `4*N*m` would carry a convention this file would then have
to defend; a ratio of two heterozygosities carries none.

    $HOME/simcov-venv/bin/python ld_surface.py
"""

from __future__ import annotations

import json
import pathlib

import moments

# `rho = 4*Ne*c` is the rate variable, and the one thing task #22's re-reading
# did NOT refute: at matched migration the curve in these units is free of Ne.
RHOS = [0.0, 1.0, 2.0, 5.0, 10.0, 20.0]

# Two migration levels at one size, so the surface is read at two divergence
# levels.  The split is deep enough (T = 10, in units of 2N generations) that
# the two demes are at migration-drift equilibrium.
CELLS = [("low-divergence", 5.0), ("high-divergence", 1.0)]

T_SPLIT = 10.0
THETA = 0.001


def surface(m_scaled: float) -> dict:
    """Corr(D) over the rho grid, and Hudson F_ST, for one migration level."""
    y = moments.LD.Demographics2D.split_mig(
        (1.0, 1.0, T_SPLIT, m_scaled), rho=RHOS, theta=THETA)
    names = y.names()
    ld_names, h_names = names[0], names[1]
    i_dd00 = ld_names.index("DD_0_0")
    i_dd01 = ld_names.index("DD_0_1")
    i_dd11 = ld_names.index("DD_1_1")
    corr = []
    for k in range(len(RHOS)):
        row = y[k]
        corr.append(row[i_dd01] / (row[i_dd00] * row[i_dd11]) ** 0.5)
    h = y[-1]
    h_within = 0.5 * (h[h_names.index("H_0_0")] + h[h_names.index("H_1_1")])
    h_between = h[h_names.index("H_0_1")]
    return {"m_scaled": m_scaled,
            "fst_hudson": 1.0 - h_within / h_between,
            "rho": RHOS,
            "corr_D": corr}


def main() -> None:
    out = {"engine": "moments.LD (Ragsdale & Gravel two-locus moment system)",
           "version": moments.__version__,
           "demography": "two-deme split with continuous symmetric migration, "
                         f"equal sizes, T = {T_SPLIT} (units of 2N), "
                         f"theta = {THETA}",
           "cells": {name: surface(m) for name, m in CELLS}}
    for name, cell in out["cells"].items():
        print(f"{name}: F_ST(Hudson) = {cell['fst_hudson']:.4f}")
        for rho, c in zip(cell["rho"], cell["corr_D"]):
            print(f"    rho = {rho:5.1f}   Corr(D) = {c:.5f}")
    here = pathlib.Path(__file__).resolve().parent
    (here / "ld_surface.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()

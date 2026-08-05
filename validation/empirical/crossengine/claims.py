"""Corpus bodies under cross-engine test, each with competitors on the SAME cells.

The identity gate is the competitor test, and it is free.  A body that agrees
with a simulation proves nothing unless a DIFFERENT body, evaluated on the same
cells, is rejected.  Every claim here therefore carries competitors, and one of
them -- named `PLANTED` -- is known to be wrong by construction.  If the
harness ever fails to reject `PLANTED`, the harness is broken and its MATCHes
are worthless; `run.py` treats that as a hard failure, not a warning.

Claims are keyed to the Lean definition they test.  Do NOT anchor anything here
to a line number: definitions move every few minutes.  `def_name` is the anchor.
"""

from __future__ import annotations

import math


# ------------------------------------------------------- mutation-selection
def msb_corpus(mu, s, h):
    """Descent.mutationSelectionBalance -- mu / (h*s + mu)."""
    return mu / (h * s + mu)


def msb_classical(mu, s, h):
    """Textbook Haldane form without the corpus's `+ mu` guard."""
    return mu / (h * s)


def msb_double(mu, s, h):
    """Per-diploid rather than per-gamete mutation rate: a factor-of-two error
    of exactly the kind this project has shipped before."""
    return 2 * mu / (h * s)


def msb_half(mu, s, h):
    return mu / (2 * h * s)


def msb_exact(mu, s, h):
    """Fixed point of EXACT viability selection followed by mutation.

    Genotype fitnesses 1, 1 - h*s, 1 - s renormalised by mean fitness, then
    forward mutation on the wild-type copies.  This is what the corpus's
    `mutationSelectionStepRare` linearises: that map drops the mean-fitness
    denominator and the p-squared term, which its own docstring records as
    "valid at small s and small p".  Carried here so that a cell rejecting both
    `corpus` and `classical` identifies the linearisation positively instead of
    leaving an unexplained gap.
    """
    p = 0.5
    for _ in range(200000):
        wbar = (1 - p) ** 2 + 2 * p * (1 - p) * (1 - h * s) + p * p * (1 - s)
        ps = p * ((1 - h * s) * (1 - p) + (1 - s) * p) / wbar
        nxt = ps + mu * (1 - ps)
        if abs(nxt - p) < 1e-15:
            return nxt
        p = nxt
    return p


def msb_planted(mu, s, h):
    """KNOWN WRONG by construction: the corpus body inflated 40 percent."""
    return 1.4 * mu / (h * s + mu)


def msbr_corpus(mu, s):
    """Descent.mutationSelectionBalanceRecessive."""
    return (math.sqrt(mu * (mu + 4 * s)) - mu) / (2 * s)


def msbr_linear(mu, s):
    """Dominant scaling applied to a recessive allele: mu/s rather than
    sqrt(mu/s).  Discriminated by the log-log slope in mu, 1 against 1/2, which
    is convention-free."""
    return mu / s


def msbr_half(mu, s):
    return math.sqrt(mu / (2 * s))


def msbr_planted(mu, s):
    """KNOWN WRONG by construction: the corpus body inflated 40 percent."""
    return 1.4 * msbr_corpus(mu, s)


CLAIMS = {
    # ------------------------------------------------------------------
    "mutationSelectionBalance": {
        "lean_file": "Descent/Portability/RareVariantPortability.lean",
        "def_name": "mutationSelectionBalance",
        "observable": "carrier_frequency",
        "args": ("MU", "S", "H"),
        "needs": {"selection": True, "finite_population": True},
        "bodies": {
            "corpus": msb_corpus,
            "classical": msb_classical,
            "exact": msb_exact,
            "double": msb_double,
            "half": msb_half,
            "PLANTED": msb_planted,
        },
        # 4*N*h*s is the drift parameter the corpus body does not contain.
        # Ne is scaled DOWN and the compound parameter swept, so the whole
        # sweep runs in seconds rather than hours.
        "cells": [
            {"name": "4Nhs=200", "N": 2000, "MU": 1e-4, "S": 0.05, "H": 0.5,
             "T0": 3000, "T1": 40000},
            {"name": "4Nhs=50", "N": 500, "MU": 1e-4, "S": 0.05, "H": 0.5,
             "T0": 3000, "T1": 80000},
            {"name": "4Nhs=10", "N": 100, "MU": 1e-4, "S": 0.05, "H": 0.5,
             "T0": 3000, "T1": 150000},
            {"name": "4Nhs=2.5", "N": 25, "MU": 1e-4, "S": 0.05, "H": 0.5,
             "T0": 3000, "T1": 150000},
            {"name": "4Nhs=1", "N": 10, "MU": 1e-4, "S": 0.05, "H": 0.5,
             "T0": 3000, "T1": 150000},
        ],
    },
    # The `+ mu` in the corpus denominator is invisible when mu << h*s, which
    # is where the cells above sit.  These cells exist only to give it power:
    # corpus and classical are 10, 33 and 50 percent apart across them, and
    # 4*N*h*s stays large so drift is not the thing being measured.
    "mutationSelectionBalance_guard": {
        "lean_file": "Descent/Portability/RareVariantPortability.lean",
        "def_name": "mutationSelectionBalance",
        "observable": "carrier_frequency",
        "args": ("MU", "S", "H"),
        # These cells run at mutation rates a tenth to a whole multiple of the
        # selection load, where a single locus emulated by infinite sites takes
        # repeat hits and stops being a single locus.  Only an engine that
        # models a true two-allele locus may answer here.
        "needs": {"selection": True, "finite_population": True,
                  "biallelic_locus": True},
        "bodies": {
            "corpus": msb_corpus,
            "classical": msb_classical,
            "exact": msb_exact,
            "double": msb_double,
            "half": msb_half,
            "PLANTED": msb_planted,
        },
        "cells": [
            {"name": "mu/hs=0.10", "N": 2000, "MU": 2e-3, "S": 0.04, "H": 0.5,
             "T0": 2000, "T1": 20000},
            {"name": "mu/hs=0.50", "N": 2000, "MU": 5e-3, "S": 0.02, "H": 0.5,
             "T0": 2000, "T1": 20000},
            {"name": "mu/hs=1.00", "N": 2000, "MU": 5e-3, "S": 0.01, "H": 0.5,
             "T0": 2000, "T1": 20000},
        ],
    },
    # ------------------------------------------------------------------
    "mutationSelectionBalanceRecessive": {
        "lean_file": "Descent/Portability/RareVariantPortability.lean",
        "def_name": "mutationSelectionBalanceRecessive",
        "observable": "carrier_frequency",
        "args": ("MU", "S"),
        # A RECESSIVE claim may only be answered by an engine that models a
        # true two-allele locus.  Under an infinite-sites emulation the
        # compound heterozygote -- two different mutation objects at the same
        # position -- is scored as heterozygous at two sites and escapes
        # selection completely at h = 0, which inflates the measured frequency
        # and inflates it MORE as N grows.  fwdpy11 is excluded here for that
        # reason, not because it is a worse simulator.
        "needs": {"selection": True, "finite_population": True,
                  "biallelic_locus": True},
        "bodies": {
            "corpus": msbr_corpus,
            "linear": msbr_linear,
            "sqrt2s": msbr_half,
            "PLANTED": msbr_planted,
        },
        "cells": [
            {"name": "N=16000", "N": 16000, "MU": 1e-4, "S": 0.5, "H": 0.0,
             "T0": 2000, "T1": 12000},
            {"name": "N=4000", "N": 4000, "MU": 1e-4, "S": 0.5, "H": 0.0,
             "T0": 3000, "T1": 25000},
            {"name": "N=1000", "N": 1000, "MU": 1e-4, "S": 0.5, "H": 0.0,
             "T0": 3000, "T1": 50000},
            {"name": "N=200", "N": 200, "MU": 1e-4, "S": 0.5, "H": 0.0,
             "T0": 3000, "T1": 100000},
            {"name": "N=50", "N": 50, "MU": 1e-4, "S": 0.5, "H": 0.0,
             "T0": 3000, "T1": 100000},
        ],
    },
}

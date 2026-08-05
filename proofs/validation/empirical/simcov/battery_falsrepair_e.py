"""Battery falsrepair-E: serialFounderWithinTime, corrected body, with a control.

FRESHNESS guard string: FALSREPAIR_E_GUARD_20260804

battery_bulk12 measured the SUPERSEDED body
  2N(1 - exp(-a)) + exp(-a)(tAnc + 2 Nanc),  a = tAnc/(2N)
and recorded LEAD (no control) -- its "control" was the constant 2*Nanc
compared against itself, which cannot fail.  The body has since been corrected
to drop the double-counted tAnc.  Same design, new seeds, and a control the
engine can fail: with Nanc = N the history is single-epoch and the mean pairwise
TMRCA must be 2N whatever tAnc is.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record

GUARD = "FALSREPAIR_E_GUARD_20260804"


def tmrca(N, Nanc, tAnc, reps=60000, seed=44001):
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=N)
    dem.add_population_parameters_change(time=tAnc, initial_size=Nanc,
                                         population="A")
    times = []
    for ts in msprime.sim_ancestry(samples=1, ploidy=2, demography=dem,
                                   num_replicates=reps, random_seed=seed):
        tr = ts.first()
        times.append(tr.time(tr.root))
    a = np.asarray(times, float)
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(len(a)))


def main():
    print("FRESHNESS=OK %s" % GUARD)
    N, Nanc = 400.0, 4000.0
    cands = {
        "corrected body [2N(1-e^-a) + e^-a * 2 Nanc]":
            lambda a, t: 2 * N * (1 - math.exp(-a)) + math.exp(-a) * 2 * Nanc,
        "superseded body [2N(1-e^-a) + e^-a (tAnc + 2 Nanc)]":
            lambda a, t: (2 * N * (1 - math.exp(-a))
                          + math.exp(-a) * (t + 2 * Nanc)),
        "competing [2N(1-e^-a) + e^-a (2 Nanc - tAnc)]":
            lambda a, t: (2 * N * (1 - math.exp(-a))
                          + math.exp(-a) * (2 * Nanc - t)),
    }
    cells = {k: [] for k in cands}
    for tAnc in (200.0, 800.0, 3000.0):
        got, sem = tmrca(N, Nanc, tAnc, seed=44001 + int(tAnc))
        a = tAnc / (2 * N)
        lab = "tAnc=%.0f (N=%.0f, Nanc=%.0f)" % (tAnc, N, Nanc)
        print("  %s  TMRCA=%.2f +/- %.2f   " % (lab, got, sem)
              + "  ".join("%.2f" % fn(a, tAnc) for fn in cands.values()))
        for k, fn in cands.items():
            cells[k].append(dict(design=lab, lean=fn(a, tAnc), truth=got,
                                 sem=max(sem, 1e-6)))
    # Control: Nanc = N is a single-epoch history, mean TMRCA = 2N = 800
    # whatever tAnc is.  The engine can fail this; the old battery's control
    # compared 2*Nanc against 2*Nanc and could not.
    cgot, csem = tmrca(N, N, 800.0, seed=44777)
    print("  CONTROL Nanc=N=400, tAnc=800: TMRCA=%.2f +/- %.2f (2N=%.2f)"
          % (cgot, csem, 2 * N))
    control = dict(design="Nanc=N [single epoch, mean TMRCA = 2N]",
                   lean=2 * N, truth=cgot, sem=max(csem, 1e-6))
    reg = ("mean pairwise TMRCA in a two-epoch history under msprime, N = 400 "
           "to tAnc then Nanc = 4000, 60000 independent genealogies per cell, "
           "tAnc crossing the epoch boundary in both directions -- battery "
           "bulk12's design at new seeds with a control that can fail")
    for k, c in cells.items():
        record("serialFounderWithinTime -- " + k, "SerialFounderChain.lean", k,
               c, regime=reg, control=control)
    json.dump(RESULTS, open("battery_falsrepair_e_results.json", "w"),
              indent=1, default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        print("%-10s %-70s worst %.2f sems"
              % (r["verdict"], r["name"], r["worst"]["sems_off"]))


if __name__ == "__main__":
    main()

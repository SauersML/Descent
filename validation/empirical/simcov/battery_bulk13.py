"""Battery 28: asymmetric migration, redone on coalescence times.

Battery 9 tried `asymmetricFst` and `effectiveSymmetricMigration` with a forward
Wright-Fisher design and the run was thrown away: its SYMMETRIC cell disagreed
with the two-deme island result this branch had already validated, so the design
could not reproduce a known answer and had no standing to report a new one.

Redone here on the structured coalescent with `F_ST` read as
`1 - E[T_within]/E[T_between]`, which is the definition evaluated on the
genealogy and needs no estimator convention. The symmetric case is the positive
control and it is MEASURED rather than asserted: at `m12 = m21 = m` the answer
must be the two-deme island value `1/(1 + 2 * 4 Ne m)`, with the factor 2 being
`islandDemeCorrection` at `n = 2`, which two independent designs have now
confirmed.

Two claims are separated:

  asymmetricFst = 1/(1 + 4 Ne m_into) reads a SINGLE rate, so it has to be told
      which one. Both readings are reported -- the larger rate and the smaller --
      because a definition taking one argument where the system has two is
      exactly the underspecified-signature class this branch has already found
      twice.

  effectiveSymmetricMigration = (m12 + m21)/2 says an asymmetric pair behaves
      like a symmetric one at the average rate. That is a testable claim about
      the arithmetic mean specifically, and the design puts the same average
      under three different asymmetries so a formula depending on more than the
      mean would separate.
"""
import json
import math

import numpy as np

import simlib
from battery_core import RESULTS, record


def two_deme_asym_fst(Ne, m12, m21, reps=26, seed=1):
    """F_ST from coalescence times with asymmetric migration between two demes.

    msprime's migration_matrix entry [j][k] is the backward rate at which
    lineages in j move to k, so the two directions are set independently.
    """
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.set_migration_rate(source="A", dest="B", rate=m12)
    dem.set_migration_rate(source="B", dest="A", rate=m21)
    vals = []
    for r in range(reps):
        ts = msprime.sim_ancestry(samples={"A": 25, "B": 25}, demography=dem,
                                  sequence_length=4e6,
                                  recombination_rate=1e-8,
                                  random_seed=seed + r)
        A, B = ts.samples(population=0), ts.samples(population=1)
        da = ts.diversity([A], mode="branch")[0]
        db = ts.diversity([B], mode="branch")[0]
        dab = ts.divergence([A, B], indexes=[(0, 1)], mode="branch")[0]
        vals.append(1.0 - ((da + db) / 2.0) / dab)
    return simlib.summarize(vals)


def main():
    Ne = 1000
    m_bar = 1e-3                       # the average rate, held FIXED
    designs = [(1e-3, 1e-3), (1.5e-3, 5e-4), (1.8e-3, 2e-4)]

    # --- positive control: the symmetric cell against the known island value --
    sym = two_deme_asym_fst(Ne, m_bar, m_bar, seed=23001)
    known = 1 / (1 + 2 * 4 * Ne * m_bar)
    ctrl = dict(design="symmetric cell vs the validated two-deme island value",
                lean=known, truth=sym["mean"], sem=sym["sem"])
    print("  control: symmetric F_ST measured %.5f ± %.5f against known %.5f"
          % (sym["mean"], sym["sem"], known))

    cells_large, cells_small, cells_eff = [], [], []
    for m12, m21 in designs:
        s = two_deme_asym_fst(Ne, m12, m21, seed=23101)
        lab = "m12=%.1e m21=%.1e" % (m12, m21)
        big, small = max(m12, m21), min(m12, m21)
        cells_large.append(dict(design=lab + " [larger]",
                                lean=1 / (1 + 4 * Ne * big),
                                truth=s["mean"], sem=s["sem"]))
        cells_small.append(dict(design=lab + " [smaller]",
                                lean=1 / (1 + 4 * Ne * small),
                                truth=s["mean"], sem=s["sem"]))
        m_eff = (m12 + m21) / 2
        cells_eff.append(dict(design=lab + " [mean, x2 deme factor]",
                              lean=1 / (1 + 2 * 4 * Ne * m_eff),
                              truth=s["mean"], sem=s["sem"]))

    record("asymmetricFst [m_into read as the LARGER rate]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m_into)", cells_large,
           regime="two demes with asymmetric migration, F_ST from coalescence "
                  "times", control=ctrl)
    record("asymmetricFst [m_into read as the SMALLER rate]",
           "PortabilityDrift.lean", "1 / (1 + 4*Ne*m_into)", cells_small,
           regime="same runs, the other reading of the single rate argument",
           control=ctrl)
    record("effectiveSymmetricMigration", "PortabilityDrift.lean",
           "(m12 + m21) / 2, fed to the symmetric two-deme form", cells_eff,
           regime="the same arithmetic mean under three different asymmetries, "
                  "so a dependence on more than the mean would separate",
           control=ctrl)

    json.dump(RESULTS, open("battery_bulk13_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

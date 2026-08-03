"""Settle CHECK 1: is `coalFst = t/(t+2Ne)` consistent with msprime, or not?

The single-replicate run showed errors of +97.0%, -15.7%, -14.9%, -12.6% with
ALTERNATING SIGN, which reads like Monte Carlo noise -- and "probably noise" is
exactly the reasoning that leaves a real discrepancy unexamined.  So this
measures the error bars instead of assuming them.

NOTHING ABOUT THE MODEL IS CHANGED.  Same demography, same Ne and t, same
MU = RHO = 1e-8, same 2 Mb, same 40+40 diploid samples, same Hudson
ratio-of-averages estimator.  ONLY the replicate count changes.  Tuning the
simulation until the discrepancy shrinks is the failure this whole effort
exists to prevent; adding replicates until the UNCERTAINTY shrinks is the
opposite move and leaves the estimand alone.

WHY ONE REPLICATE WAS NEVER GOING TO SETTLE IT: at Ne=1000, RHO=1e-8 and
L=2 Mb the expected number of recombination events is 4*Ne*RHO*L = 80, so a
replicate contains on the order of eighty independent genealogies.  An F_ST of
0.02 estimated from eighty trees has a standard error comparable to its own
value.

POOLING IS RATIO-OF-AVERAGES, NOT AVERAGE-OF-RATIOS.  Hudson's estimator is a
ratio of sums over sites; averaging per-replicate ratios is biased at small
F_ST, which is precisely where the +97% cell sits.  Numerator and denominator
are summed across every replicate and divided once.  The delete-one jackknife
over replicates gives the standard error of that pooled ratio.
"""
import json, sys
import numpy as np
import msprime

MU = 1e-8
RHO = 1e-8
SEQ = 2e6
NDIP = 40                      # per deme, as in check_defs.py
CELLS = [(1000, 50), (1000, 100), (1000, 1000), (5000, 4000)]
REPS = int(sys.argv[1]) if len(sys.argv) > 1 else 200


def one(Ne, t, seed):
    """Return (numerator_sum, denominator_sum) for one replicate."""
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=Ne)
    dem.add_population(name="B", initial_size=Ne)
    dem.add_population(name="ANC", initial_size=Ne)
    dem.add_population_split(time=t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": NDIP, "B": NDIP}, demography=dem,
                              sequence_length=SEQ, recombination_rate=RHO,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)
    G = ts.genotype_matrix()
    if G.shape[0] == 0:
        return 0.0, 0.0
    a = 2 * NDIP
    c1 = G[:, :a].sum(axis=1).astype(float)
    c2 = G[:, a:2 * a].sum(axis=1).astype(float)
    p1, p2 = c1 / a, c2 / a
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (a - 1) - p2 * (1 - p2) / (a - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    ok = den > 0
    return float(num[ok].sum()), float(den[ok].sum())


out = []
for Ne, t in CELLS:
    nums, dens = [], []
    for r in range(REPS):
        n, d = one(Ne, t, 100000 + 7919 * r + Ne + t)
        nums.append(n); dens.append(d)
    nums, dens = np.array(nums), np.array(dens)
    pooled = nums.sum() / dens.sum()
    # delete-one jackknife over replicates
    jk = np.array([(nums.sum() - nums[i]) / (dens.sum() - dens[i])
                   for i in range(REPS)])
    se = np.sqrt((REPS - 1) / REPS * ((jk - jk.mean()) ** 2).sum())
    lean = t / (t + 2.0 * Ne)
    dev = pooled - lean
    z = dev / se if se > 0 else float("nan")
    rec = dict(Ne=Ne, t=t, reps=REPS, sim=pooled, se=se, coalFst=lean,
               deviation=dev, z=z,
               rel_err_pct=100.0 * dev / lean)
    out.append(rec)
    print(f"Ne={Ne:<6d} t={t:<6d} sim={pooled:.5f} +/- {se:.5f}   "
          f"coalFst={lean:.5f}   dev={dev:+.5f}  z={z:+.2f}  "
          f"rel={100.0*dev/lean:+.1f}%", flush=True)

print()
worst = max(abs(r["z"]) for r in out)
print(f"replicates per cell: {REPS}")
print(f"largest |z|: {worst:.2f}")
if worst < 3:
    print("VERDICT: every cell is within 3 SE of coalFst. The single-replicate")
    print("errors were Monte Carlo noise; the formula is consistent with msprime.")
else:
    print("VERDICT: at least one cell deviates by more than 3 SE. This is NOT")
    print("noise -- either coalFst is not the F_ST msprime measures here, or the")
    print("split model differs from the formula's. Reporting rather than tuning.")
json.dump(out, open("split_fst_power.json", "w"), indent=1)

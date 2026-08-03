"""Check the PGS portability definitions against an end-to-end simulation.

Pipeline: msprime two-population split -> additive causal architecture ->
phenotype in the source population -> marginal GWAS in the source -> clump+
threshold PGS -> evaluate R^2 in source and target.  Sweeping the split time
sweeps F_ST, which is the argument the Lean portability definitions take.

Definitions under test:

  ScoreDistribution.lean   pgsVariance = sum beta^2 * 2p(1-p)
                             (exact only under linkage equilibrium)
  PortabilityDrift.lean    Expected_Abs_Shift = sqrt(Var_Delta_Mu)*sqrt(2/pi)

Two selection laws that this script used to test are absent from the corpus,
and this script keeps their transcriptions so that the falsification stays
reproducible:

  stabilizingPortability  r2_0 fst strength = r2_0*(1-2*fst)*exp(-strength*fst)
  diversifyingPortability r2_0 fst lam      = r2_0*(1-2*fst)*(exp(-lam*fst))^2

Both carry a prefactor linear in F_ST, and this run measured the observed
target over source R^2 ratio against it:

  F_ST 0.0099 -> observed 0.550 against prefactor 0.980
  F_ST 0.0906 -> observed 0.213 against prefactor 0.819
  F_ST 0.2910 -> observed 0.103 against prefactor 0.418

No value of the free parameter rescues either law, because exp(-strength*fst)
tends to 1 as fst tends to 0, so both predict 0.98 of source R^2 at F_ST
0.0099 where the simulation gives 0.55. Keep these transcriptions. Deleting
them removes the only reproducible record of why the two laws are absent.

AND THIS SCRIPT IS NOT ONLY A FALSIFIER.  The same run CONFIRMED pgsVariance:
across the 18 replicates in port.json the linkage-equilibrium formula sits at a
mean ratio of 0.969 to the actual score variance, range 0.813 to 1.072, about
three per cent low, which is the direction and size its stated assumption
predicts.  That makes this file the only instrument that holds pgsVariance to a
measurement, so deleting it as "the script for two dead laws" would silently
retire a confirmation as well.

THREE REPLICATES PER CELL WAS NOT A MEASUREMENT.  The eighteen records above
are six split times at three replicates, with no error bar anywhere in the
file, and cells in the same condition have landed at 0.343, 0.370 and 0.639 --
scatter comparable to the effect being reported.  The falsification of the two
selection laws survives that, because the gap between 0.55 observed and 0.98
predicted at F_ST 0.0099 is far larger than any plausible standard error; the
CONFIRMATION of pgsVariance at "0.969, about three per cent low" does not,
because three per cent is smaller than the scatter that produced it.

So the grid is now swept on all three axes the claim depends on -- split time,
heritability, and causal-variant count -- and every cell reports the standard
error of its mean over replicates alongside the mean.  Each replicate is also
written individually, with its own wall time, so the next person to size a run
on this script does not have to guess.

THE DEFAULTS ARE STILL THE SMALL RUN.  One replicate is minutes of CPU and
gigabytes of memory at the shipped n_dip and sequence length, so a full
factorial is a cluster job, not a laptop job; `--help` shows how to ask for it.
"""
from __future__ import annotations

import argparse
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

import simprov  # noqa: E402

NE = 10000
MU = 1.25e-8
RHO = 1e-8

# Defaults are the run this file has always done: six split times, one
# heritability, one causal count, three replicates.  The full factorial is a
# flag away and is documented in the run plan rather than made the default,
# because one replicate here costs minutes of CPU and gigabytes of memory.
DEFAULT_SPLIT_TIMES = [200, 500, 1000, 2000, 4000, 8000]
DEFAULT_H2 = [0.5]
DEFAULT_NCAUSAL = [300]
DEFAULT_REPS = 3
DEFAULT_SEED = 1000

# The per-cell quantities whose mean and standard error are reported.  Naming
# them here rather than aggregating whatever keys happen to appear keeps a cell
# from silently losing a column when a replicate returns early.
CELL_METRICS = ("fst", "n_snps", "t_sec", "pgsVar_ratio",
                "r2A_all", "r2B_all", "ratio_all",
                "r2A_z2", "r2B_z2", "ratio_z2",
                "r2A_z4", "r2B_z4", "ratio_z4")


def lean_stabilizingPortability(r2_0, fst, strength):
    """Transcribed from the absent PortabilityBounds declaration
    stabilizingPortability. This run falsified it, and the header records
    the measurement that removed it."""
    return r2_0 * (1 - 2 * fst) * np.exp(-strength * fst)


def lean_pgsVariance(beta, p):
    """ScoreDistribution declaration pgsVariance, `∑ i, β i ^ 2 * (2 * p i * (1 - p i))`."""
    return float(np.sum(beta**2 * 2 * p * (1 - p)))


def hudson_fst(c1, c2, n1, n2):
    p1, p2 = c1 / n1, c2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    ok = den > 0
    return float(num[ok].sum() / den[ok].sum())


def standardize(X):
    p = (X.mean(axis=0) / 2.0).astype(np.float64)
    keep = (p > 0.01) & (p < 0.99)
    X = np.ascontiguousarray(X[:, keep])
    p = p[keep]
    scale = (1.0 / np.sqrt(2 * p * (1 - p))).astype(np.float32)
    X -= (2 * p).astype(np.float32)
    X *= scale
    return X, p, keep


def one_rep(args):
    import msprime
    split_t, n_dip, length, n_causal, h2, seed = args
    t_start = time.time()
    dem = msprime.Demography()
    for name in ("A", "B", "ANC"):
        dem.add_population(name=name, initial_size=NE)
    dem.add_population_split(time=split_t, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(samples={"A": n_dip, "B": n_dip}, demography=dem,
                              sequence_length=length, recombination_rate=RHO,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 1)

    # Keep dosages as int8 until the panel is selected: a float64 copy of the
    # full site set is ~14 GB per worker at n_dip=6000 and OOM-kills the node.
    G = ts.genotype_matrix()                            # sites x haploids, int8
    D = (G[:, 0::2] + G[:, 1::2]).T                     # individuals x sites
    del G
    D = np.ascontiguousarray(D, dtype=np.int8)

    cA = D[:n_dip].sum(axis=0, dtype=np.int64).astype(float)
    cB = D[n_dip:].sum(axis=0, dtype=np.int64).astype(float)
    fst = hudson_fst(cA, cB, 2 * n_dip, 2 * n_dip)

    # common variants in the SOURCE population define the analysis panel
    pA = cA / (2.0 * n_dip)
    panel = np.where((pA > 0.05) & (pA < 0.95))[0]
    A = np.ascontiguousarray(D[:n_dip][:, panel], dtype=np.float32)
    B = np.ascontiguousarray(D[n_dip:][:, panel], dtype=np.float32)
    del D

    ZA, pA, keepA = standardize(A)
    # standardize the target with the SOURCE allele frequencies, as a deployed
    # score must (the model ships fixed centering/scaling)
    pB_used = pA
    Bk = B[:, keepA]
    ZB = ((Bk - 2 * pB_used) / np.sqrt(2 * pB_used * (1 - pB_used))).astype(np.float32)

    rng = np.random.default_rng(seed + 7)
    M = ZA.shape[1]
    if M < n_causal * 3:
        return None
    causal = rng.choice(M, size=n_causal, replace=False)
    beta = rng.standard_normal(n_causal)

    gA = ZA[:, causal] @ beta
    gA_scaled = gA / gA.std()
    eA = rng.standard_normal(n_dip)
    y = np.sqrt(h2) * gA_scaled + np.sqrt(1 - h2) * eA
    y -= y.mean()

    gB = ZB[:, causal] @ beta
    gB_scaled = gB / gA.std()          # same scaling as deployed
    eB = rng.standard_normal(n_dip)
    yB = np.sqrt(h2) * gB_scaled + np.sqrt(1 - h2) * eB
    yB -= yB.mean()

    # Hold out half the SOURCE population.  R^2 must be measured out of sample
    # in both populations, otherwise the source number is inflated by
    # overfitting and the ratio confounds overfitting with portability.
    n_train = n_dip // 2
    tr = slice(0, n_train)
    te = slice(n_train, n_dip)
    bhat = (ZA[tr].T @ (y[tr] - y[tr].mean())) / n_train
    se = np.sqrt((1 - bhat**2).clip(1e-12) / n_train)
    z = bhat / se

    out = dict(split_t=split_t, fst=fst, n_causal=n_causal, h2=h2,
               n_snps=int(M), seed=seed)

    # clump+threshold PGS at several z thresholds
    for zt, tag in ((0.0, "all"), (2.0, "z2"), (4.0, "z4")):
        sel = np.where(np.abs(z) > zt)[0]
        if len(sel) < 5:
            out[f"r2A_{tag}"] = out[f"r2B_{tag}"] = float("nan")
            out[f"ratio_{tag}"] = float("nan")
            out[f"nsnp_{tag}"] = int(len(sel))
            continue
        w = bhat[sel]
        sA_te = ZA[te][:, sel] @ w          # held-out source individuals
        sB = ZB[:, sel] @ w                 # target population
        sA_tr = ZA[tr][:, sel] @ w          # in-sample, for reference only
        out[f"r2A_{tag}"] = float(np.corrcoef(sA_te, y[te])[0, 1] ** 2)
        out[f"r2B_{tag}"] = float(np.corrcoef(sB, yB)[0, 1] ** 2)
        out[f"r2Ain_{tag}"] = float(np.corrcoef(sA_tr, y[tr])[0, 1] ** 2)
        out[f"nsnp_{tag}"] = int(len(sel))
        # The portability ratio is formed PER REPLICATE and averaged, never as
        # a ratio of the two cell means: the two R^2 come from the same
        # simulated panel, so their fluctuations cancel within a replicate and
        # not between them.
        out[f"ratio_{tag}"] = (out[f"r2B_{tag}"] / out[f"r2A_{tag}"]
                               if out[f"r2A_{tag}"] > 0 else float("nan"))

    # pgsVariance: sum beta^2 2p(1-p) vs the actual variance of the score,
    # using the causal weights on raw dosages (linkage equilibrium assumption)
    braw = np.zeros(M)
    braw[causal] = beta / np.sqrt(2 * pA[causal] * (1 - pA[causal]))
    score_raw = A @ braw
    out["pgsVar_actual"] = float(score_raw.var())
    out["pgsVar_lean_LE"] = lean_pgsVariance(braw[causal], pA[causal])
    out["pgsVar_ratio"] = (out["pgsVar_lean_LE"] / out["pgsVar_actual"]
                           if out["pgsVar_actual"] > 0 else float("nan"))
    out["t_sec"] = time.time() - t_start
    return out


def _pm(s, dp):
    """Format a summary as mean +/- SE, and say so plainly when there is neither.

    A cell that produced one usable replicate has no standard error, and
    printing its mean as though it did is exactly the habit this rewrite is
    meant to break.
    """
    if s["mean"] is None:
        return "no data"
    if s["se"] is None:
        return ("%.*f (1 rep, no SE)" % (dp, s["mean"]))
    return "%.*f+/-%.*f" % (dp, s["mean"], dp, s["se"])


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Sweep split time, heritability and causal-variant count "
                    "through the msprime -> GWAS -> PGS portability pipeline.",
        epilog="One replicate is minutes of CPU and gigabytes of memory at the "
               "shipped --n-dip and --seq-length. Time a single replicate "
               "before sizing a factorial run.")
    ap.add_argument("--split-times", type=simprov.parse_ints,
                    default=DEFAULT_SPLIT_TIMES,
                    help="split times in generations, comma separated")
    ap.add_argument("--h2", type=simprov.parse_floats, default=DEFAULT_H2,
                    help="heritabilities, comma separated")
    ap.add_argument("--n-causal", type=simprov.parse_ints,
                    default=DEFAULT_NCAUSAL,
                    help="causal-variant counts, comma separated")
    ap.add_argument("--n-dip", type=int,
                    default=int(os.environ.get("NDIP", "3000")),
                    help="diploids per population (env NDIP)")
    ap.add_argument("--seq-length", type=float,
                    default=float(os.environ.get("LEN", "3e7")),
                    help="simulated sequence length in bp (env LEN)")
    simprov.add_sweep_args(ap, int(os.environ.get("REPS", str(DEFAULT_REPS))),
                           "port.json", DEFAULT_SEED)
    ap.set_defaults(jobs=int(os.environ.get("NPROC", "8")))
    args = ap.parse_args(argv)

    cells_spec = [(t, h2, nc) for t in args.split_times
                  for h2 in args.h2 for nc in args.n_causal]
    jobs = [(t, args.n_dip, args.seq_length, nc, h2,
             args.seed + 37 * r + t + 101 * nc + int(1000 * h2))
            for (t, h2, nc) in cells_spec for r in range(args.reps)]
    print("%d cells x %d replicates = %d simulations on %d workers"
          % (len(cells_spec), args.reps, len(jobs), args.jobs), flush=True)

    t0 = time.time()
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        raw = list(ex.map(one_rep, jobs, chunksize=1))
    print("simulation wall time %.1f s" % (time.time() - t0), flush=True)

    records, cells = [], []
    for ci, (t, h2, nc) in enumerate(cells_spec):
        blk = raw[ci * args.reps:(ci + 1) * args.reps]
        for r, o in enumerate(blk):
            if o is None:
                # A replicate that returned nothing had too few common variants
                # to place n_causal on. It is recorded, not dropped: a cell
                # standing on two survivors of five must not look like a cell of
                # two.
                records.append(dict(split_t=t, h2=h2, n_causal=nc, rep=r,
                                    seed=jobs[ci * args.reps + r][5],
                                    failed="panel smaller than 3 * n_causal"))
            else:
                records.append(dict(o, rep=r))
        good = [o for o in blk if o]
        cell = dict(split_t=t, h2=h2, n_causal=nc, reps=args.reps,
                    n_ok=len(good), n_failed=len(blk) - len(good))
        for k in CELL_METRICS:
            cell[k] = simprov.summarize([o.get(k, float("nan")) for o in good])
        cells.append(cell)
        print("t=%-6d h2=%.2f nc=%-5d  F_ST %s  target/source R2 %s  (n=%d)"
              % (t, h2, nc, _pm(cell["fst"], 4), _pm(cell["ratio_all"], 3),
                 cell["n_ok"]), flush=True)

    pv = simprov.summarize([o["pgsVar_ratio"] for o in raw
                            if o and "pgsVar_ratio" in o])
    print("")
    print("pgsVariance (linkage-equilibrium formula) / actual score variance:")
    if pv["n"] == 0:
        print("  no usable replicate produced one.")
    else:
        print("  mean %.4f  sd %s  se %s  range [%.4f, %.4f] over %d replicates"
              % (pv["mean"],
                 "%.4f" % pv["sd"] if pv["sd"] is not None else "n/a",
                 "%.4f" % pv["se"] if pv["se"] is not None else "n/a",
                 pv["min"], pv["max"], pv["n"]))
    print("  A three per cent shortfall is only a confirmation if the standard")
    print("  error above is well under three per cent. Read them together.")

    p = simprov.write(args.output, "popgen_defs/check_portability.py",
                      dict(split_times=args.split_times, h2=args.h2,
                           n_causal=args.n_causal, n_dip=args.n_dip,
                           seq_length=args.seq_length,
                           NE=NE, MU=MU, RHO=RHO),
                      args.seed, args.reps, cells, records)
    print("-> %s (%d cells, %d replicate records)"
          % (p, len(cells), len(records)))


if __name__ == "__main__":
    main()

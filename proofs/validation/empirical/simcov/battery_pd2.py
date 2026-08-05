"""Battery pd2: signal retention at migration-drift balance, with no ceiling to divide by.

WHAT THIS REPLACES.  `signalRetentionMigrationDrift` and
`retainedSignalVarianceMigrationDrift` are the last two definitions in
PortabilityDrift.lean with no verdict, and the reason is on the record in their
own docstrings: two runs of the same design disagreed by an order of magnitude
more than the error bars they quoted, and the instability was traced to a
CALIBRATION.  Retention was estimated as `w'Sigma_T beta / w'Sigma_S beta` with
`w = Sigma_S beta` fitted on the SAME source sample the denominator contracts
against, so the denominator carried squared estimation noise the numerator did
not, and the whole table had to be divided by a separately estimated "panmictic
ceiling".  That ceiling came out 0.8905 in one run and 1.0430 in the other -- a
value above one, which attenuation cannot produce, so the second estimate was
noise-dominated and every cell inherited a 17% swing.

THE FIX IS A SAMPLE SPLIT, NOT MORE REPLICATES.  Source individuals are split
into two halves.  The weights come from half A, the source-side covariance is
evaluated on half B:

    w        = Sigma_A beta          (half A of the source)
    Cov_src  = w' Sigma_B beta       (half B of the source, independent of A)
    Cov_tgt  = w' Sigma_T beta       (the target deme, independent of both)
    retention = Cov_tgt / Cov_src

`Sigma_A` and `Sigma_B` are independent estimates of the same source covariance,
so the denominator has no squared-noise inflation and there is NOTHING TO
CALIBRATE.  The ceiling is not estimated better; it is removed from the design.

POSITIVE CONTROL, and it is the one the old design could only assume: a single
panmictic population whose sample is split three ways into "half A", "half B"
and "target".  There `Sigma_T` is another independent estimate of the same
matrix, so retention must be 1.  A design that still attenuates fails here, and
the failure is visible rather than divided out.

THE BODY UNDER TEST, and its competitors on the same cells:

    signalRetentionMigrationDrift Ne m = (1 - F_ST) * sharedLDFromMigration(4 Ne m)

`sharedLDFromMigration M = M/(1+M)` was refuted by `battery_bulk34`, so the body
is carried BOTH ways: as written, with the LD factor taken from its migration
formula, and with the LD factor taken from the MEASURED cross-deme LD
correlation, which is the reading `covarianceDivergenceMutationDrift` gets.
Competitors: `1 - F_ST` alone, and the LD factor alone.  If the product is wrong
because it multiplies two factors each already below one, a single factor is what
survives, and the table has to be able to say which.

argument_source: model for `F_ST` and `M` where the closed forms are evaluated at
the simulation's own `Ne` and `m`; sample for the measured-LD reading, declared
because that reading takes its LD factor from the replicates it is scored on.
"""
import json
import math
import os
import sys
from multiprocessing import Pool

import numpy as np

GUARD = "PD2-FRESHNESS-RETENTION-SPLITSAMPLE-v1"

NE = 1000
SEQ = 5e6
RHO = 1e-8
MU = 1e-8
N_DIP = 300          # per deme
N_CAUSAL = 200
N_PAIRS = 4000       # site pairs for the LD-correlation measurement
REPS = 40


def _cov(G):
    """Sample covariance of the columns-as-individuals dosage matrix G (sites x n)."""
    Gc = G - G.mean(axis=1, keepdims=True)
    return (Gc @ Gc.T) / (G.shape[1] - 1)


def _r_vector(G, pairs):
    Gc = G - G.mean(axis=1, keepdims=True)
    nrm = np.sqrt((Gc ** 2).sum(axis=1))
    i, j = pairs[:, 0], pairs[:, 1]
    den = nrm[i] * nrm[j]
    num = (Gc[i] * Gc[j]).sum(axis=1)
    out = np.where(den > 0, num / np.where(den > 0, den, 1.0), np.nan)
    return out


def one_rep(args):
    kind, m, seed = args
    import msprime

    rng = np.random.default_rng(seed)
    if kind == "island":
        dem = msprime.Demography.island_model([NE, NE], migration_rate=m)
        ts = msprime.sim_ancestry(
            samples={"pop_0": N_DIP, "pop_1": N_DIP}, demography=dem,
            sequence_length=SEQ, recombination_rate=RHO, random_seed=seed)
    else:
        ts = msprime.sim_ancestry(
            samples=2 * N_DIP, population_size=NE,
            sequence_length=SEQ, recombination_rate=RHO, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 7)
    if ts.num_sites < 2 * N_CAUSAL:
        return None
    gm = ts.genotype_matrix()                      # sites x haplotypes
    n_hap = gm.shape[1]
    dos = gm[:, 0::2] + gm[:, 1::2]                # sites x diploids
    if kind == "island":
        src_all = np.arange(0, N_DIP)
        tgt = np.arange(N_DIP, 2 * N_DIP)
    else:
        # the control: one population, split three ways by label only
        perm = rng.permutation(2 * N_DIP)
        src_all, tgt = perm[:N_DIP], perm[N_DIP:]

    # common variants in the SOURCE, so the causal set is a source-ascertained
    # panel -- which is what a source-trained score has access to.
    p_src = dos[:, src_all].mean(axis=1) / 2.0
    keep = np.where((p_src > 0.05) & (p_src < 0.95))[0]
    if len(keep) < N_CAUSAL + 50:
        return None
    causal = rng.choice(keep, size=N_CAUSAL, replace=False)
    causal.sort()
    beta = rng.normal(size=N_CAUSAL)

    half = rng.permutation(src_all)
    A, B = half[: N_DIP // 2], half[N_DIP // 2:]

    Gc_A = dos[np.ix_(causal, A)].astype(float)
    Gc_B = dos[np.ix_(causal, B)].astype(float)
    Gc_T = dos[np.ix_(causal, tgt)].astype(float)

    SA, SB, ST = _cov(Gc_A), _cov(Gc_B), _cov(Gc_T)
    w = SA @ beta
    cov_src = float(w @ (SB @ beta))
    cov_tgt = float(w @ (ST @ beta))
    if cov_src <= 0:
        return None
    retention = cov_tgt / cov_src

    # F_ST, Hudson, as a ratio of averages over the common panel
    a = dos[np.ix_(keep, src_all)].sum(axis=1).astype(float)
    b = dos[np.ix_(keep, tgt)].sum(axis=1).astype(float)
    n1, n2 = 2.0 * len(src_all), 2.0 * len(tgt)
    p1, p2 = a / n1, b / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    fst = float(num.sum() / den.sum())

    # cross-deme correlation of signed LD, on pairs of the causal panel
    idx = rng.integers(0, N_CAUSAL, size=(N_PAIRS, 2))
    idx = idx[idx[:, 0] != idx[:, 1]]
    rS = _r_vector(dos[np.ix_(causal, src_all)].astype(float), idx)
    rT = _r_vector(Gc_T, idx)
    ok = np.isfinite(rS) & np.isfinite(rT)
    shared_ld = float(np.corrcoef(rS[ok], rT[ok])[0, 1])

    return dict(retention=retention, fst=fst, shared_ld=shared_ld)


def summarize(vals):
    v = np.array([x for x in vals if x is not None and np.isfinite(x)], float)
    return float(v.mean()), float(v.std(ddof=1) / math.sqrt(len(v))), len(v)


def main():
    print("FRESHNESS_GUARD=%s" % GUARD)
    cells_M = [0.4, 2.0, 8.0, 40.0]
    jobs = []
    for M in cells_M:
        m = M / (4.0 * NE)
        for r in range(REPS):
            jobs.append(("island", m, 900000 + int(1000 * M) + 31 * r))
    for r in range(REPS):
        jobs.append(("panmictic", 0.0, 700000 + 31 * r))

    pool = Pool(20)
    out = pool.map(one_rep, jobs)
    pool.close()
    pool.join()

    k = 0
    per_cell = []
    for M in cells_M:
        rows = [x for x in out[k:k + REPS] if x]
        k += REPS
        ret = summarize([x["retention"] for x in rows])
        fst = summarize([x["fst"] for x in rows])
        sld = summarize([x["shared_ld"] for x in rows])
        per_cell.append((M, ret, fst, sld, len(rows)))
        print("4Nm=%-6.1f n=%3d  retention %.4f +/- %.4f   fst %.4f +/- %.4f   shared_ld %.4f +/- %.4f"
              % (M, len(rows), ret[0], ret[1], fst[0], fst[1], sld[0], sld[1]))

    ctrl_rows = [x for x in out[k:k + REPS] if x]
    cret = summarize([x["retention"] for x in ctrl_rows])
    cfst = summarize([x["fst"] for x in ctrl_rows])
    print("\nCONTROL panmictic, one population split three ways: retention %.4f +/- %.4f "
          "(%.2f sems from 1), F_ST %.5f +/- %.5f"
          % (cret[0], cret[1], abs(cret[0] - 1.0) / cret[1], cfst[0], cfst[1]))

    control = dict(design="one panmictic population split three ways [retention = 1]",
                   lean=1.0, truth=cret[0], sem=cret[1])

    def shared_from_M(M):
        return M / (1.0 + M)

    forms = {
        "signalRetentionMigrationDrift [as written: (1-F_eq)*M/(1+M)]":
            lambda M, f, s: (M / (1.0 + M)) * shared_from_M(M),
        "signalRetentionMigrationDrift [measured F_ST, measured shared LD]":
            lambda M, f, s: (1.0 - f) * s,
        "[competing] 1 - F_ST alone":
            lambda M, f, s: 1.0 - f,
        "[competing] shared LD alone":
            lambda M, f, s: s,
    }

    import verdict
    results = []
    for name, fn in forms.items():
        cells = []
        for (M, ret, fst, sld, n) in per_cell:
            cells.append(dict(design="4Nm=%.1f" % M, lean=float(fn(M, fst[0], sld[0])),
                              truth=ret[0], sem=ret[1]))
        v, note, worst = verdict.classify(cells, control=control,
                                          sem_source="replicates", rel_floor=0.05)
        regime = ("two-deme island model at migration-drift balance, Ne=%d, %d Mb with "
                  "recombination %g, %d diploids per deme, %d causal sites; retention is "
                  "w'Sigma_T beta / w'Sigma_B beta with w = Sigma_A beta fitted on an "
                  "INDEPENDENT half of the source sample, so no panmictic ceiling is "
                  "estimated and none is divided out; %d replicates, sem across replicates"
                  % (NE, int(SEQ / 1e6), RHO, N_DIP, N_CAUSAL, REPS))
        verdict.report(name, "see docstring", cells, v, note, worst, regime=regime)
        preds = [c["lean"] for c in cells]
        results.append(dict(name=name, file="PortabilityDrift.lean", verdict=v, note=note,
                            regime=regime, cells=cells, worst=worst, guard=GUARD,
                            argument_source=("model" if "as written" in name else "sample"),
                            sem_source="replicates", oracle_independent=True,
                            span=(max(preds) - min(preds)) / max(abs(max(preds)), 1e-12)))

    results.append(dict(name="[controls]", guard=GUARD,
                        panmictic_retention=dict(mean=cret[0], sem=cret[1]),
                        panmictic_fst=dict(mean=cfst[0], sem=cfst[1]),
                        measured=[dict(M=M, retention=r[0], retention_sem=r[1],
                                       fst=f[0], fst_sem=f[1], shared_ld=s[0], shared_ld_sem=s[1],
                                       n=n)
                                  for (M, r, f, s, n) in per_cell]))
    json.dump(results, open("battery_pd2_results.json", "w"), indent=1)
    print("\nFRESHNESS_GUARD=%s DONE" % GUARD)


if __name__ == "__main__":
    main()

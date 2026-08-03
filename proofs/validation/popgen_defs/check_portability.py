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
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

NE = 10000
MU = 1.25e-8
RHO = 1e-8


def lean_stabilizingPortability(r2_0, fst, strength):
    """PortabilityBounds.lean:223"""
    return r2_0 * (1 - 2 * fst) * np.exp(-strength * fst)


def lean_pgsVariance(beta, p):
    """ScoreDistribution.lean:42  `∑ i, β i ^ 2 * (2 * p i * (1 - p i))`"""
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
            continue
        w = bhat[sel]
        sA_te = ZA[te][:, sel] @ w          # held-out source individuals
        sB = ZB[:, sel] @ w                 # target population
        sA_tr = ZA[tr][:, sel] @ w          # in-sample, for reference only
        out[f"r2A_{tag}"] = float(np.corrcoef(sA_te, y[te])[0, 1] ** 2)
        out[f"r2B_{tag}"] = float(np.corrcoef(sB, yB)[0, 1] ** 2)
        out[f"r2Ain_{tag}"] = float(np.corrcoef(sA_tr, y[tr])[0, 1] ** 2)
        out[f"nsnp_{tag}"] = int(len(sel))

    # pgsVariance: sum beta^2 2p(1-p) vs the actual variance of the score,
    # using the causal weights on raw dosages (linkage equilibrium assumption)
    braw = np.zeros(M)
    braw[causal] = beta / np.sqrt(2 * pA[causal] * (1 - pA[causal]))
    score_raw = A @ braw
    out["pgsVar_actual"] = float(score_raw.var())
    out["pgsVar_lean_LE"] = lean_pgsVariance(braw[causal], pA[causal])
    return out


def main():
    n_dip = int(os.environ.get("NDIP", "3000"))
    length = float(os.environ.get("LEN", "3e7"))
    n_causal = int(os.environ.get("NCAUSAL", "300"))
    reps = int(os.environ.get("REPS", "3"))
    jobs = []
    for split_t in (200, 500, 1000, 2000, 4000, 8000):
        for r in range(reps):
            jobs.append((split_t, n_dip, length, n_causal, 0.5,
                         1000 + 37 * r + split_t))
    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "18"))) as ex:
        out = [f.result() for f in [ex.submit(one_rep, a) for a in jobs]]
    out = [o for o in out if o]
    with open(sys.argv[1] if len(sys.argv) > 1 else "port.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()

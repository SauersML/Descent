"""Round 5: a batch of cheap, independent definition checks.

  LDDecayTheory.lean:153    admixtureLD a d1 d2 = a(1-a) d1 d2
  LDDecayTheory.lean:192    bottleneckLDAmplification N_b t = 1-(1-1/(2N_b))^t
  PortabilityDrift.lean:252 Expected_Abs_Shift = sqrt(Var_Delta_Mu)*sqrt(2/pi)
  SampleOverlapBias.lean:54 partialOverlapR2 = r2 + f*(h2-r2)/n_gwas
  DemographicHistory.lean:64 demoSteppingStoneFst d Ne m s2 = d/(d+4 Ne m s2)
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


def lean_admixtureLD(a, d1, d2):
    return a * (1 - a) * d1 * d2


def lean_bottleneckLDAmplification(N_b, t):
    return 1 - (1 - 1 / (2 * N_b)) ** t


def lean_partialOverlapR2(r2_true, h2, f, n_gwas):
    return r2_true + f * (h2 - r2_true) / n_gwas


def lean_demoSteppingStoneFst(d, Ne, m, s2):
    return d / (d + 4 * Ne * m * s2)


# --------------------------------------------------------------------------

def check_admixture_ld(args):
    """Two loci, admixed population formed from A and B in proportion alpha."""
    alpha, pA1, pB1, pA2, pB2, n, seed = args
    rng = np.random.default_rng(seed)
    origin = rng.random(n) < alpha
    p1 = np.where(origin, pA1, pB1)
    p2 = np.where(origin, pA2, pB2)
    g1 = (rng.random(n) < p1).astype(float)
    g2 = (rng.random(n) < p2).astype(float)
    D_obs = float(np.mean(g1 * g2) - np.mean(g1) * np.mean(g2))
    return dict(check="admixtureLD", alpha=alpha, n=n,
                sim=D_obs,
                lean=lean_admixtureLD(alpha, pA1 - pB1, pA2 - pB2))


def check_bottleneck_ld(args):
    """Two-locus WF: does 1-(1-1/2N)^t describe the rise in E[r^2]?"""
    N, r, gens, reps, seed = args
    rng = np.random.default_rng(seed)
    x = np.zeros((reps, 4))
    # start at linkage equilibrium with both loci at frequency 1/2
    x[:, 0] = x[:, 1] = x[:, 2] = x[:, 3] = 0.25
    twoN = 2 * N
    out = []
    for t in range(1, gens + 1):
        D = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
        y = x.copy()
        y[:, 0] -= r * D
        y[:, 3] -= r * D
        y[:, 1] += r * D
        y[:, 2] += r * D
        y = np.clip(y, 0, None)
        y /= y.sum(axis=1, keepdims=True)
        counts = np.empty_like(y)
        for i in range(reps):
            counts[i] = rng.multinomial(twoN, y[i])
        x = counts / twoN
        if t in (5, 10, 25, 50, 100):
            pA = x[:, 0] + x[:, 1]
            pB = x[:, 0] + x[:, 2]
            D2 = x[:, 0] * x[:, 3] - x[:, 1] * x[:, 2]
            den = pA * (1 - pA) * pB * (1 - pB)
            ok = den > 1e-12
            r2 = np.zeros_like(D2)
            r2[ok] = D2[ok] ** 2 / den[ok]
            out.append(dict(check="bottleneckLD", N=N, r=r, t=t,
                            sim_Er2=float(r2.mean()),
                            lean=lean_bottleneckLDAmplification(N, t)))
    return out


def check_expected_abs_shift(args):
    """Mean |X| for X ~ N(0, v) is sqrt(v)*sqrt(2/pi) -- half-normal mean."""
    v, n, seed = args
    rng = np.random.default_rng(seed)
    x = rng.normal(0, np.sqrt(v), size=n)
    return dict(check="ExpectedAbsShift", var=v,
                sim=float(np.abs(x).mean()),
                lean=float(np.sqrt(v) * np.sqrt(2 / np.pi)))


def check_partial_overlap(args):
    """PGS R^2 in a target sample that shares a fraction f with the GWAS."""
    n_gwas, n_test, f, h2, n_snp, reps, seed = args
    rng = np.random.default_rng(seed)
    r2_in, r2_out, r2_mix = [], [], []
    for _ in range(reps):
        beta = rng.standard_normal(n_snp) / np.sqrt(n_snp)
        Xg = rng.standard_normal((n_gwas, n_snp))
        gg = Xg @ beta
        gg /= gg.std()
        yg = np.sqrt(h2) * gg + np.sqrt(1 - h2) * rng.standard_normal(n_gwas)
        bhat = (Xg.T @ (yg - yg.mean())) / n_gwas

        n_shared = int(round(f * n_test))
        idx_shared = rng.choice(n_gwas, n_shared, replace=False) if n_shared else []
        Xn = rng.standard_normal((n_test - n_shared, n_snp))
        gn = Xn @ beta
        gn /= np.sqrt(n_snp) * np.sqrt(1 / n_snp)  # unit-ish scale
        yn = np.sqrt(h2) * (Xn @ beta) / np.std(Xg @ beta) \
            + np.sqrt(1 - h2) * rng.standard_normal(n_test - n_shared)
        if n_shared:
            Xt = np.vstack([Xg[idx_shared], Xn])
            yt = np.concatenate([yg[idx_shared], yn])
        else:
            Xt, yt = Xn, yn
        s = Xt @ bhat
        r2_mix.append(float(np.corrcoef(s, yt)[0, 1] ** 2))
        s_out = Xn @ bhat
        r2_out.append(float(np.corrcoef(s_out, yn)[0, 1] ** 2))
        s_in = Xg @ bhat
        r2_in.append(float(np.corrcoef(s_in, yg)[0, 1] ** 2))
    r2_true = float(np.mean(r2_out))
    return dict(check="partialOverlap", n_gwas=n_gwas, f=f, h2=h2, n_snp=n_snp,
                r2_out=r2_true, r2_in=float(np.mean(r2_in)),
                sim_mixed=float(np.mean(r2_mix)),
                lean=lean_partialOverlapR2(r2_true, h2, f, n_gwas))


def check_stepping_stone(args):
    import msprime
    ndemes, Ne, m, d, seed = args
    dem = msprime.Demography.stepping_stone_model([Ne] * ndemes,
                                                  migration_rate=m,
                                                  boundaries=True)
    samples = {f"pop_{i}": (25 if i in (0, d) else 0) for i in range(ndemes)}
    ts = msprime.sim_ancestry(samples=samples, demography=dem,
                              sequence_length=3e6, recombination_rate=1e-8,
                              random_seed=seed)
    ss = [list(range(50)), list(range(50, 100))]
    dxy = ts.divergence(sample_sets=ss, indexes=[(0, 1)], mode="branch")[0]
    pi = ts.diversity(sample_sets=ss, mode="branch")
    fst = float(1 - (pi[0] + pi[1]) / 2 / dxy)
    return dict(check="steppingStone", ndemes=ndemes, Ne=Ne, m=m, d=d,
                sim=fst, lean=lean_demoSteppingStoneFst(d, Ne, m, 1.0))


def main():
    jobs = []
    for alpha in (0.2, 0.5, 0.8):
        jobs.append((check_admixture_ld,
                     (alpha, 0.8, 0.2, 0.7, 0.1, 4_000_000, 5 + int(alpha * 10))))
    for N in (100, 500):
        jobs.append((check_bottleneck_ld, (N, 0.01, 100, 6000, 31 + N)))
    for v in (0.001, 0.01, 0.1):
        jobs.append((check_expected_abs_shift, (v, 2_000_000, 77 + int(v * 1000))))
    for f in (0.0, 0.1, 0.25, 0.5, 1.0):
        jobs.append((check_partial_overlap, (2000, 2000, f, 0.5, 500, 6, 13 + int(f * 100))))
    for d in (1, 2, 4, 8):
        jobs.append((check_stepping_stone, (10, 1000, 0.002, d, 400 + d)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "20"))) as ex:
        res = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]
    out = []
    for r in res:
        out.extend(r) if isinstance(r, list) else out.append(r)
    with open(sys.argv[1] if len(sys.argv) > 1 else "b5.json", "w") as fh:
        json.dump(out, fh)
    print(f"wrote {len(out)} records")


if __name__ == "__main__":
    main()

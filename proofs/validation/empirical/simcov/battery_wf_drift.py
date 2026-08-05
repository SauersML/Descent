"""In-regime test of ClosedPopulationNoMutation.retention.

CLAIM UNDER TEST:  H_t / H_0 == (1 - 1/(2 Ne))^t
REGIME:            closed population, NO mutation. This is the regime the
                   structure's `mutation_negligible` field enforces; the run
                   that produced the FALSIFIED verdict was at demographic
                   equilibrium, where mutation is not negligible.

DESIGN.  Forward Wright-Fisher on independent biallelic loci, mutation rate
zero, starting from standing variation. Per generation each locus draws
Binomial(2Ne, p)/(2Ne). The decay H_{t+1} = H_t (1 - 1/(2Ne)) is exact in
EXPECTATION for Wright-Fisher irrespective of linkage -- linkage changes the
variance, not the mean -- so independent loci is the correct design and gives
tighter bars than a linked one.

THE DENOMINATOR TRAP, handled explicitly.  H is averaged over ALL loci,
including those that have fixed (which contribute 0). Conditioning on loci that
are still segregating inflates H exactly where drift has done its work, which
is this regime. The conditioned estimator is carried alongside as a CONTROL
that must FAIL: if it does not, the design is not sensitive to the trap and the
agreement of the main estimator means less.

COMPETITORS, on the same cells, because a match against no alternative is not a
measurement:
    (1 - 1/Ne)^t        haploid ploidy
    (1 - 1/(2Ne))^(2t)  doubled exponent
    exp(-t/(2Ne))       diffusion limit
    1                   no decay at all
"""
import json, sys
import numpy as np

GUARD = "wf-drift-in-regime-v1"


def run(ne, n_loci, n_reps, generations, seed):
    rng = np.random.default_rng(seed)
    two_n = 2 * ne
    # Standing variation at t = 0. Uniform on (0,1) keeps the initial spectrum
    # broad rather than concentrating it where drift is slowest.
    p = rng.uniform(0.05, 0.95, size=(n_reps, n_loci))
    h0_all = (2 * p * (1 - p)).mean(axis=1)
    h0_seg = h0_all.copy()

    out = []
    checkpoints = sorted(set(int(round(g)) for g in generations))
    for gen in range(1, max(checkpoints) + 1):
        p = rng.binomial(two_n, p) / two_n
        if gen in checkpoints:
            het = 2 * p * (1 - p)
            ratio_all = het.mean(axis=1) / h0_all
            seg = het > 0
            with np.errstate(invalid="ignore"):
                seg_mean = np.where(seg.sum(axis=1) > 0,
                                    (het * seg).sum(axis=1) / np.maximum(seg.sum(axis=1), 1),
                                    np.nan)
            ratio_seg = seg_mean / h0_seg
            out.append({
                "generations": gen,
                "measured": float(ratio_all.mean()),
                "sem": float(ratio_all.std(ddof=1) / np.sqrt(n_reps)),
                "measured_segregating_only": float(np.nanmean(ratio_seg)),
                "predicted": float((1 - 1 / two_n) ** gen),
                "competitor_haploid": float((1 - 1 / ne) ** gen),
                "competitor_doubled": float((1 - 1 / two_n) ** (2 * gen)),
                "competitor_diffusion": float(np.exp(-gen / two_n)),
                "competitor_no_decay": 1.0,
            })
    return out


def main():
    print(f"GUARD={GUARD}")
    print(f"numpy={np.__version__}")
    results = {}
    for ne in (100, 250):
        gens = [int(ne * f) for f in (0.25, 0.5, 1.0, 2.0)]
        rows = run(ne=ne, n_loci=5000, n_reps=40, generations=gens, seed=20260804 + ne)
        results[ne] = rows
        print(f"\n=== Ne = {ne}, 5000 loci, 40 replicates, mutation rate 0 ===")
        print(f"{'t':>6} {'measured':>10} {'sem':>8} {'predicted':>10} {'sems':>7}"
              f" {'haploid':>9} {'doubled':>9} {'diffusion':>10} {'segOnly':>9}")
        for r in rows:
            def sems(x):
                return abs(r["measured"] - x) / r["sem"] if r["sem"] > 0 else float("inf")
            print(f"{r['generations']:>6} {r['measured']:>10.5f} {r['sem']:>8.5f} "
                  f"{r['predicted']:>10.5f} {sems(r['predicted']):>7.2f} "
                  f"{sems(r['competitor_haploid']):>9.1f} {sems(r['competitor_doubled']):>9.1f} "
                  f"{sems(r['competitor_diffusion']):>10.1f} "
                  f"{sems(r['measured_segregating_only']):>9.1f}")

    worst = 0.0
    for rows in results.values():
        for r in rows:
            worst = max(worst, abs(r["measured"] - r["predicted"]) / r["sem"])
    print(f"\nworst cell against the claim: {worst:.2f} sems")
    print("competitor columns are sems between the MEASURED value and that "
          "competitor; a large number is a rejection.")
    with open("wf_drift_results.json", "w") as fh:
        json.dump({"guard": GUARD, "results": {str(k): v for k, v in results.items()}}, fh, indent=1)


if __name__ == "__main__":
    sys.exit(main())

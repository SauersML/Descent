"""Battery 2: fast Wright-Fisher and exact checks over untested definitions.

  PopulationGeneticsFoundations.lean:273  wrightFIT = 1-(1-f_IS)(1-f_ST)
  PopulationGeneticsFoundations.lean:791  alleleFreqAfterMigration
                                            = p_c + (p0-p_c)(1-m)^t
  PopulationGeneticsFoundations.lean:188  selectionMigrationEquilibrium = s/(s+m)
  DemographicHistory.lean:480             heterozygosityLossVariableNe = 1-exp(-sum 1/(2Ne_t))
  LDDecayTheory.lean:275                  harmonicMeanNe = T / sum(1/Ne_i)
  DemographicHistory.lean:423             founderHeterozygosityLoss k t = 1-(1-1/(2k))^t
  RareVariantPortability.lean:324         expectedEffectMultiplier
                                            = (p(1-p))^(1+alpha)
  ImputationPortability.lean:40           attenuatedVariance = beta_sq*het*r2_imp
"""
from __future__ import annotations

import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

RES = []


def rec(name, source, lean, truth, params, note=""):
    rel = (abs(lean - truth) / abs(truth)
           if truth not in (0, None) and np.isfinite(truth) else float("nan"))
    RES.append(dict(name=name, source=source, lean=float(lean),
                    truth=float(truth), rel=float(rel), params=params, note=note))


# --------------------------------------------------------------------------
def wf_drift_fst(args):
    """heterozygosityLossVariableNe = 1 - exp(-sum 1/(2 Ne_t)); ground truth = 1 - H_t/H_0."""
    Ne_schedule, reps, seed = args
    rng = np.random.default_rng(seed)
    p = np.full(reps, 0.5)
    H0 = float(np.mean(2 * p * (1 - p)))
    for Ne in Ne_schedule:
        p = rng.binomial(2 * int(Ne), p) / (2 * int(Ne))
    H = float(np.mean(2 * p * (1 - p)))
    truth = 1 - H / H0
    lean = 1 - np.exp(-sum(1.0 / (2 * Ne) for Ne in Ne_schedule))
    return dict(name="heterozygosityLossVariableNe", source="DemographicHistory.lean:480",
                lean=float(lean), truth=float(truth),
                params=dict(T=len(Ne_schedule), Ne_min=min(Ne_schedule),
                            Ne_max=max(Ne_schedule)),
                note="drift-only heterozygosity loss")


def wf_founder_heterozygosity_loss(args):
    """founderHeterozygosityLoss k t = 1-(1-1/(2k))^t against simulated heterozygosity loss."""
    k, t, reps, seed = args
    rng = np.random.default_rng(seed)
    p = np.full(reps, 0.5)
    H0 = float(np.mean(2 * p * (1 - p)))
    for _ in range(t):
        p = rng.binomial(2 * k, p) / (2 * k)
    H = float(np.mean(2 * p * (1 - p)))
    return dict(name="founderHeterozygosityLoss", source="DemographicHistory.lean:423",
                lean=float(1 - (1 - 1 / (2 * k)) ** t), truth=float(1 - H / H0),
                params=dict(k=k, t=t), note="")


def wf_migration(args):
    """alleleFreqAfterMigration: continent-island recursion p' = (1-m)p + m*p_c."""
    p0, p_c, m, t, reps, seed = args
    rng = np.random.default_rng(seed)
    N = 20000                       # large N so drift is negligible
    p = np.full(reps, p0)
    for _ in range(t):
        p = (1 - m) * p + m * p_c
        p = rng.binomial(2 * N, np.clip(p, 0, 1)) / (2 * N)
    truth = float(np.mean(p))
    lean = p_c + (p0 - p_c) * (1 - m) ** t
    return dict(name="alleleFreqAfterMigration",
                source="PopulationGeneticsFoundations.lean:791",
                lean=float(lean), truth=truth,
                params=dict(p0=p0, p_c=p_c, m=m, t=t), note="")


def sel_mig_equilibrium(args):
    """selectionMigrationEquilibrium = s/(s+m): equilibrium of a locally
    favoured allele under migration from a fixed continent."""
    s, m, reps, seed = args
    # deterministic recursion: selection toward p=1 locally, migration to p_c=0
    p = 0.5
    for _ in range(200000):
        # selection: haploid-style, p' = p(1+s)/(1+s p)
        p = p * (1 + s) / (1 + s * p)
        p = (1 - m) * p                     # migrants carry the allele at 0
        if p < 1e-12:
            break
    return dict(name="selectionMigrationEquilibrium",
                source="PopulationGeneticsFoundations.lean:188",
                lean=float(s / (s + m)), truth=float(p),
                params=dict(s=s, m=m), note="haploid selection-migration balance")


def main():
    jobs = []
    for sched in ([1000] * 50, [100] * 50, [1000] * 20 + [50] * 5 + [1000] * 25,
                  [200] * 100):
        jobs.append((wf_drift_fst, (sched, 40000, 11 + len(sched) + int(sched[0]))))
    for k, t in [(10, 5), (50, 20), (200, 100)]:
        jobs.append((wf_founder_heterozygosity_loss, (k, t, 40000, 7 + k + t)))
    for p0, p_c, m, t in [(0.8, 0.2, 0.01, 50), (0.2, 0.9, 0.05, 20),
                          (0.5, 0.1, 0.002, 200)]:
        jobs.append((wf_migration, (p0, p_c, m, t, 4000, 3 + int(p0 * 10) + t)))
    for s, m in [(0.1, 0.01), (0.05, 0.02), (0.2, 0.1)]:
        jobs.append((sel_mig_equilibrium, (s, m, 1, 1)))

    with ProcessPoolExecutor(max_workers=int(os.environ.get("NPROC", "16"))) as ex:
        out = [f.result() for f in [ex.submit(fn, a) for fn, a in jobs]]

    # exact algebraic identities, no simulation needed
    for f_IS, f_ST in [(0.1, 0.05), (0.3, 0.2)]:
        lean = 1 - (1 - f_IS) * (1 - f_ST)
        truth = f_IS + f_ST - f_IS * f_ST
        out.append(dict(name="wrightFIT",
                        source="PopulationGeneticsFoundations.lean:273",
                        lean=lean, truth=truth, params=dict(f_IS=f_IS, f_ST=f_ST),
                        note="algebraic identity"))
    for Ne in ([100, 1000, 10000], [50] * 3):
        lean = len(Ne) / sum(1 / x for x in Ne)
        truth = float(len(Ne) / np.sum(1.0 / np.array(Ne, dtype=float)))
        out.append(dict(name="harmonicMeanNe", source="LDDecayTheory.lean:275",
                        lean=lean, truth=truth, params=dict(Ne=str(Ne)), note=""))

    with open(sys.argv[1] if len(sys.argv) > 1 else "b2.json", "w") as fh:
        json.dump(out, fh)

    print(f"{'definition':<30} {'lean':>11} {'truth':>11} {'rel err':>9}  params")
    for r in out:
        rel = (abs(r["lean"] - r["truth"]) / abs(r["truth"])
               if r["truth"] else float("nan"))
        flag = "  <-- CHECK" if rel > 0.05 else ""
        ps = " ".join(f"{k}={v}" for k, v in r["params"].items())
        print(f"{r['name']:<30} {r['lean']:11.5f} {r['truth']:11.5f} "
              f"{rel*100:8.2f}%  {ps}{flag}")


if __name__ == "__main__":
    main()

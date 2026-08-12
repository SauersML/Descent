"""BLIND GATE 2 (v3.1 mixture), stage 3: the single-shot grader.  Run ONCE, after the fresh seeds
finish; every rule here is fixed before any gate outcome exists.

Measured side, per the data files' own metric_rule ("Use *-deme-test rows only"):
  - anchor r2_train: train-deme-test rows, corr(PGS_raw, true_liab)^2
  - per-target ratio: other-deme-test rows, corr^2 / anchor
  - per-target AUC: Mann-Whitney of PGS_raw against y_binary on other-deme-test rows
phenoC is the pre-registered primary (drift-proof); phenoA is reported as secondary.

Grading: per phenotype, residuals pooled at SEED level (each seed contributes its
mean over target demes), bars P1/P2 = |seed mean| <= 3 * seed-sem.  Verdict written
to gate_verdict.json; this file must not be edited after the pin commit.
"""
import json
import glob
import math
import sys

import numpy as np
import pandas as pd

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/descent/validation/empirical/gate")
import gate_predictor_v31 as GP

TO = "/projects/standard/hsiehph/sauer354/theory-out"
SEED_GLOB = f"{TO}/gate2_l3/grid2d_{{pheno}}_realpt_g2s*.parquet"


def auc_mw(score, y):
    s1, s0 = score[y == 1], score[y == 0]
    if len(s1) == 0 or len(s0) == 0:
        return None
    order = np.concatenate([s0, s1]).argsort().argsort()
    return float((order[len(s0):] + 1).sum() - len(s1) * (len(s1) + 1) / 2) / (len(s0) * len(s1))


def main():
    tables = GP.load_all()
    verdict = {"bars": {}, "seeds": {}}
    for pheno in ("phenoC", "phenoA"):
        seed_ratio_resid, seed_auc_resid = [], []
        for path in sorted(glob.glob(SEED_GLOB.format(pheno=pheno))):
            seed = path.split("g2s")[-1].split(".")[0]
            side = json.load(open(f"{TO}/gate2_l3/grid2d_realpt_g2s{seed}.json"))
            t = side["train_deme"]
            df = pd.read_parquet(path)
            test = df[df["split"].astype(str).str.contains("test")]
            deme = test["deme"].to_numpy()
            pgs = test["PGS_raw"].to_numpy()
            liab = test["true_liab"].to_numpy()
            yb = test["y_binary"].to_numpy()
            mt = deme == t
            if mt.sum() < 30:
                continue
            r2t = float(np.corrcoef(pgs[mt], liab[mt])[0, 1] ** 2)
            if r2t <= 0:
                continue
            pred = GP.predict(tables, t, r2t, float(side.get("pt", {}).get("best_p_threshold", 1e-6)))
            rres, ares = [], []
            for j in np.unique(deme).astype(int):
                if j == t or j not in pred:
                    continue
                m = deme == j
                if m.sum() < 30:
                    continue
                r2j = float(np.corrcoef(pgs[m], liab[m])[0, 1] ** 2)
                rres.append(r2j / r2t - pred[j]["ratio"])
                am = auc_mw(pgs[m], yb[m])
                if am is not None and 0.01 < yb[m].mean() < 0.99:
                    ares.append(am - pred[j]["auc"])
            if rres:
                seed_ratio_resid.append(float(np.mean(rres)))
            if ares:
                seed_auc_resid.append(float(np.mean(ares)))
        for name, arr in (("P1_ratio", seed_ratio_resid), ("P2_auc", seed_auc_resid)):
            a = np.array(arr)
            n = len(a)
            sem = a.std(ddof=1) / math.sqrt(n) if n > 1 else float("nan")
            verdict["bars"][f"{pheno}_{name}"] = {
                "n_seeds": n,
                "mean": float(a.mean()) if n else None,
                "sem": float(sem) if n > 1 else None,
                "pass": bool(abs(a.mean()) <= 3 * sem) if n > 1 else None,
                "per_seed": [round(float(x), 5) for x in a],
            }
    json.dump(verdict, open(f"{TO}/gate2_verdict.json", "w"), indent=1, sort_keys=True)
    print(json.dumps(verdict["bars"], indent=1, sort_keys=True))


if __name__ == "__main__":
    main()

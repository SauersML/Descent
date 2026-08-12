"""LAYER-3 GRADE v3 -- the AUC chain's h2 corrected, derived before running.

ROOT CAUSE OF grade2's P2 FAILURE (+0.05 uniform, ~6 sems, both cases):
  grade2 built h2_j from `true_slope_deme`, which gen_real_pt.py:502 defines as
  the per-deme PGS_z->liability REGRESSION SLOPE Cov(liab,PGS_z)/Var(PGS_z) --
  not a genetic-scale factor.  Squaring a regression slope of order ~0.3 made
  h2_j tiny, under-predicted the full-liability r2, under-predicted AUC, and
  produced exactly the observed positive residual.

THE CORRECT COMPOSITION (exact given the pipeline's own definitions):
  outcome y = 1{c0 + base_j + true_liab + e > 0}, e ~ N(0, 1), base_j constant
  within deme, true_liab standardized GLOBALLY.  Within deme j the latent full
  liability has variance Var_j(true_liab) + 1, and Cov(X, full) = Cov(X, liab),
  so  Corr^2_j(X, full) = r2_j(X, liab) * h2_j,   h2_j = V_j / (V_j + 1),
  V_j = within-deme variance of the globally standardized genetic liability.
  Identical across phenos (phenoC demeans by a within-deme constant).

TWO GRADES EMITTED, SAME CELLS:
  P2-meas: h2_j from the MEASURED V_j (composition check -- is the chain right
           once h2 is the right object?).
  P2-thy:  h2_j from THEORY: V_j = m1_asc[j] / (sum_k w_k m1_asc[k] + B/2),
           per-locus dosage variance 2 E[p_j q_j | asc] within deme plus the
           between-deme dosage-mean variance B = 4 E[(p_j - pbar_w)^2 | asc]
           entering the pooled standardization.  Tables from stress_asc2.json
           (ascertained degree-2 moments through the exact S1/S2 histories);
           graded only if that file exists, else emitted as null.
SECOND CORRECTION, SAME RUN: grade2 computed every metric on ALL rows,
  including the train-deme-fit rows the P+T weights were fitted on -- an
  overfit-inflated anchor r2_t.  The blind gates' frozen metric rule
  (gate4_grade.py:47, from the data files' own metric_rule field) is
  *-deme-test rows only; v3 applies it.  P1 is therefore re-graded under the
  corrected rule, not re-emitted.
BARS: unchanged form (|mean resid| <= 3 sems per case x pheno).
"""
import json, glob, math, os
import numpy as np
import pandas as pd
from statistics import NormalDist

TO = "/projects/standard/hsiehph/sauer354/theory-out"
PRED = json.load(open(f"{TO}/stress_predict.json"))
ASC = json.load(open(f"{TO}/stress_asc2.json")) if os.path.exists(f"{TO}/stress_asc2.json") else None
PHENOS = ["phenoC", "phenoA"]
ND = NormalDist()

def law_tables(case):
    op = PRED[case]["op"]
    H = op["H"]; wins = op["windows"]
    def g(tab, i, j): return tab.get(f"{i}_{j}", tab.get(f"{j}_{i}"))
    D = max(int(k.split("_")[1]) for k in H) + 1
    ratio = {}
    for t in range(D):
        sum_tt = sum(g(w,t,t) for w in wins)
        for j in range(D):
            if j == t: ratio[(t,j)] = 1.0; continue
            sum_tj = sum(g(w,t,j) for w in wins)
            ratio[(t,j)] = (sum_tj/sum_tt)**2 * (g(H,t,t)/g(H,j,j))**2
    return ratio, D

def theory_vj(case, nsz):
    if ASC is None or case not in ASC: return None
    a = ASC[case]
    m1 = {int(k): v for k, v in a["m1"].items()}
    pp = {}
    for k, v in a["pp"].items():
        i, j = (int(x) for x in k.split("_"))
        pp[(i,j)] = pp[(j,i)] = v
    demes = sorted(m1)
    wtot = sum(nsz.get(k, 0) for k in demes)
    if wtot == 0: return None
    w = {k: nsz.get(k, 0)/wtot for k in demes}
    # per unit beta^2 per locus: within-deme dosage variance 2 E[p_k q_k | asc]
    within = {k: 2.0*m1[k] for k in demes}
    # between: 4 * E[(p_k - pbar_w)^2 | asc], pbar_w = sum_l w_l p_l
    Epp_bar = {k: sum(w[l]*pp[(k,l)] for l in demes) for k in demes}
    Ebarbar = sum(w[l]*w[m]*pp[(l,m)] for l in demes for m in demes)
    B = 4.0*sum(w[k]*(pp[(k,k)] - 2.0*Epp_bar[k] + Ebarbar) for k in demes)
    pool = sum(w[k]*within[k] for k in demes) + B
    return {k: within[k]/pool for k in demes}

def auc_mw(score, y):
    s1, s0 = score[y==1], score[y==0]
    if len(s1)==0 or len(s0)==0: return None
    order = np.concatenate([s0,s1]).argsort().argsort()
    return float((order[len(s0):]+1).sum() - len(s1)*(len(s1)+1)/2)/(len(s0)*len(s1))

def chart_auc(r2_abs, K):
    rr = math.sqrt(max(min(r2_abs,0.999),0.0)); T = ND.inv_cdf(1-K)
    xs = np.linspace(-8,8,2001); ph = np.exp(-xs**2/2)/math.sqrt(2*math.pi)
    sig = math.sqrt(max(1-rr**2,1e-12))
    pc = np.array([ND.cdf((rr*x-T)/sig) for x in xs])
    Kh = np.trapezoid(ph*pc, xs)
    if Kh<=0 or Kh>=1: return None
    fc = ph*pc/Kh; f0 = ph*(1-pc)/(1-Kh)
    F0 = np.cumsum(f0)*(xs[1]-xs[0])
    return float(np.trapezoid(fc*F0, xs))

out = {"bars":{}}
for case in ("S1","S2"):
    R, D = law_tables(case)
    for pheno in PHENOS:
        res_v2, res_auc_m, res_auc_t, pairs = [], [], [], []
        for path in sorted(glob.glob(f"{TO}/stress_l3/{case}_{pheno}_realpt_stress*.csv")):
            seed = int(path.split("stress")[-1].split(".")[0])
            side = json.load(open(f"{TO}/stress_l3/{case}_realpt_stress{seed}.json"))
            t = side["train_deme"]
            df = pd.read_csv(path)
            # gate metric rule: *-deme-test rows only (gate4_grade.py:47)
            test = df[df["split"].astype(str).str.contains("test")]
            deme = test["deme"].to_numpy(); pgs = test["PGS_raw"].to_numpy()
            liab = test["true_liab"].to_numpy(); yb = test["y_binary"].to_numpy()
            r2 = {}; auc = {}; prev = {}; vmeas = {}
            for j in np.unique(deme).astype(int):
                m = deme==j
                r = np.corrcoef(pgs[m], liab[m])[0,1]
                r2[int(j)] = r*r
                auc[int(j)] = auc_mw(pgs[m], yb[m]); prev[int(j)] = float(yb[m].mean())
                vmeas[int(j)] = float(liab[m].var())
            # pooled-standardization weights = FULL per-deme sample counts (the
            # global standardize ran over all individuals), from the sidecar
            nsz = {int(j): (side["n_per_deme_train"] if int(j)==t else side["n_per_deme"])
                   for j in r2}
            vthy = theory_vj(case, nsz)
            if r2.get(t,0) <= 0: continue
            for j in r2:
                if j==t: continue
                pred = R[(t,j)]; meas = r2[j]/r2[t]
                res_v2.append(meas-pred); pairs.append((pred,meas))
                if auc.get(j) is not None and 0.01 < prev.get(j,0) < 0.99:
                    h2m = vmeas[j]/(vmeas[j]+1.0)
                    pa = chart_auc(pred*r2[t]*h2m, prev[j])
                    if pa is not None: res_auc_m.append(auc[j]-pa)
                    if vthy is not None and j in vthy:
                        h2t = vthy[j]/(vthy[j]+1.0)
                        pt2 = chart_auc(pred*r2[t]*h2t, prev[j])
                        if pt2 is not None: res_auc_t.append(auc[j]-pt2)
        def bar(res):
            res = np.array(res); n = len(res)
            if n < 2: return {"n": n, "mean": None, "sem": None, "pass": None}
            sem = res.std(ddof=1)/math.sqrt(n)
            return {"n": n, "mean": float(res.mean()), "sem": float(sem),
                    "pass": bool(abs(res.mean())<=3*sem)}
        pr = np.array(pairs)
        b = {"ratio": bar(res_v2),
             "pred_meas_corr": float(np.corrcoef(pr[:,0],pr[:,1])[0,1]) if len(pr)>2 else None,
             "auc_h2meas": bar(res_auc_m),
             "auc_h2theory": bar(res_auc_t) if res_auc_t else None}
        out["bars"][f"{case}_{pheno}"] = b
json.dump(out, open(f"{TO}/stress_l3_grade3.json","w"), indent=1)
print(json.dumps(out["bars"], indent=1))

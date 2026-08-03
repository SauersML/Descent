"""T4b: does the true mean ancestry-tract length depend on r_total at all?
   T8b: neutralDriftR2Ratio with genotype noise removed (exact R2 given the
        drifted frequencies), averaged over many Balding-Nichols replicates.
"""
import math, random, statistics, sys
sys.path.insert(0,'.')
import battery as B
R = B.R

def t4b():
    for morgans in (1.0, 4.0, 16.0):
        L = B.sim_tracts(0.5, 10, morgans, pop=300, chrom_reps=300)
        m, sd, se = B.mean_sd(L)
        print(f"T4b morgans={morgans:5} n={len(L):6} mc_mean={m:.5f} +-{se:.5f}"
              f"  standard(1/(g(1-a)))={1/(10*0.5):.5f}"
              f"  lean(1/(g*rtot))={1/(10*morgans):.5f}")

def t8b():
    V_A, V_E = 0.4, 0.6
    for M in (400, 20000):
        for fst in (0.02, 0.05, 0.1, 0.2):
            p0 = [R.uniform(0.05,0.95) for _ in range(M)]
            raw = [R.gauss(0,1) for _ in range(M)]
            vs = sum(r*r*2*p*(1-p) for r,p in zip(raw,p0))
            beta = [r*math.sqrt(V_A/vs) for r in raw]
            VS = sum(b*b*2*p*(1-p) for b,p in zip(beta,p0))
            r2s = VS/(VS+V_E)
            a = (1-fst)/fst
            ratios=[]
            for _ in range(40):
                pT = [B.beta_sample(a*p, a*(1-p)) for p in p0]
                VT = sum(b*b*2*p*(1-p) for b,p in zip(beta,pT))
                ratios.append((VT/(VT+V_E))/r2s)
            m,sd,se = B.mean_sd(ratios)
            lean = B.lean_neutralDriftR2Ratio(V_A,V_E,fst)
            print(f"T8b M={M:6} fst={fst:5} mean_ratio={m:.5f} +-{se:.5f} "
                  f"min={min(ratios):.5f} lean={lean:.5f} floor(1-fst)={1-fst:.4f} "
                  f"lean_rel_err={(lean-m)/m:+.4f} "
                  f"floor_violated={sum(1 for r in ratios if r < 1-fst)}/40")

t4b(); t8b()

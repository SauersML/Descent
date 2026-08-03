#!/usr/bin/env /usr/bin/python3.12
"""Differential test: Calibrator drift/demography defs vs direct Wright-Fisher simulation.

Pure stdlib (cluster python3.12 has no numpy/sympy).  All allele frequencies are
exact rationals c/(2N) with integer numerator c, so every quantity that DECIDES a
comparison is computed in fractions.Fraction, never a float.

Sims:
  A  ctrl      neutralDriftR2Ratio  (positive control; shared_ld = 1)
  B  tagged    taggedDriftR2Ratio   (two-locus causal+tag haplotype WF)
  C  bench     DriftRegime.benchmarkRatio / benchmarkRatioSquared
  D  regime    closedPopulation vs mutation-drift heterozygosity trajectory
  E  flow      AncestrySpecificArchitecture.geneFlowFstStep, island model
"""
import json, random, sys, math
from fractions import Fraction as F

# ---------------------------------------------------------------- WF machinery

def wf_step(c, twoN):
    """One Wright-Fisher generation on a biallelic locus: c derived allele copies
    out of twoN.  Returns new count."""
    return random.binomialvariate(twoN, c / twoN)

def wf_step_mut(c, twoN, mu):
    """WF with symmetric two-way mutation at rate mu applied to the gamete pool."""
    p = c / twoN
    p = p * (1.0 - mu) + (1.0 - p) * mu
    return random.binomialvariate(twoN, p)

def wf_step_hap(cnt, twoN):
    """One WF generation on 4 haplotypes (counts list of len 4) via 3 binomials."""
    out = [0, 0, 0, 0]
    rem = twoN
    tot = twoN
    for i in range(3):
        if rem == 0:
            break
        pi = cnt[i] / tot
        # conditional binomial given the remaining draws
        denom = 1.0 - sum(cnt[j] for j in range(i)) / tot
        if denom <= 0.0:
            break
        q = min(1.0, max(0.0, pi / denom))
        k = random.binomialvariate(rem, q)
        out[i] = k
        rem -= k
    out[3] = rem
    return out

# ------------------------------------------------------- exact moment helpers
# het numerator: 2*p*(1-p) with p=c/twoN  ->  2*c*(twoN-c) / twoN^2

def het_frac(c, twoN):
    return F(2 * c * (twoN - c), twoN * twoN)


# ================================================== A. neutralDriftR2Ratio ctrl

def sim_ctrl(L, twoN_anc, twoN_s, twoN_t, t, reps, h2_num, h2_den, seed, mu=0.0,
             t_s=None, t_t=None):
    """Two branches from a common ancestor, score = the causal variants themselves
    (perfect tagging).  Compares the exact simulated R2 ratio against
    neutralDriftR2Ratio fed (i) the PGS-weighted heterozygosity loss and
    (ii) a Hudson pairwise F_ST, the number a practitioner would supply."""
    random.seed(seed)
    rows = []
    for r in range(reps):
        # ancestral: uniform freqs, then one WF generation of ancestral sampling
        anc = [random.randrange(1, twoN_anc) for _ in range(L)]
        b2 = [random.randrange(1, 11) ** 2 for _ in range(L)]   # b_j^2, integers
        cs = [max(0, min(twoN_s, round(c * twoN_s / twoN_anc))) for c in anc]
        ct = [max(0, min(twoN_t, round(c * twoN_t / twoN_anc))) for c in anc]
        ts = t if t_s is None else t_s
        tt = t if t_t is None else t_t
        for _ in range(ts):
            cs = [wf_step_mut(c, twoN_s, mu) if mu else wf_step(c, twoN_s) for c in cs]
        for _ in range(tt):
            ct = [wf_step_mut(c, twoN_t, mu) if mu else wf_step(c, twoN_t) for c in ct]
        # exact PGS variances  V = sum b^2 * 2p(1-p)
        VS = sum(F(b * 2 * c * (twoN_s - c), twoN_s * twoN_s) for b, c in zip(b2, cs))
        VT = sum(F(b * 2 * c * (twoN_t - c), twoN_t * twoN_t) for b, c in zip(b2, ct))
        if VS == 0:
            continue
        # V_E chosen so source h2 = h2_num/h2_den  ->  V_E = VS*(den-num)/num
        VE = VS * F(h2_den - h2_num, h2_num)
        R2S = VS / (VS + VE)
        R2T = VT / (VT + VE)
        obs = R2T / R2S
        # measured fst, definition 1: PGS-weighted heterozygosity loss S->T
        fst_pgs = 1 - VT / VS
        # measured fst, definition 2: Hudson pairwise F_ST (exact, no sampling term)
        num = F(0); den = F(0)
        for c1, c2 in zip(cs, ct):
            p1 = F(c1, twoN_s); p2 = F(c2, twoN_t)
            num += (p1 - p2) ** 2
            den += p1 * (1 - p2) + p2 * (1 - p1)
        fst_hud = num / den if den else F(0)
        # Lean: neutralDriftR2Ratio V_A V_E fst = (1-f)(VA+VE)/((1-f)VA+VE)
        def lean(f):
            return (1 - f) * (VS + VE) / ((1 - f) * VS + VE)
        rows.append(dict(rep=r,
                         obs=float(obs),
                         fst_pgs=float(fst_pgs), fst_hudson=float(fst_hud),
                         lean_at_fst_pgs=float(lean(fst_pgs)),
                         lean_at_fst_hudson=float(lean(fst_hud)),
                         err_pgs=float(lean(fst_pgs) / obs - 1),
                         err_hudson=float(lean(fst_hud) / obs - 1),
                         floor_1mfst=float(1 - fst_pgs),
                         floor_violated=bool(obs < 1 - fst_pgs)))
    return rows


# ==================================================== B. taggedDriftR2Ratio

def sim_tagged(L, twoN, t_s, t_t, reps, h2_num, h2_den, seed, rho_min=0.5):
    """Causal locus C + tag locus M per block, 4-haplotype WF on two branches.
    Score is the SOURCE marginal-regression score on the tags; evaluated exactly
    (no genotype sampling) in both populations."""
    random.seed(seed)
    rows = []
    for r in range(reps):
        anc = []
        bs = []
        for _ in range(L):
            pC = random.uniform(0.1, 0.9)
            pM = random.uniform(0.1, 0.9)
            rho = random.uniform(rho_min, 0.98)
            Dmax = min(pC * (1 - pM), pM * (1 - pC))
            Dmin = -min(pC * pM, (1 - pC) * (1 - pM))
            D = rho * math.sqrt(pC * (1 - pC) * pM * (1 - pM))
            D = max(Dmin * 0.999, min(Dmax * 0.999, D))
            # haplotype freqs (C,M): 11,10,01,00
            f11 = pC * pM + D
            f10 = pC * (1 - pM) - D
            f01 = (1 - pC) * pM - D
            f00 = (1 - pC) * (1 - pM) + D
            fr = [f11, f10, f01, f00]
            if min(fr) <= 0:
                fr = [max(1e-6, x) for x in fr]
                s = sum(fr); fr = [x / s for x in fr]
            cnt = wf_step_hap([int(round(x * twoN)) for x in fr], twoN)
            anc.append(cnt)
            bs.append(random.randrange(1, 11))
        src = [list(c) for c in anc]
        tgt = [list(c) for c in anc]
        for _ in range(t_s):
            src = [wf_step_hap(c, twoN) for c in src]
        for _ in range(t_t):
            tgt = [wf_step_hap(c, twoN) for c in tgt]

        def moments(cnt):
            n11, n10, n01, n00 = cnt
            pC = F(n11 + n10, twoN); pM = F(n11 + n01, twoN)
            D = F(n11, twoN) - pC * pM
            return pC, pM, D

        VarS_score = F(0); VarT_score = F(0)
        CovS = F(0); CovT = F(0)
        VgS = F(0); VgT = F(0)
        nblk = 0
        for b, cS, cT in zip(bs, src, tgt):
            pCS, pMS, DS = moments(cS)
            pCT, pMT, DT = moments(cT)
            hMS = 2 * pMS * (1 - pMS); hMT = 2 * pMT * (1 - pMT)
            if hMS == 0:
                continue            # tag fixed in source: no weight estimable
            nblk += 1
            beta = b * 2 * DS / hMS          # source marginal OLS coefficient
            VarS_score += beta * beta * hMS
            VarT_score += beta * beta * hMT
            CovS += beta * b * 2 * DS
            CovT += beta * b * 2 * DT
            VgS += b * b * 2 * pCS * (1 - pCS)
            VgT += b * b * 2 * pCT * (1 - pCT)
        if VarS_score == 0 or VarT_score == 0 or VgS == 0:
            continue
        VE = VgS * F(h2_den - h2_num, h2_num)     # source h2 = num/den
        R2S = CovS * CovS / (VarS_score * (VgS + VE))
        R2T = CovT * CovT / (VarT_score * (VgT + VE))
        if R2S == 0:
            continue
        obs = R2T / R2S
        # --- what the corpus would measure ---
        # explained variance of the score in each population
        ExS = CovS * CovS / VarS_score
        ExT = CovT * CovT / VarT_score
        k_true = ExT / ExS                      # total signal retention
        fst_drift = 1 - VgT / VgS               # causal-locus heterozygosity loss
        shared_ld = k_true / (1 - fst_drift) if fst_drift != 1 else F(0)
        # Lean prediction with the SAME retention factor k = (1-fst)*shared_ld
        VA = VgS
        lean = (k_true * VA / (k_true * VA + VE)) / (VA / (VA + VE))
        # the correct closed form: obs = k * Var_S(y) / Var_T(y)
        correct = k_true * (VgS + VE) / (VgT + VE)
        rows.append(dict(rep=r, nblk=nblk,
                         obs=float(obs), lean=float(lean), correct=float(correct),
                         err=float(lean / obs - 1),
                         err_correct=float(correct / obs - 1),
                         k_true=float(k_true), fst_drift=float(fst_drift),
                         shared_ld=float(shared_ld),
                         h2_target=float(VgT / (VgT + VE)),
                         bound_retention=float((1 - fst_drift) * shared_ld),
                         bound_holds=bool((1 - fst_drift) * shared_ld <= obs),
                         cap_claim=float(obs / (1 - fst_drift)),
                         cap_holds=bool(shared_ld <= obs / (1 - fst_drift))))
    return rows


# ============================================ C. benchmarkRatio (DriftRegime)

def sim_bench(L, twoN_a, twoN_b, t, reps, seed, mu=0.0):
    """Two branches with (possibly) asymmetric Ne from a common ancestor.
    Measures: het_B/het_A, branch drift coefficients F_i = 1 - H_i/H_anc, and the
    Hudson pairwise F_ST; then evaluates (1-fstT)/(1-fstS) under each reading."""
    random.seed(seed)
    rows = []
    for r in range(reps):
        anc = [random.randrange(1, 1000) for _ in range(L)]
        AN = 1000
        Hanc = sum(het_frac(c, AN) for c in anc)
        ca = [max(0, min(twoN_a, round(c * twoN_a / AN))) for c in anc]
        cb = [max(0, min(twoN_b, round(c * twoN_b / AN))) for c in anc]
        Hanc = sum(het_frac(c, twoN_a) for c in ca)   # rebase on branch A start
        HancB = sum(het_frac(c, twoN_b) for c in cb)
        for _ in range(t):
            if mu:
                ca = [wf_step_mut(c, twoN_a, mu) for c in ca]
                cb = [wf_step_mut(c, twoN_b, mu) for c in cb]
            else:
                ca = [wf_step(c, twoN_a) for c in ca]
                cb = [wf_step(c, twoN_b) for c in cb]
        HA = sum(het_frac(c, twoN_a) for c in ca)
        HB = sum(het_frac(c, twoN_b) for c in cb)
        num = F(0); den = F(0)
        for c1, c2 in zip(ca, cb):
            p1 = F(c1, twoN_a); p2 = F(c2, twoN_b)
            num += (p1 - p2) ** 2
            den += p1 * (1 - p2) + p2 * (1 - p1)
        fst_hud = num / den if den else F(0)
        fA = 1 - HA / Hanc          # branch drift coefficient, A = "source"
        fB = 1 - HB / HancB         # branch drift coefficient, B = "target"
        het_ratio = HB / HA
        rows.append(dict(rep=r,
                         het_ratio=float(het_ratio),
                         fA_branch=float(fA), fB_branch=float(fB),
                         fst_hudson=float(fst_hud),
                         bench_branch=float((1 - fB) / (1 - fA)),
                         bench_sq_branch=float(((1 - fB) / (1 - fA)) ** 2),
                         bench_hudson_sym=float((1 - fst_hud) / (1 - fst_hud)),
                         err_branch=float((1 - fB) / (1 - fA) / het_ratio - 1),
                         err_sq_branch=float(((1 - fB) / (1 - fA)) ** 2 / het_ratio - 1)))
    return rows


# =================================== D. heterozygosity regimes (DriftRegime)

def sim_regime(L, twoN, t, reps, mus, seed):
    """Measured retention H_t/H_0 under drift alone and under mutation-drift,
    against closedPopulation's (1-1/(2Ne))^t and hetMutationFloor's theta/(1+theta)."""
    random.seed(seed)
    out = []
    Ne = twoN / 2
    for mu in mus:
        rets = []
        for r in range(reps):
            c = [random.randrange(1, twoN) for _ in range(L)]
            H0 = sum(het_frac(x, twoN) for x in c)
            for _ in range(t):
                c = [wf_step_mut(x, twoN, mu) if mu else wf_step(x, twoN) for x in c]
            Ht = sum(het_frac(x, twoN) for x in c)
            rets.append(float(Ht / H0))
        m = sum(rets) / len(rets)
        sd = (sum((x - m) ** 2 for x in rets) / max(1, len(rets) - 1)) ** 0.5
        theta = 4 * Ne * mu
        out.append(dict(mu=mu, Ne=Ne, t=t, reps=reps,
                        measured_retention=m, se=sd / len(rets) ** 0.5,
                        closedPopulation_pred=(1 - 1 / (2 * Ne)) ** t,
                        hetMutationFloor=theta / (1 + theta) if mu else 0.0))
    return out


# ============================== E. geneFlowFstStep / island migration-drift

def sim_flow(L, twoN, m, t, reps, seed, npop=2):
    """Island model: npop demes of size twoN/2, migration rate m per generation.
    Measures equilibrium F_ST against 1/(1+4 Ne m) and checks the linearised
    one-generation map ibdFlowStep against the realised step."""
    random.seed(seed)
    traj = []
    for r in range(reps):
        pops = [[random.randrange(1, twoN) for _ in range(L)] for _ in range(npop)]
        # start every deme identical -> F_ST 0
        pops = [list(pops[0]) for _ in range(npop)]
        series = []
        for gen in range(t):
            # migration: each deme's gamete pool receives fraction m from the mean
            freqs = [[c / twoN for c in P] for P in pops]
            mean = [sum(freqs[k][j] for k in range(npop)) / npop for j in range(L)]
            new = []
            for k in range(npop):
                pk = [(1 - m) * freqs[k][j] + m * mean[j] for j in range(L)]
                new.append([random.binomialvariate(twoN, min(1.0, max(0.0, x))) for x in pk])
            pops = new
            if gen % max(1, t // 20) == 0 or gen == t - 1:
                num = F(0); den = F(0)
                for j in range(L):
                    ps = [F(pops[k][j], twoN) for k in range(npop)]
                    for a in range(npop):
                        for bq in range(a + 1, npop):
                            p1, p2 = ps[a], ps[bq]
                            num += (p1 - p2) ** 2
                            den += p1 * (1 - p2) + p2 * (1 - p1)
                series.append((gen, float(num / den) if den else 0.0))
        traj.append(series)
    # average across reps
    gens = [g for g, _ in traj[0]]
    avg = [sum(traj[r][i][1] for r in range(len(traj))) / len(traj) for i in range(len(gens))]
    Ne = twoN / 2
    return dict(m=m, Ne=Ne, twoN=twoN, npop=npop, L=L, reps=reps,
                gens=gens, fst=avg,
                fst_final=avg[-1],
                pred_1_over_1p4Nm=1.0 / (1.0 + 4 * Ne * m),
                pred_island_corrected=1.0 / (1.0 + 4 * Ne * m * (npop / (npop - 1.0)) ** 2))


# ------------------------------------------------------------------- driver
if __name__ == "__main__":
    what = sys.argv[1]
    cfg = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
    fn = dict(ctrl=sim_ctrl, tagged=sim_tagged, bench=sim_bench,
              regime=sim_regime, flow=sim_flow)[what]
    print(json.dumps(dict(sim=what, cfg=cfg, out=fn(**cfg))))

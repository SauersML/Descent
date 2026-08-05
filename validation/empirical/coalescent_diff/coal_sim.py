#!/usr/bin/env python3
"""Direct coalescent / Wright-Fisher simulation of the gnomon popgen core.

PURE STDLIB.  No numpy, no sympy.  /usr/bin/python3.12 on MSI.

Every quantity here is measured from a SIMULATED PROCESS -- gene copies with
labels, resampled generation by generation -- never from a second closed form.
That is the point: a formula-vs-formula check cannot catch a shared
misconception, and three of the targets below are places where the corpus took
a standard closed form and attached it to a different quantity.

POSITIVE CONTROLS, each run BEFORE the test it licenses:

  P1  Single WF population, infinite alleles.  Equilibrium probability that two
      distinct gene copies are identical is exactly 1/(1+theta), theta=4*Ne*mu.
      This is the textbook mutation-drift identity and it is EXACT (not an
      approximation) for the model simulated.  It licenses the whole SIM1/SIM2
      identity machinery: if the engine cannot reproduce 1/(1+theta) in one
      population, nothing it says about two populations means anything.

  P2  Pure drift, no mutation: within-population identity must follow
      Q(t+1) = 1/(2Ne) + (1-1/(2Ne)) Q(t) exactly.  Licenses the resampler.

  P3  Stepping stone: expected time for two lineages d demes apart on a circle
      of D demes to first share a deme must equal d(D-d)/(2 sigma^2 m).
      Licenses SIM5's walk, AND is itself the reference the corpus's
      steppingStoneMeetingTimeOnLattice asserts.

  P4  Admixture LD: if the two source populations have the same allele
      frequency at either locus, admixture LD must be zero.

WHAT EACH SIM DECIDES

  SIM1  Descent.PopulationGeneticsFoundations.fstMutationDriftTransient
        Fst(t) = [1/(1+theta)] (1 - exp(-(1+theta) t/(2Ne)))
        Two isolated demes, infinite alleles, measured Fst = (Qs-Qb)/(1-Qb).
        Run under BOTH initial conditions, because the corpus docstring
        ("starting from Fst=0") does not say which:
          A. ancestor at mutation-drift equilibrium  (the standard split)
          B. ancestor with zero identity (infinitely diverse)
        The Lean's rate constant (1+theta)/(2Ne) = 2mu + 1/(2Ne) is the
        relaxation rate of the WITHIN-deme identity Qs.  The approach of Fst
        under (A) is governed instead by the decay of the BETWEEN-deme identity
        Qb, whose only clock is mutation: rate 2mu = theta/(2Ne).  Those differ
        by a factor (1+theta)/theta, which diverges as theta -> 0.

  SIM2  Descent.PopulationGeneticsFoundations.fstMigrationMutationEquilibrium
        1/(1 + 4 Ne m + 4 Ne mu).  n-deme island model with infinite-alleles
        mutation, equilibrium Fst measured by time-averaging.

  SIM3  Descent.LDDecayTheory.admixtureLD  and
        Descent.DemographicHistory.admixedAlleleFreq
        alpha(1-alpha) dp1 dp2 -- measured from simulated admixed haplotypes.

  SIM4  Descent.PopulationGeneticsFoundations.expectedNewMutations and
        sharedLDFractionFromMutation.  Infinite-sites WF: how many mutations
        ARISE per generation (theta/2, the docstring's first claim) versus how
        many are SEGREGATING after t generations (the docstring's second claim,
        "~theta t/2").

  SIM5  Descent.DemographicHistory.demoSteppingStoneFst d/(d+4 Ne m s2),
        and Descent.DemographicHistory.steppingStoneMeetingTimeOnLattice
        d(D-d)/(2 s2 m), and steppingStoneDiffusionTimescale d/(2 s2 m).
        Direct Monte Carlo of the two-lineage stepping-stone coalescent on a
        circle: lineages walk, coalesce with probability 1/(2Ne) when
        co-located.  Nothing is solved; the process is run.
"""

import json
import math
import os
import random
import sys
from collections import Counter
from multiprocessing import Pool

NCORE = int(os.environ.get("COAL_NCORE", "16"))
SEED0 = 20260803


# --------------------------------------------------------------------------
# identity helpers
# --------------------------------------------------------------------------
def q_within(labels):
    """P(two DISTINCT gene copies drawn from `labels` carry the same allele)."""
    g = len(labels)
    if g < 2:
        return 0.0
    c = Counter(labels)
    s = sum(n * (n - 1) for n in c.values())
    return s / (g * (g - 1))


def q_between(l1, l2):
    """P(one copy from each of two demes carries the same allele)."""
    c1 = Counter(l1)
    c2 = Counter(l2)
    if len(c1) > len(c2):
        c1, c2 = c2, c1
    s = sum(n * c2.get(k, 0) for k, n in c1.items())
    return s / (len(l1) * len(l2))


def fst_hudson(qs, qb):
    """Fst = (Qs - Qb)/(1 - Qb).  The identity-probability form; equivalently
    1 - Hs/Hb with H = 1 - Q.  This is the form whose isolated-demes limit is
    Qs, hence 1/(1+theta), which is what fstMutationDriftEquilibrium says."""
    if 1.0 - qb == 0.0:
        return float("nan")
    return (qs - qb) / (1.0 - qb)


def wf_step(labels, rng, mu, ctr):
    """One WF generation, infinite alleles.  ctr is a 1-element list used as a
    shared new-allele counter so labels are globally unique."""
    g = len(labels)
    rr = rng.randrange
    rf = rng.random
    out = [labels[rr(g)] for _ in range(g)]
    if mu > 0.0:
        for i in range(g):
            if rf() < mu:
                ctr[0] += 1
                out[i] = ctr[0]
    return out


# --------------------------------------------------------------------------
# P1 / P2  positive controls
# --------------------------------------------------------------------------
def _p1_rep(args):
    ne, mu, burn, samp, seed = args
    rng = random.Random(seed)
    g = 2 * ne
    ctr = [g]
    pop = list(range(g))
    for _ in range(burn):
        pop = wf_step(pop, rng, mu, ctr)
    acc = 0.0
    n = 0
    for t in range(samp):
        pop = wf_step(pop, rng, mu, ctr)
        if t % 5 == 0:
            acc += q_within(pop)
            n += 1
    return acc / n


def control_p1(pool):
    """Reference is the EXACT discrete-time fixed point of the identity
    recursion Q' = (1-mu)^2 [1/(2Ne) + (1-1/(2Ne)) Q], not its diffusion limit
    1/(1+theta).  Both are reported; the exact one is what the simulated
    process must reproduce, and the gap between them is the size of the
    diffusion approximation at these parameters."""
    rows = []
    for theta in (0.25, 1.0, 4.0):
        ne = 100
        mu = theta / (4.0 * ne)
        jobs = [(ne, mu, 20 * ne, 20000, SEED0 + 7919 * k + int(theta * 13))
                for k in range(NCORE * 2)]
        vals = pool.map(_p1_rep, jobs)
        meas = sum(vals) / len(vals)
        a = 1.0 / (2.0 * ne)
        k2 = (1.0 - mu) ** 2
        exact = k2 * a / (1.0 - k2 * (1.0 - a))
        pred = 1.0 / (1.0 + theta)
        rows.append({"theta": theta, "Ne": ne, "measured_Q": meas,
                     "exact_discrete_fixed_point": exact,
                     "diffusion_1_over_1_plus_theta": pred,
                     "rel_err": (meas - exact) / exact,
                     "n_rep": len(vals)})
        print("  P1 theta=%-5.2f  Q measured %.5f  exact discrete %.5f  rel "
              "%+.4f   [diffusion 1/(1+theta) %.5f]"
              % (theta, meas, exact, (meas - exact) / exact, pred), flush=True)
    ok = all(abs(r["rel_err"]) < 0.02 for r in rows)
    return {"rows": rows, "pass": ok}


def _p2_rep(args):
    ne, gens, seed = args
    rng = random.Random(seed)
    g = 2 * ne
    ctr = [g]
    pop = list(range(g))
    traj = [q_within(pop)]
    for _ in range(gens):
        pop = wf_step(pop, rng, 0.0, ctr)
        traj.append(q_within(pop))
    return traj


def control_p2(pool):
    ne, gens = 50, 200
    jobs = [(ne, gens, SEED0 + 104729 * k) for k in range(NCORE * 50)]
    trajs = pool.map(_p2_rep, jobs)
    m = len(trajs)
    mean = [sum(tr[t] for tr in trajs) / m for t in range(gens + 1)]
    a = 1.0 / (2.0 * ne)
    pred = [1.0 - (1.0 - a) ** t for t in range(gens + 1)]
    errs = [abs(mean[t] - pred[t]) for t in range(1, gens + 1)]
    worst = max(errs)
    print("  P2 pure drift Ne=%d: worst |Q_meas - (1-(1-1/2Ne)^t)| = %.5f over "
          "%d gens, %d reps" % (ne, worst, gens, m), flush=True)
    return {"Ne": ne, "gens": gens, "n_rep": m, "worst_abs_dev": worst,
            "measured_at": {str(t): mean[t] for t in (10, 50, 100, 200)},
            "predicted_at": {str(t): pred[t] for t in (10, 50, 100, 200)},
            "pass": worst < 0.02}


# --------------------------------------------------------------------------
# SIM1  fstMutationDriftTransient
# --------------------------------------------------------------------------
def _sim1_rep(args):
    ne, mu, gens, init, step, seed = args
    rng = random.Random(seed)
    g = 2 * ne
    ctr = [g]
    anc = list(range(g))
    if init == "equilibrium":
        for _ in range(10 * ne):
            anc = wf_step(anc, rng, mu, ctr)
    d1 = list(anc)
    d2 = list(anc)
    out = []
    for t in range(gens + 1):
        if t % step == 0:
            out.append((q_within(d1), q_within(d2), q_between(d1, d2)))
        d1 = wf_step(d1, rng, mu, ctr)
        d2 = wf_step(d2, rng, mu, ctr)
    return out


def lean_fst_transient(theta, t, ne):
    return (1.0 / (1.0 + theta)) * (1.0 - math.exp(-(1.0 + theta) * t / (2.0 * ne)))


def derived_fst_transient_equilibrium_split(theta, t, ne, mu):
    """Fst(t) for two demes split from an ancestor AT mutation-drift
    equilibrium, derived from the process rather than assumed.

    Each deme stays at its own equilibrium, so Qs(t) = Q* for all t.  Two genes
    in DIFFERENT demes can never coalesce after the split, so their identity is
    whatever it was at the split, surviving mutation on both lineages:
    Qb(t) = Q* (1-mu)^(2t).  Hence

        Fst(t) = (Q* - Qb)/(1 - Qb) = Q*(1 - x)/(1 - Q* x),  x = (1-mu)^(2t).

    The clock is 2*mu = theta/(2 Ne).  The corpus's exp(-(1+theta) t/(2 Ne))
    has clock (1+theta)/(2 Ne) -- the relaxation rate of the WITHIN-deme
    identity, not of Fst.  They differ by (1+theta)/theta.
    """
    a = 1.0 / (2.0 * ne)
    k2 = (1.0 - mu) ** 2
    qstar = k2 * a / (1.0 - k2 * (1.0 - a))
    x = (1.0 - mu) ** (2 * t)
    return qstar * (1.0 - x) / (1.0 - qstar * x)


def sim1(pool):
    cells = []
    for theta, gens, step in ((0.25, 4000, 100), (1.0, 1200, 40), (4.0, 600, 20)):
        ne = 100
        mu = theta / (4.0 * ne)
        for init in ("equilibrium", "zero_identity"):
            jobs = [(ne, mu, gens, init, step,
                     SEED0 + 31337 * k + int(theta * 101) + (0 if init[0] == "e" else 555))
                    for k in range(NCORE * 20)]
            reps = pool.map(_sim1_rep, jobs)
            npt = len(reps[0])
            m = len(reps)
            traj = []
            for i in range(npt):
                t = i * step
                qs = sum((r[i][0] + r[i][1]) / 2.0 for r in reps) / m
                qb = sum(r[i][2] for r in reps) / m
                f = fst_hudson(qs, qb)
                traj.append({"t": t, "Qs": qs, "Qb": qb, "fst_measured": f,
                             "fst_lean": lean_fst_transient(theta, t, ne),
                             "fst_derived_equilibrium_split":
                                 derived_fst_transient_equilibrium_split(theta, t, ne, mu)})
            # worst relative disagreement over the interior of the trajectory
            worst = 0.0
            worst_t = None
            worst_der = 0.0
            for p in traj:
                if p["t"] == 0:
                    continue
                a, b = p["fst_lean"], p["fst_measured"]
                if b <= 1e-6:
                    continue
                e = (a - b) / b
                if abs(e) > abs(worst):
                    worst, worst_t = e, p["t"]
                e2 = (p["fst_derived_equilibrium_split"] - b) / b
                if abs(e2) > abs(worst_der):
                    worst_der = e2
            cells.append({"theta": theta, "Ne": ne, "mu": mu, "init": init,
                          "n_rep": m, "gens": gens,
                          "worst_rel_err_lean_vs_measured": worst,
                          "worst_at_t": worst_t,
                          "worst_rel_err_derived_vs_measured": worst_der,
                          "equilibrium_measured": traj[-1]["fst_measured"],
                          "equilibrium_1_over_1_plus_theta": 1.0 / (1.0 + theta),
                          "trajectory": traj})
            print("  SIM1 theta=%-5.2f init=%-14s LEAN worst rel err %+.3f at "
                  "t=%s | DERIVED-split worst rel err %+.3f | eq measured %.4f "
                  "vs 1/(1+theta) %.4f"
                  % (theta, init, worst, worst_t, worst_der,
                     traj[-1]["fst_measured"], 1.0 / (1.0 + theta)), flush=True)
    return cells


# --------------------------------------------------------------------------
# SIM2  fstMigrationMutationEquilibrium
# --------------------------------------------------------------------------
def _sim2_rep(args):
    ndeme, ne, m, mu, burn, samp, seed = args
    rng = random.Random(seed)
    g = 2 * ne
    ctr = [ndeme * g]
    demes = [list(range(i * g, (i + 1) * g)) for i in range(ndeme)]
    rr = rng.randrange
    rf = rng.random

    def gen(demes):
        new = []
        for i in range(ndeme):
            src = demes[i]
            out = []
            for _ in range(g):
                if rf() < m:
                    j = rr(ndeme)
                    out.append(demes[j][rr(g)])
                else:
                    out.append(src[rr(g)])
            if mu > 0.0:
                for k in range(g):
                    if rf() < mu:
                        ctr[0] += 1
                        out[k] = ctr[0]
            new.append(out)
        return new

    for _ in range(burn):
        demes = gen(demes)
    accs = 0.0
    accb = 0.0
    n = 0
    for t in range(samp):
        demes = gen(demes)
        if t % 10 == 0:
            qs = sum(q_within(d) for d in demes) / ndeme
            pairs = [(i, j) for i in range(ndeme) for j in range(i + 1, ndeme)]
            sel = pairs if len(pairs) <= 40 else [pairs[rr(len(pairs))] for _ in range(40)]
            qb = sum(q_between(demes[i], demes[j]) for i, j in sel) / len(sel)
            accs += qs
            accb += qb
            n += 1
    return accs / n, accb / n


def sim2(pool):
    ndeme, ne = 20, 25
    rows = []
    grid = [(0.0, 1.0), (1.0, 0.5), (1.0, 2.0), (4.0, 0.5), (0.25, 0.5)]
    for fourNm, theta in grid:
        m = fourNm / (4.0 * ne)
        mu = theta / (4.0 * ne)
        jobs = [(ndeme, ne, m, mu, 1500, 4000, SEED0 + 6151 * k + int(fourNm * 31 + theta * 7))
                for k in range(NCORE)]
        vals = pool.map(_sim2_rep, jobs)
        qs = sum(v[0] for v in vals) / len(vals)
        qb = sum(v[1] for v in vals) / len(vals)
        f = fst_hudson(qs, qb)
        lean = 1.0 / (1.0 + 4.0 * ne * m + 4.0 * ne * mu)
        # finite-island correction: a gene drawn from a uniformly random deme is
        # a true immigrant only with probability (n-1)/n, and Wright's finite-n
        # island result carries (n/(n-1))^2 on the migration term.
        m_eff = m * (ndeme - 1) / ndeme
        lean_corr = 1.0 / (1.0 + 4.0 * ne * m_eff * (ndeme / (ndeme - 1.0)) ** 2
                           + 4.0 * ne * mu)
        rows.append({"n_demes": ndeme, "Ne": ne, "4Nm": fourNm, "theta": theta,
                     "Qs": qs, "Qb": qb, "fst_measured": f,
                     "fst_lean": lean, "rel_err_lean": (lean - f) / f,
                     "fst_lean_finite_island_corrected": lean_corr,
                     "rel_err_corrected": (lean_corr - f) / f,
                     "n_rep": len(vals)})
        print("  SIM2 4Nm=%-5.2f theta=%-4.1f  measured %.4f  lean %.4f (%+.3f)"
              "  finite-n corrected %.4f (%+.3f)"
              % (fourNm, theta, f, lean, (lean - f) / f, lean_corr,
                 (lean_corr - f) / f), flush=True)
    return rows


# --------------------------------------------------------------------------
# SIM3  admixtureLD / admixedAlleleFreq
# --------------------------------------------------------------------------
def _sim3_rep(args):
    alpha, p1a, p1b, p2a, p2b, nhap, seed = args
    rng = random.Random(seed)
    rf = rng.random
    n11 = n1 = n2 = 0
    for _ in range(nhap):
        if rf() < alpha:
            a = 1 if rf() < p1a else 0
            b = 1 if rf() < p2a else 0
        else:
            a = 1 if rf() < p1b else 0
            b = 1 if rf() < p2b else 0
        n1 += a
        n2 += b
        n11 += a & b
    return n11 / nhap, n1 / nhap, n2 / nhap


def sim3(pool):
    rows = []
    grid = [
        (0.5, 0.8, 0.2, 0.7, 0.1, "test"),
        (0.2, 0.9, 0.1, 0.6, 0.2, "test"),
        (0.8, 0.3, 0.9, 0.5, 0.05, "test"),
        (0.5, 0.4, 0.4, 0.7, 0.1, "CONTROL P4: dp1 = 0"),
        (0.5, 0.8, 0.2, 0.3, 0.3, "CONTROL P4: dp2 = 0"),
    ]
    for alpha, p1a, p1b, p2a, p2b, tag in grid:
        jobs = [(alpha, p1a, p1b, p2a, p2b, 200000, SEED0 + 9973 * k + int(alpha * 977))
                for k in range(NCORE)]
        vals = pool.map(_sim3_rep, jobs)
        f11 = sum(v[0] for v in vals) / len(vals)
        f1 = sum(v[1] for v in vals) / len(vals)
        f2 = sum(v[2] for v in vals) / len(vals)
        d_meas = f11 - f1 * f2
        d_lean = alpha * (1 - alpha) * (p1a - p1b) * (p2a - p2b)
        p_lean = alpha * p1a + (1 - alpha) * p1b
        rows.append({"tag": tag, "alpha": alpha, "p1A": p1a, "p1B": p1b,
                     "p2A": p2a, "p2B": p2b,
                     "D_measured": d_meas, "D_lean_admixtureLD": d_lean,
                     "abs_err": d_meas - d_lean,
                     "rel_err": ((d_lean - d_meas) / d_meas) if abs(d_meas) > 1e-4 else None,
                     "p1_measured": f1, "p1_lean_admixedAlleleFreq": p_lean,
                     "p1_abs_err": f1 - p_lean,
                     "n_hap": 200000 * len(vals)})
        print("  SIM3 %-22s alpha=%.2f  D measured %+.5f  lean %+.5f  (abs err "
              "%+.5f);  p1 measured %.5f lean %.5f"
              % (tag, alpha, d_meas, d_lean, d_meas - d_lean, f1, p_lean), flush=True)
    return rows


# --------------------------------------------------------------------------
# SIM4  expectedNewMutations / sharedLDFractionFromMutation
# --------------------------------------------------------------------------
def _sim4_rep(args):
    """Infinite-sites WF.  Track counts of derived copies at each segregating
    site.  Report (mutations arisen, sites segregating) at each checkpoint."""
    ne, mu_site, gens, step, seed = args
    rng = random.Random(seed)
    g = 2 * ne
    sites = []          # list of derived-allele counts
    arisen = 0
    out = []
    for t in range(gens + 1):
        if t % step == 0:
            out.append((t, arisen, len(sites)))
        # drift: binomial resample of each site
        nxt = []
        for k in sites:
            p = k / g
            kk = 0
            for _ in range(g):
                if rng.random() < p:
                    kk += 1
            if 0 < kk < g:
                nxt.append(kk)
        # new mutations: Poisson(2*Ne*mu_site) per generation, each at count 1
        lam = g * mu_site
        nm = 0
        pk = math.exp(-lam)
        cum = pk
        u = rng.random()
        while u > cum and nm < 50:
            nm += 1
            pk *= lam / nm
            cum += pk
        arisen += nm
        nxt.extend([1] * nm)
        sites = nxt
    return out


def sim4(pool):
    ne = 50
    rows = []
    for theta in (1.0, 4.0):
        mu_site = theta / (4.0 * ne)
        gens, step = 1200, 100
        jobs = [(ne, mu_site, gens, step, SEED0 + 3571 * k + int(theta * 17))
                for k in range(NCORE)]
        reps = pool.map(_sim4_rep, jobs)
        m = len(reps)
        npt = len(reps[0])
        traj = []
        for i in range(npt):
            t = reps[0][i][0]
            ar = sum(r[i][1] for r in reps) / m
            sg = sum(r[i][2] for r in reps) / m
            traj.append({"t": t, "mutations_arisen": ar, "sites_segregating": sg,
                         "lean_expectedNewMutations_theta_t_over_2": theta * t / 2.0,
                         "lean_sharedLDFraction_exp": math.exp(-theta * t / 2.0)})
        last = traj[-1]
        rows.append({"theta": theta, "Ne": ne, "n_rep": m, "trajectory": traj,
                     "arisen_over_lean_at_end":
                         last["mutations_arisen"] / last["lean_expectedNewMutations_theta_t_over_2"],
                     "segregating_over_lean_at_end":
                         last["sites_segregating"] / last["lean_expectedNewMutations_theta_t_over_2"],
                     "watterson_equilibrium_theta_sum_1_over_i":
                         theta * sum(1.0 / i for i in range(1, 2 * ne))})
        print("  SIM4 theta=%.1f at t=%d: arisen %.1f (lean theta t/2 = %.1f, "
              "ratio %.3f);  SEGREGATING %.1f (ratio %.4f); Watterson eq %.1f"
              % (theta, last["t"], last["mutations_arisen"],
                 last["lean_expectedNewMutations_theta_t_over_2"],
                 last["mutations_arisen"] / last["lean_expectedNewMutations_theta_t_over_2"],
                 last["sites_segregating"],
                 last["sites_segregating"] / last["lean_expectedNewMutations_theta_t_over_2"],
                 theta * sum(1.0 / i for i in range(1, 2 * ne))), flush=True)
    return rows


# --------------------------------------------------------------------------
# SIM5  stepping stone: meeting time (P3) and Fst
# --------------------------------------------------------------------------
def _sim5_rep(args):
    """Two lineages on a circle of D demes, each migrating to a uniformly
    chosen neighbour with probability m per generation; when co-located they
    coalesce with probability 1/(2Ne).  Returns (meeting time, coalescence
    time) for each of `reps` replicates started at separation d."""
    ddeme, ne, m, d, reps, cap, seed = args
    rng = random.Random(seed)
    rf = rng.random
    coal_p = 1.0 / (2.0 * ne)
    met_sum = 0.0
    met_n = 0
    coal_sum = 0.0
    coal_n = 0
    censored = 0
    for _ in range(reps):
        x = 0
        y = d
        t = 0
        met = None
        while t < cap:
            if x == y:
                if met is None:
                    met = t
                if rf() < coal_p:
                    break
            if rf() < m:
                x = (x + (1 if rf() < 0.5 else -1)) % ddeme
            if rf() < m:
                y = (y + (1 if rf() < 0.5 else -1)) % ddeme
            t += 1
        if t >= cap:
            censored += 1
            continue
        if met is not None:
            met_sum += met
            met_n += 1
        coal_sum += t
        coal_n += 1
    return met_sum, met_n, coal_sum, coal_n, censored


def sim5(pool):
    ddeme, ne, m, s2 = 64, 25, 0.2, 1.0
    cap = 400000
    out = {"D": ddeme, "Ne": ne, "m": m, "sigma_sq": s2, "cap": cap}
    # CONTROL P3a: within-deme coalescence time.  Strobeck (1987): under any
    # conservative migration model the expected coalescence time for two genes
    # from the SAME deme is 2*N_total = 2*D*Ne, independent of m.  Note this is
    # NOT the per-deme 2*Ne that `coalFst` is handed; that substitution is the
    # second of the two compensating omissions the corpus documents.
    # CONTROL P3b: the meeting time itself, against d(D-d)/(2 sigma^2 m).
    rows = []
    for d in (0, 1, 2, 4, 8, 16, 32):
        reps = 3000 if d else 4000
        jobs = [(ddeme, ne, m, d, reps, cap, SEED0 + 1299709 * k + 71 * d)
                for k in range(NCORE)]
        vals = pool.map(_sim5_rep, jobs)
        met_sum = sum(v[0] for v in vals)
        met_n = sum(v[1] for v in vals)
        coal_sum = sum(v[2] for v in vals)
        coal_n = sum(v[3] for v in vals)
        cens = sum(v[4] for v in vals)
        meet = met_sum / met_n if met_n else float("nan")
        tcoal = coal_sum / coal_n if coal_n else float("nan")
        row = {"d": d, "n_rep": coal_n, "censored": cens,
               "meeting_time_measured": meet,
               "meeting_time_lean_onLattice": d * (ddeme - d) / (2.0 * s2 * m),
               "meeting_time_lean_perDeme_diffusionTimescale": d / (2.0 * s2 * m),
               "coal_time_measured": tcoal}
        rows.append(row)
        print("  SIM5 d=%-3d  meeting %10.1f  lattice-lean %10.1f  perDeme-lean "
              "%8.1f   T_coal %10.1f  (censored %d)"
              % (d, meet, row["meeting_time_lean_onLattice"],
                 row["meeting_time_lean_perDeme_diffusionTimescale"], tcoal, cens),
              flush=True)
    out["rows"] = rows
    tw = [r for r in rows if r["d"] == 0][0]["coal_time_measured"]
    out["control_P3a_Twithin_measured"] = tw
    out["control_P3a_Twithin_expected_2_N_total"] = 2.0 * ne * ddeme
    out["control_P3a_pass"] = abs(tw / (2.0 * ne * ddeme) - 1.0) < 0.05
    mt = [r for r in rows if r["d"] in (4, 8, 16)]
    out["control_P3b_meeting_time_worst_rel_err"] = max(
        abs(r["meeting_time_measured"] / r["meeting_time_lean_onLattice"] - 1.0)
        for r in mt)
    out["control_P3b_pass"] = out["control_P3b_meeting_time_worst_rel_err"] < 0.08
    print("  CONTROL P3a T_within measured %.1f vs 2*N_total %.1f -> %s"
          % (tw, 2.0 * ne * ddeme, "PASS" if out["control_P3a_pass"] else "FAIL"),
          flush=True)
    print("  CONTROL P3b lattice meeting time worst rel err %.4f -> %s"
          % (out["control_P3b_meeting_time_worst_rel_err"],
             "PASS" if out["control_P3b_pass"] else "FAIL"), flush=True)
    fst = []
    for r in rows:
        if r["d"] == 0:
            continue
        tb = r["coal_time_measured"]
        f_meas = 1.0 - tw / tb
        f_lean = r["d"] / (r["d"] + 4.0 * ne * m * s2)
        # the exponential form that was DELETED, with L fitted per-row would be
        # unfair; report the best single-L exponential separately below.
        # the same hyperbolic derivation carried out WITHOUT the d << D limit:
        # meeting time d(D-d)/(2 s2 m) over a metapopulation 2*D*Ne
        deff = r["d"] * (ddeme - r["d"]) / ddeme
        f_lat = deff / (deff + 4.0 * ne * m * s2)
        fst.append({"d": r["d"], "T_between": tb, "T_within": tw,
                    "fst_measured": f_meas,
                    "fst_lean_demoSteppingStoneFst": f_lean,
                    "rel_err": (f_lean - f_meas) / f_meas,
                    "fst_lattice_exact_hyperbolic": f_lat,
                    "rel_err_lattice": (f_lat - f_meas) / f_meas})
        print("  SIM5 Fst d=%-3d measured %.4f  lean d/(d+4Nem s2) %.4f (%+.3f) "
              " lattice-hyperbolic %.4f (%+.3f)"
              % (r["d"], f_meas, f_lean, (f_lean - f_meas) / f_meas,
                 f_lat, (f_lat - f_meas) / f_meas), flush=True)
    out["fst"] = fst
    # best-fit exponential 1-exp(-d/L), L scanned; RMS relative error of each form
    best = None
    L = 0.25
    while L < 200.0:
        e = 0.0
        for f in fst:
            pr = 1.0 - math.exp(-f["d"] / L)
            e += ((pr - f["fst_measured"]) / f["fst_measured"]) ** 2
        e = math.sqrt(e / len(fst))
        if best is None or e < best[1]:
            best = (L, e)
        L *= 1.02
    rms_hyp = math.sqrt(sum(f["rel_err"] ** 2 for f in fst) / len(fst))
    out["rms_rel_err_hyperbolic_demoSteppingStoneFst"] = rms_hyp
    out["best_fit_exponential_L"] = best[0]
    out["rms_rel_err_exponential_L_fitted"] = best[1]
    print("  SIM5 RMS rel err: hyperbolic (corpus) %.4f | best-fitted "
          "exponential 1-exp(-d/L), L=%.2f: %.4f"
          % (rms_hyp, best[0], best[1]), flush=True)
    return out


# --------------------------------------------------------------------------
def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    out = {}
    with Pool(NCORE) as pool:
        print("POSITIVE CONTROLS FIRST", flush=True)
        if which in ("all", "controls", "sim1", "sim2"):
            out["control_P1_mutation_drift_identity"] = control_p1(pool)
            out["control_P2_pure_drift_recurrence"] = control_p2(pool)
            if not (out["control_P1_mutation_drift_identity"]["pass"]
                    and out["control_P2_pure_drift_recurrence"]["pass"]):
                print("CONTROLS FAILED -- nothing below is admissible", flush=True)
                json.dump(out, open("coal_sim_results_%s.json" % which, "w"), indent=1)
                return 1
        if which in ("all", "sim1"):
            print("\nSIM1 fstMutationDriftTransient", flush=True)
            out["sim1_fstMutationDriftTransient"] = sim1(pool)
        if which in ("all", "sim2"):
            print("\nSIM2 fstMigrationMutationEquilibrium", flush=True)
            out["sim2_fstMigrationMutationEquilibrium"] = sim2(pool)
        if which in ("all", "sim3"):
            print("\nSIM3 admixtureLD / admixedAlleleFreq "
                  "(last two rows are control P4)", flush=True)
            out["sim3_admixtureLD"] = sim3(pool)
        if which in ("all", "sim4"):
            print("\nSIM4 expectedNewMutations / sharedLDFractionFromMutation",
                  flush=True)
            out["sim4_expectedNewMutations"] = sim4(pool)
        if which in ("all", "sim5"):
            print("\nSIM5 stepping stone (control P3 is the d=0 T_within = 2Ne "
                  "row and the meeting-time column)", flush=True)
            out["sim5_stepping_stone"] = sim5(pool)
    fn = "coal_sim_results_%s.json" % which
    json.dump(out, open(fn, "w"), indent=1)
    print("\n-> " + fn, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())

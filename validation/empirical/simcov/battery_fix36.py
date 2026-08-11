"""Battery fix36: the tag-side monomorphic probability, by coalescent moment duality.

THE LAW UNDER TEST. For a neutral variant at frequency `p` at the moment two branches
part, the probability that a sample of `n` haplotypes drawn from one branch `t`
generations later is MONOMORPHIC -- every copy the same allele, so the variant carries no
signal there -- is

    P(mono | p, n, tau)  =  SUM_k  P(N_tau = k | N_0 = n) * ( p^k + (1-p)^k ),
    tau = t / (2 Ne)

with `N_tau` Kingman's block-counting process, a pure death chain from `n` to `1` with
rate binom(k,2). This is moment duality -- E[X_t^m | X_0 = p] = E[p^{N_t} | N_0 = m] --
and it is EXACT for the Wright-Fisher diffusion: no moment closure, no distributional
assumption, and zero fitted quantities. The law is Tavare (1984); the block-counting
distribution in closed form is Chen & Chen (2013, PMC3697976) eq 15.

WHY THIS BATTERY EXISTS AND WHY IT DOES NOT CALL msprime. The law's truth does not depend
on how the frequencies `p` were chosen -- ascertainment enters ONLY by deciding which `p`
values are fed in. So the sharp test is a direct Wright-Fisher simulation at known `p`,
reproducible from this repository by anyone, rather than a coalescent ancestry whose
ascertainment machinery would have to be trusted alongside the law. A separately run
ascertained-tag version at Ne=1500, n=200, 24 replicates and 2147 tags per cell agreed at
worst 1.17 sems; that run is NOT in this repository and does not count here. This battery
is the part a reader can check.

That distinction is the whole reason this file exists. `stillSegregatingProb` in
`PhenomeWidePortability.lean` states in its own docstring that two independent
computations agree with it but that "those scripts are not in this repository, so a reader
cannot check them and they do not amount to a verdict." Landing a second body with the
same confession would reproduce a defect the corpus has already named against itself.

THE RELATION TO `stillSegregatingProb`, WHICH IS A DIFFERENT OBJECT AND MUST NOT BE
CONFUSED WITH THIS ONE. That body is the probability a variant is still segregating IN THE
POPULATION -- Kimura's eigenfunction solution, with no sample size in it. This one is a
property of a SAMPLE of `n`, and a variant can be segregating in the population while
absent from the sample. They meet only in the limit: `1 - P(mono | p, n, tau)` decreases
to `stillSegregatingProb` as `n` grows. The `n`-dependence is the entire content here, and
it is what an analysis pricing tag loss off a population-level quantity was missing.

THE TWO COMPETITORS ARE RECORDED ON THE SAME CELLS, because a battery that rejects nothing
is indistinguishable from a battery with no power.

  [beta closure, competing] -- Balding-Nichols: `p_t ~ Beta` with mean `p` and variance
      `p(1-p)F`, `F = 1 - exp(-tau)`. It matches the first two moments of the truth
      EXACTLY and still fails, because a continuous density on (0,1) has no atoms at 0 and
      1 and the monomorphic probability is precisely the atom mass. This was the corpus's
      previous approximation and it is refuted here on the cells that clear the exact form.
      Its failure is worst at SMALL F, which is the diagnostic signature: at short times
      almost all the monomorphic mass is atom mass.

  [tau/2 convention, competing] -- the same law with `tau = t/(4 Ne)`, i.e. reading
      Tavare's `N` as the DIPLOID size rather than as gene copies. One wrong constant in an
      otherwise correct law. It is here because a factor-of-2 timescale convention is the
      commonest way to get this family of results wrong, and a battery that cannot see it
      is not testing the timescale at all.

CELLS ARE ADMITTED BY A RULE FIXED IN ADVANCE, NOT BY THEIR RESULT. A cell is readable
only if the predicted probability clears `5/K` -- five expected events in `K` trajectories.
At `p = 0.5` and `t = 250` the law predicts about 3e-7, which `K` trajectories cannot
measure at all, and reporting a measured 0 against it would report the resolution of the
simulation rather than the accuracy of the law. Excluded cells are PRINTED with their
predicted values, not silently dropped.

THE TWO CONTROLS ARE INDEPENDENT OF THE LAW AND BOTH CAN FAIL. An earlier draft of this
file used `n = 1`, where a sample of one is monomorphic by definition -- an identity
control, which cannot fail and therefore checks only plumbing. Both controls here compute
their target from something the block-counting sum does not supply:

  PURE SAMPLING at `t = 0`. The answer is `p^n + (1-p)^n` with no coalescent content
      whatsoever. Run at frequencies below the MAF floor (0.005 to 0.02) for the arithmetic
      reason that `0.95^200 = 3.5e-5` is unmeasurable at this `K` while `0.99^200 = 0.134`
      is comfortable. A control has to be readable to be a control.

  THE PAIR COALESCENT at `n = 2`, against `1 - 2p(1-p)exp(-tau)`. This is the two-lineage
      case in closed form, derived from the pair coalescence probability alone and using no
      block-counting distribution, so it independently tests the timescale that the
      competing `tau/2` entry attacks. Its values sit between 0.5 and 0.95, so it is
      readable everywhere.

THE BLOCK-COUNTING DISTRIBUTION IS COMPUTED BY UNIFORMIZATION, NOT BY THE CLOSED FORM.
Chen & Chen eq 15 is an alternating sum with factorial-scale terms; at `n = 200` in double
precision it loses all its precision to cancellation. Uniformization -- `P(tau) = SUM_j
Poisson(j; Lam*tau) * (I + Q/Lam)^j` with `Lam = n(n-1)/2` -- has no subtraction anywhere,
so every partial sum is a sub-probability vector. Cite the closed form as the law; compute
with a form that survives the `n` the application needs.
"""
import json
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

NE_DIP, NSAMP = 1500, 200
TWO_NE = 2 * NE_DIP
TIMES = (250, 750, 2000)
K = 12000                     # independent WF trajectories per frequency group
SEED = 3600017


# ------------------------------------------------------------------ the law
def block_counting_pmf(n, tau):
    """P(N_tau = k | N_0 = n), k = 1..n, by uniformization. No subtraction anywhere."""
    if n == 1:
        return np.array([1.0])
    lam = np.array([k * (k - 1) / 2.0 for k in range(1, n + 1)])   # lam[k-1]
    Lam = lam[-1]
    stay, down = 1.0 - lam / Lam, lam / Lam
    v = np.zeros(n)
    v[n - 1] = 1.0
    out = np.zeros(n)
    m = Lam * tau
    jmax = int(m + 10 * math.sqrt(m) + 50)
    logw = -m                                    # log Poisson(0; m)
    for j in range(jmax + 1):
        out += math.exp(logw) * v
        nxt = v * stay
        nxt[:-1] += v[1:] * down[1:]
        v = nxt
        logw += math.log(m) - math.log(j + 1)
    return out / out.sum()


def p_mono(p, n, tau, pmf=None):
    """P(sample of n monomorphic | frequency p, coalescent time tau). The law."""
    P = block_counting_pmf(n, tau) if pmf is None else pmf
    i = np.arange(1, len(P) + 1)
    p = np.atleast_1d(np.asarray(p, dtype=float))
    return np.power.outer(p, i) @ P + np.power.outer(1 - p, i) @ P


def p_mono_beta(p, n, F):
    """COMPETITOR: Balding-Nichols. E[X^n] + E[(1-X)^n] under a Beta with the right mean
    and variance -- exact in the first two moments, no atoms at the boundaries."""
    c = (1.0 - F) / F
    p = np.atleast_1d(np.asarray(p, dtype=float))
    a, b = p * c, (1.0 - p) * c
    ea, eb = np.ones_like(p), np.ones_like(p)
    for s in range(n):
        ea *= (a + s) / (c + s)
        eb *= (b + s) / (c + s)
    return ea + eb


def selfcheck():
    """The uniformization engine against death chains small enough to solve by hand."""
    bad = []
    for tau in (0.05, 0.25, 0.9):
        P2 = block_counting_pmf(2, tau)
        if abs(P2[1] - math.exp(-tau)) > 1e-12:
            bad.append(("n=2 stays at 2", tau, P2[1], math.exp(-tau)))
        P3 = block_counting_pmf(3, tau)
        want2 = 1.5 * (math.exp(-tau) - math.exp(-3 * tau))
        if abs(P3[2] - math.exp(-3 * tau)) > 1e-12 or abs(P3[1] - want2) > 1e-12:
            bad.append(("n=3", tau, (P3[2], P3[1]), (math.exp(-3 * tau), want2)))
    for p in (0.05, 0.3):                      # tau -> 0 is pure sampling
        got, want = float(p_mono(p, 20, 1e-12)[0]), p ** 20 + (1 - p) ** 20
        if abs(got - want) > 1e-9:
            bad.append(("tau->0", p, got, want))
    if bad:
        raise AssertionError("uniformization self-check failed: %r" % (bad,))
    print("uniformization self-checks pass (n=2 and n=3 analytic, tau->0 pure sampling)")


# ------------------------------------------------------------------ the simulation
def drift_snapshots(rng, p0, times):
    """Exact Wright-Fisher binomial drift on TWO_NE gene copies from p0. Returns the
    population frequency at each requested time, so one set of trajectories can be
    sampled at several sample sizes."""
    p = np.array(p0, dtype=float)
    out, prev = {}, 0
    for t in times:
        for _ in range(t - prev):
            p = rng.binomial(TWO_NE, p) / TWO_NE
        prev = t
        out[t] = p.copy()
    return out


def mono_frac(rng, p, n):
    """Draw a sample of n haplotypes at each population frequency; is it monomorphic?"""
    k = rng.binomial(n, p)
    return ((k == 0) | (k == n)).astype(float)


def cell(design, lean, truth):
    return dict(design=design, lean=float(lean), truth=float(truth),
                sem=max(math.sqrt(max(truth, 1.0 / K) * (1 - truth) / K), 1e-9))


def main():
    selfcheck()
    rng = np.random.default_rng(SEED)

    groups = [("p=%.2f" % p, np.full(K, p)) for p in (0.05, 0.10, 0.25, 0.50)]
    # the realistic use: a neutral 1/p spectrum truncated at the MAF floor an
    # ascertainment would have applied, which is the shape a tag panel presents
    u = rng.uniform(0, 1, K)
    groups.append(("neutral 1/p spectrum on [0.05, 0.95]",
                   0.05 * (0.95 / 0.05) ** u))

    pmf = {t: block_counting_pmf(NSAMP, t / TWO_NE) for t in TIMES}
    pmf_half = {t: block_counting_pmf(NSAMP, t / (2.0 * TWO_NE)) for t in TIMES}

    cells, cells_beta, cells_half, ctrl_pair, skipped = [], [], [], [], []
    for label, p0 in groups:
        snap = drift_snapshots(rng, p0, TIMES)
        for t in TIMES:
            tau = t / TWO_NE
            design = "%s, t=%d (tau=%.4f)" % (label, t, tau)
            meas = float(mono_frac(rng, snap[t], NSAMP).mean())
            pred = float(p_mono(p0, NSAMP, tau, pmf=pmf[t]).mean())
            if pred < 5.0 / K:
                skipped.append((design, pred))
            else:
                cells.append(cell(design, pred, meas))
                cells_beta.append(cell(
                    design, p_mono_beta(p0, NSAMP, 1 - math.exp(-tau)).mean(), meas))
                cells_half.append(cell(
                    design, p_mono(p0, NSAMP, tau / 2.0, pmf=pmf_half[t]).mean(), meas))
            # CONTROL: the pair coalescent, in closed form, no block-counting sum
            m2 = float(mono_frac(rng, snap[t], 2).mean())
            want2 = float(np.mean(1 - 2 * p0 * (1 - p0) * math.exp(-tau)))
            ctrl_pair.append(cell("%s, n=2 pair coalescent" % design, want2, m2))

    # CONTROL: pure sampling at t = 0, at frequencies where it is measurable at all
    ctrl_t0 = []
    for p in (0.005, 0.01, 0.02):
        pv = np.full(K, p)
        m0 = float(mono_frac(rng, pv, NSAMP).mean())
        ctrl_t0.append(cell("p=%.3f, t=0 pure sampling" % p,
                            p ** NSAMP + (1 - p) ** NSAMP, m0))

    reg = ("exact Wright-Fisher binomial drift on 2Ne=%d gene copies from a KNOWN initial "
           "frequency, %d independent trajectories per group, sample of n=%d haplotypes "
           "drawn binomially at each time; the estimand is the POOLED fraction of "
           "trajectories whose sample is monomorphic, matched by a pooled mean of the "
           "predicted per-trajectory probabilities. Cells admitted only where the "
           "predicted probability clears 5/%d expected events, and the excluded cells are "
           "printed with their predictions." % (TWO_NE, K, NSAMP, K))
    control = dict(ctrl_t0[1])
    control["design"] = ("pure sampling at t=0, computed from the observable's definition "
                         "with no coalescent content")

    record("tagSampleMonomorphicProb", "Coalescent/Duality.lean",
           "sum_k P(N_tau = k | n) * (p^k + (1-p)^k)",
           cells + ctrl_t0 + ctrl_pair, regime=reg, control=control,
           argument_source="model", realised_inputs=True,
           note="Tavare (1984); block-counting pmf by uniformization rather than the "
                "cancellation-prone closed form. Zero fitted quantities.")
    record("tagSampleMonomorphicProb [beta closure, competing]",
           "Coalescent/Duality.lean",
           "E[X^n]+E[(1-X)^n] for X ~ Beta(mean p, var p(1-p)(1-exp(-tau)))",
           cells_beta, regime=reg, control=control, argument_source="model", realised_inputs=True,
           note="matches the first two moments exactly and has no atoms at 0 and 1, "
                "which is where the entire monomorphic probability lives")
    record("tagSampleMonomorphicProb [tau/2 convention, competing]",
           "Coalescent/Duality.lean",
           "the same law with tau = t/(4 Ne), reading Tavare's N as the diploid size",
           cells_half, regime=reg, control=control, argument_source="model", realised_inputs=True,
           note="one wrong constant in an otherwise correct law; cells that cannot see a "
                "factor-of-2 timescale error are not testing the timescale")

    # dump_results, NOT a bare json.dump: it stamps the SOURCE HASH into the
    # file. Without it the ledger records the rows as UNVERIFIED -- no reader
    # can check the numbers came from this battery, which is the same standing
    # as the confession this file exists to avoid.
    sha = dump_results(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "battery_fix36_results.json"))
    print("\nbattery sha %s" % sha)
    if skipped:
        print("\nCELLS EXCLUDED BY THE PRE-SET READABILITY RULE (predicted < 5/%d):" % K)
        for design, pred in skipped:
            print("  %-46s predicted %.3e" % (design, pred))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-22s %-52s worst %9.2f sems, %7.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

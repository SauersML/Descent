"""Simulation engines: independent ground truth for the definitions.

The range and invariant tiers need no reference values, which is why they
scale.  Their residue is the definitions whose names make a claim that only an
external reference can settle -- is `2 * p * (1 - p)` really the variance of a
genotype under Hardy-Weinberg, is `(1 - r) ^ t` really the survival of linkage
disequilibrium under recombination.

Every oracle here simulates the quantity the NAME refers to, from first
principles: draw individuals, draw genotypes, run generations, measure.  None
of them is derived by rearranging the Lean formula, because an oracle obtained
that way tests nothing.  Where a closed form is used it is a textbook result
stated in the docstring with its source, and it is cross-checked against the
sampler at a control point in the same run.

Pure numpy on purpose.  msprime and scipy are absent from this environment, and
the quantities in this residue are ones a Wright-Fisher sampler and a Gaussian
sampler can reach honestly.
"""
from __future__ import annotations

import numpy as np

# --------------------------------------------------------------------------
# Wright-Fisher: drift, heterozygosity, differentiation


def wf_trajectory(p0, Ne, t, reps, rng):
    """Binomial Wright-Fisher for `t` generations.  Returns final frequencies.

    Diploid, so 2*Ne gene copies per generation.
    """
    p = np.full(reps, float(p0))
    n = int(round(2 * Ne))
    for _ in range(int(t)):
        p = rng.binomial(n, np.clip(p, 0.0, 1.0)) / n
    return p


def fst_to_generations(fst, Ne):
    """Generations of drift giving the requested F_ST at effective size Ne.

    Inverts the standard neutral relation F_ST = 1 - (1 - 1/(2 Ne))^t.  This is
    a change of PARAMETERISATION so the simulation can be asked for a given
    F_ST; it is not the quantity under test.
    """
    per_gen = 1.0 - 1.0 / (2.0 * Ne)
    return max(1, int(round(np.log(1.0 - fst) / np.log(per_gen))))


def sim_drift_variance(p0, fst, Ne=500, reps=40000, seed=0):
    """Var(p_t) after drift to differentiation `fst`, starting from `p0`."""
    rng = np.random.default_rng(seed)
    t = fst_to_generations(fst, Ne)
    p = wf_trajectory(p0, Ne, t, reps, rng)
    return float(np.var(p))


def sim_freq_diff_sq(p0, fst, Ne=500, reps=40000, seed=0):
    """E[(p1 - p2)^2] for two populations drifting independently from `p0`."""
    rng = np.random.default_rng(seed)
    t = fst_to_generations(fst, Ne)
    p1 = wf_trajectory(p0, Ne, t, reps, rng)
    p2 = wf_trajectory(p0, Ne, t, reps, rng)
    return float(np.mean((p1 - p2) ** 2))


def sim_heterozygosity_decay(H0, Ne, t, reps=20000, seed=0):
    """Mean heterozygosity after `t` generations of drift.

    Starts every replicate at the frequency giving H0 = 2p(1-p).
    """
    rng = np.random.default_rng(seed)
    p0 = 0.5 * (1.0 - np.sqrt(max(0.0, 1.0 - 2.0 * H0)))
    p = wf_trajectory(p0, Ne, t, reps, rng)
    return float(np.mean(2 * p * (1 - p)))


# --------------------------------------------------------------------------
# Hardy-Weinberg genotypes and variance components


def sim_genotype_variance(p, n=400000, seed=0):
    """Var of a diploid genotype dosage under Hardy-Weinberg."""
    rng = np.random.default_rng(seed)
    g = rng.binomial(2, p, size=n)
    return float(np.var(g))


def sim_pairwise_epistatic_variance(gamma, p1, p2, n=600000, seed=0):
    """Var of the pairwise interaction term gamma * g1 * g2.

    Under Hardy-Weinberg with the two loci in linkage equilibrium, so the
    genotypes are drawn independently.  Centred as a variance COMPONENT: the
    interaction contribution is the variance of the product of the CENTRED
    dosages, which is what an interaction term contributes to additive-model
    residual variance.
    """
    rng = np.random.default_rng(seed)
    g1 = rng.binomial(2, p1, size=n).astype(float)
    g2 = rng.binomial(2, p2, size=n).astype(float)
    return float(np.var(gamma * (g1 - g1.mean()) * (g2 - g2.mean())))


def sim_between_subgroup_variance(p1, p2, n=400000, seed=0):
    """Variance of allele frequency BETWEEN two equally sized subgroups.

    Draws the subgroup label, then the allele; the between-group component is
    the variance of the group means.
    """
    rng = np.random.default_rng(seed)
    grp = rng.integers(0, 2, size=n)
    a = rng.random(n) < np.where(grp == 0, p1, p2)
    m0, m1 = a[grp == 0].mean(), a[grp == 1].mean()
    grand = a.mean()
    w0 = (grp == 0).mean()
    return float(w0 * (m0 - grand) ** 2 + (1 - w0) * (m1 - grand) ** 2)


# --------------------------------------------------------------------------
# admixture and two-locus LD


def sim_admixed_haplotype_freq(alpha, pA, qA, pB, qB, n=800000, seed=0):
    """Frequency of the AB haplotype in a freshly admixed population.

    Individuals come from source A with probability `alpha`, else source B.
    Each source is in linkage equilibrium internally, so within a source the
    two loci are drawn independently.
    """
    rng = np.random.default_rng(seed)
    from_a = rng.random(n) < alpha
    p = np.where(from_a, pA, pB)
    q = np.where(from_a, qA, qB)
    hap_a = rng.random(n) < p
    hap_b = rng.random(n) < q
    return float(np.mean(hap_a & hap_b))


def sim_admixture_ld(alpha, pA, qA, pB, qB, n=1500000, seed=0):
    """D = P(AB) - P(A)P(B) in a freshly admixed population."""
    rng = np.random.default_rng(seed)
    from_a = rng.random(n) < alpha
    p = np.where(from_a, pA, pB)
    q = np.where(from_a, qA, qB)
    ha = rng.random(n) < p
    hb = rng.random(n) < q
    return float(np.mean(ha & hb) - np.mean(ha) * np.mean(hb))


def sim_ld_decay(D0, r, g, n=400000, seed=0):
    """LD remaining after `g` generations of random mating with recombination.

    Simulated as an explicit two-locus haplotype pool: each generation, a
    fraction `r` of gametes are recombinants formed from two independently
    drawn parental haplotypes, which is what breaks the association.
    """
    rng = np.random.default_rng(seed)
    # build a haplotype pool with the requested D at p = q = 0.5
    p = q = 0.5
    probs = np.array([p * q + D0, p * (1 - q) - D0,
                      (1 - p) * q - D0, (1 - p) * (1 - q) + D0])
    if np.any(probs < 0):
        return None
    idx = rng.choice(4, size=n, p=probs / probs.sum())
    a = (idx < 2).astype(np.int8)          # locus 1 allele
    b = (idx % 2 == 0).astype(np.int8)     # locus 2 allele
    for _ in range(int(g)):
        i = rng.integers(0, n, size=n)
        j = rng.integers(0, n, size=n)
        rec = rng.random(n) < r
        a_new = a[i]
        b_new = np.where(rec, b[j], b[i])
        a, b = a_new, b_new
    return float(np.mean(a * b) - np.mean(a) * np.mean(b))


def sim_no_recombination_prob(r, t, n=400000, seed=0):
    """P(no recombination in `t` meioses) at per-generation rate `r`."""
    rng = np.random.default_rng(seed)
    hits = rng.random((n, int(t))) < r
    return float(np.mean(~hits.any(axis=1)))


# --------------------------------------------------------------------------
# prediction, risk and information


def sim_r2_from_variances(v_signal, v_noise, n=400000, seed=0):
    """Squared correlation between the signal and signal+noise."""
    rng = np.random.default_rng(seed)
    s = rng.normal(0, np.sqrt(v_signal), n)
    y = s + rng.normal(0, np.sqrt(v_noise), n)
    return float(np.corrcoef(s, y)[0, 1] ** 2)


def sim_shrinkage_mse(lam, sigma_sq, beta_sq, n=400000, seed=0):
    """MSE of the shrunk estimator `lam * (beta + noise)` for beta."""
    rng = np.random.default_rng(seed)
    beta = rng.normal(0, np.sqrt(beta_sq), n)
    obs = beta + rng.normal(0, np.sqrt(sigma_sq), n)
    return float(np.mean((lam * obs - beta) ** 2))


def sim_optimal_shrinkage(sigma_sq, beta_sq, n=400000, seed=0):
    """The shrinkage minimising MSE, found by search rather than by formula."""
    grid = np.linspace(0.0, 1.0, 2001)
    rng = np.random.default_rng(seed)
    beta = rng.normal(0, np.sqrt(beta_sq), n)
    obs = beta + rng.normal(0, np.sqrt(sigma_sq), n)
    # MSE(lam) is quadratic in lam; evaluate on a grid and take the argmin
    mses = [np.mean((g * obs - beta) ** 2) for g in grid]
    return float(grid[int(np.argmin(mses))])


def sim_bernoulli_logloss(p, q, n=600000, seed=0):
    """E_{y~Bernoulli(p)}[-log P_q(y)]."""
    rng = np.random.default_rng(seed)
    y = rng.random(n) < p
    return float(np.mean(np.where(y, -np.log(q), -np.log(1 - q))))


def sim_bernoulli_kl(p, q, n=600000, seed=0):
    """E_{y~Bernoulli(p)}[log(P_p(y) / P_q(y))]."""
    rng = np.random.default_rng(seed)
    y = rng.random(n) < p
    lp = np.where(y, np.log(p), np.log(1 - p))
    lq = np.where(y, np.log(q), np.log(1 - q))
    return float(np.mean(lp - lq))


def sim_brier(q, eta, n=600000, seed=0):
    """E_{y~Bernoulli(eta)}[(q - y)^2] for a constant forecast `q`."""
    rng = np.random.default_rng(seed)
    y = (rng.random(n) < eta).astype(float)
    return float(np.mean((q - y) ** 2))


def sim_number_needed_to_screen(sens, prev, n=200000, seed=0):
    """Expected number screened to detect one case.

    Simulated as a waiting time: screen individuals one at a time, each a case
    with probability `prev` and detected with probability `sens`.  Sampled as a
    geometric rather than computed, so the formula is not assumed.
    """
    rng = np.random.default_rng(seed)
    per = prev * sens
    if per <= 0:
        return None
    return float(np.mean(rng.geometric(per, size=n)))


def sim_gwas_estimator_variance(n_ind, p, r2_ld, reps=4000, seed=0):
    """Sampling variance of the marker effect estimate in a simple GWAS.

    A causal variant with unit effect, a marker in LD r^2 with it, phenotype
    standardised.  The estimator is ordinary least squares of phenotype on
    marker dosage.  Returns the empirical variance of the estimate, from which
    an effective sample size can be read off independently of any formula.
    """
    rng = np.random.default_rng(seed)
    ests = np.empty(reps)
    rho = np.sqrt(r2_ld)
    for k in range(reps):
        gc = rng.binomial(2, p, size=n_ind).astype(float)
        gc = (gc - gc.mean()) / (gc.std() + 1e-12)
        noise = rng.normal(0, 1, n_ind)
        gm = rho * gc + np.sqrt(max(0.0, 1 - r2_ld)) * noise
        y = gc + rng.normal(0, 1, n_ind)
        gm = (gm - gm.mean())
        ests[k] = float(gm @ y / (gm @ gm))
    return float(np.var(ests))


def sim_admixture_ld_at_gen(alpha, pA, qA, pB, qB, r, g, n=800000, seed=0):
    """Admixture LD after `g` generations of random mating with recombination.

    One simulation end to end: build the admixed haplotype pool by drawing each
    founder from source A with probability `alpha`, then run the same
    recombination loop as `sim_ld_decay` on that pool.  Nothing is multiplied
    by a decay factor -- the decay is what the loop produces.
    """
    rng = np.random.default_rng(seed)
    from_a = rng.random(n) < alpha
    a = (rng.random(n) < np.where(from_a, pA, pB)).astype(np.int8)
    b = (rng.random(n) < np.where(from_a, qA, qB)).astype(np.int8)
    for _ in range(int(g)):
        i = rng.integers(0, n, size=n)
        j = rng.integers(0, n, size=n)
        rec = rng.random(n) < r
        a, b = a[i], np.where(rec, b[j], b[i])
    return float(np.mean(a * b) - np.mean(a) * np.mean(b))


# --------------------------------------------------------------------------
# second batch: regression, variance components, mutation-drift, structure


def sim_ols_slope_variance(sigma2, varX, n, reps=1200, seed=0):
    """Sampling variance of the OLS slope, measured across replicate fits.

    y = b*x + e with Var(e) = sigma2 and Var(x) = varX.  The slope is refit on
    each replicate and the variance is taken over replicates, so the textbook
    sigma2/(n*varX) is never used -- it is what the check is testing.
    """
    rng = np.random.default_rng(seed)
    n = int(round(n))
    est = np.empty(reps)
    sx = np.sqrt(varX)
    for k in range(reps):
        x = rng.normal(0.0, sx, n)
        y = 1.0 * x + rng.normal(0.0, np.sqrt(sigma2), n)
        xc = x - x.mean()
        est[k] = float(xc @ (y - y.mean()) / (xc @ xc))
    return float(np.var(est, ddof=1))


def sim_r2_from_mse(mse, varY, n=400000, seed=0):
    """1 - SSE/SST for a predictor whose error variance is `mse`."""
    rng = np.random.default_rng(seed)
    y = rng.normal(0.0, np.sqrt(varY), n)
    pred = y + rng.normal(0.0, np.sqrt(mse), n)
    # centre the predictor so the comparison is of explained variance
    sse = np.mean((y - pred) ** 2)
    sst = np.var(y)
    return float(1.0 - sse / sst)


def sim_fisher_average_effect(a, d, p, n=800000, seed=0):
    """Fisher's average effect: the REGRESSION slope of genotypic value on dosage.

    Genotypic values -a, d, a at dosages 0, 1, 2 under Hardy-Weinberg.  The
    average effect of a gene substitution is defined as the least-squares
    slope, so it is obtained here by regressing, not by the formula.
    """
    rng = np.random.default_rng(seed)
    g = rng.binomial(2, p, size=n)
    val = np.where(g == 0, -a, np.where(g == 1, d, a)).astype(float)
    gc = g - g.mean()
    return float(gc @ (val - val.mean()) / (gc @ gc))


def sim_hwe_heterozygote_freq(p, n=400000, seed=0):
    """P(heterozygote) under Hardy-Weinberg, sampled."""
    rng = np.random.default_rng(seed)
    return float(np.mean(rng.binomial(2, p, size=n) == 1))


def sim_heterozygosity_loss(t, Ne, reps=20000, seed=0):
    """1 - H_t/H_0 after t generations of drift, from an explicit WF run."""
    rng = np.random.default_rng(seed)
    p0 = 0.5
    p = wf_trajectory(p0, Ne, t, reps, rng)
    h0 = 2 * p0 * (1 - p0)
    return float(1.0 - np.mean(2 * p * (1 - p)) / h0)


def sim_infinite_alleles_heterozygosity(theta, Ne=None, reps=4000, seed=0):
    """Equilibrium heterozygosity under the infinite-alleles model.

    theta = 4*Ne*mu.  Simulated as a coalescent: two gene copies differ if any
    mutation falls on either lineage before they coalesce.  Coalescence of two
    lineages in a diploid population of size Ne is geometric with rate
    1/(2*Ne), and mutations arrive at rate mu on each lineage; the identity is
    measured by sampling those waiting times, not by evaluating theta/(1+theta).
    """
    rng = np.random.default_rng(seed)
    Ne = 1000.0 if Ne is None else Ne
    mu = theta / (4.0 * Ne)
    if mu <= 0 or mu >= 1:
        return None
    tcoal = rng.geometric(1.0 / (2.0 * Ne), size=reps)
    # P(at least one mutation on either of the two lineages before coalescing)
    p_no_mut = (1.0 - mu) ** (2.0 * tcoal)
    return float(np.mean(1.0 - p_no_mut))


def sim_island_model_fst(Ne, m, demes=100, gens=None, reps=60, seed=0):
    """F_ST at migration-drift equilibrium in a finite island model.

    Explicit Wright-Fisher in each deme with a migrant pool.  REGIME: the
    closed form being checked is the infinite-island limit, so this is run
    with many demes; at few demes the two genuinely differ and that is a
    property of the model, not a defect in the formula.
    """
    rng = np.random.default_rng(seed)
    Ne = float(Ne)
    n = int(round(2 * Ne))
    if n < 2 or not (0 < m < 1):
        return None
    gens = int(gens or max(120, 4 * Ne))
    p = np.full((reps, demes), 0.5)
    for _ in range(gens):
        pbar = p.mean(axis=1, keepdims=True)
        p = (1.0 - m) * p + m * pbar
        p = rng.binomial(n, np.clip(p, 0.0, 1.0)) / n
    pbar = p.mean(axis=1, keepdims=True)
    hs = np.mean(2 * p * (1 - p))
    ht = np.mean(2 * pbar * (1 - pbar))
    if ht <= 0:
        return None
    return float((ht - hs) / ht)


def sim_distinct_haplotypes(k, n, reps=1500, seed=0):
    """Expected number of DISTINCT haplotypes when n are drawn from 2^k types."""
    rng = np.random.default_rng(seed)
    k, n = int(k), int(n)
    types = 2 ** k
    if types > 10 ** 7:
        return None
    out = np.empty(reps)
    for i in range(reps):
        out[i] = len(np.unique(rng.integers(0, types, size=n)))
    return float(out.mean())


def sim_spike_slab_variance(pi, sigma_slab, n=800000, seed=0):
    """Variance of a spike-and-slab draw: zero w.p. 1-pi, N(0, s^2) w.p. pi."""
    rng = np.random.default_rng(seed)
    on = rng.random(n) < pi
    x = np.where(on, rng.normal(0.0, sigma_slab, n), 0.0)
    return float(np.mean(x ** 2))


def sim_am_equilibrium_variance(V_A, r, h2, gens=40, n=60000, seed=0):
    """Additive variance at assortative-mating equilibrium, by iteration.

    Runs the mating process forward: each generation, mates are paired on
    phenotype with correlation r, and the additive variance is remeasured.
    The closed form V_A/(1 - r*h2) is never used.
    """
    rng = np.random.default_rng(seed)
    if not (0 <= r * h2 < 0.95):
        return None
    va = float(V_A)
    ve = V_A * (1.0 - h2) / max(h2, 1e-9)
    for _ in range(gens):
        a = rng.normal(0.0, np.sqrt(va), n)
        phen = a + rng.normal(0.0, np.sqrt(ve), n)
        order = np.argsort(phen)
        a_s = a[order]
        # pair rank-adjacent individuals with probability r, at random otherwise
        partner = a_s.copy()
        shuffled = a_s[rng.permutation(n)]
        take = rng.random(n) < r
        mate = np.where(take, np.roll(a_s, 1), shuffled)
        off = 0.5 * (partner + mate) + rng.normal(0.0, np.sqrt(va / 2.0), n)
        va = float(np.var(off))
    return va

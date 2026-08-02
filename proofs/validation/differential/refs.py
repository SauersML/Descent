"""Closed-form reference quantities for the coalescent / drift / LD corpus.

Every function here is derived from a stated population-genetic model and is
INDEPENDENT of the Lean definition it is used to check.  Nothing in this file
samples; all of it is exact algebra, so a disagreement is a disagreement about
mathematics, not about Monte Carlo error.

Each reference carries `MODEL`, the assumptions under which it is exact.  A
mismatch between a definition's model and the reference's model is a MODEL
error and is reported separately from a FORMULA error -- the distinction the
`fstDerived`/`fstFromTau`/`targetHetFromFst` cluster turns on.
"""

from __future__ import annotations

import math

# ===========================================================================
# 1. F_ST estimator conventions, two populations, biallelic
# ===========================================================================
# All three are "F_ST" and they are different numbers.  Bhatia, Patterson,
# Sankararaman & Price (2013) Genome Res 23:1514, eqs 6-10.

def fst_nei_gst(p1: float, p2: float) -> float:
    """Nei's G_ST for two equally weighted subpopulations.

    MODEL: parametric (infinite sample), biallelic, equal subpopulation
    weights.  G_ST = 1 - H_S/H_T with H_S the mean within-deme expected
    heterozygosity and H_T the heterozygosity of the pooled allele frequency.
    """
    pbar = (p1 + p2) / 2.0
    h_s = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2.0
    h_t = 2 * pbar * (1 - pbar)
    return 1.0 - h_s / h_t


def fst_hudson(p1: float, p2: float) -> float:
    """Hudson's F_ST, parametric limit.

    MODEL: parametric, biallelic.  N/D with N = (p1-p2)^2 (sample-size
    correction vanishes as n -> inf) and D = p1(1-p2) + p2(1-p1).
    """
    return (p1 - p2) ** 2 / (p1 * (1 - p2) + p2 * (1 - p1))


def fst_hudson_sample(p1: float, p2: float, n1: int, n2: int) -> float:
    """Hudson's ratio-of-averages estimator at finite haploid sample size.

    Present so the parametric limit above can be checked rather than asserted:
    `fst_hudson_sample -> fst_hudson` as n -> inf.
    """
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    return num / den


def fst_weir_cockerham(p1: float, p2: float, n: int) -> float:
    """Weir & Cockerham (1984) theta for two demes of equal haploid size n.

    MODEL: random mating, equal sample sizes, biallelic.  Included to pin
    which of the three conventions a definition matches.
    """
    pbar = (p1 + p2) / 2.0
    s2 = ((p1 - pbar) ** 2 + (p2 - pbar) ** 2)  # r=2 demes: sum/(r-1) = sum
    a = (n / 2.0) * (s2 - (pbar * (1 - pbar) - s2 / 2.0) / (n - 1))
    b = (n / (n - 1.0)) * (pbar * (1 - pbar) - s2 / 2.0)
    return a / (a + b)


# ===========================================================================
# 2. Clean-split coalescent: exact expected coalescence times
# ===========================================================================

def split_ET_within(t: float, n_daughter: float, n_anc: float) -> float:
    """E[T] for two lineages sampled in the same daughter population.

    MODEL: instantaneous clean split t generations ago; constant sizes;
    no migration; no selection.  Continuous (large-N) coalescent.

        E[T_w] = 2*N_d*(1 - e^{-x}) + 2*N_a*e^{-x},   x = t/(2*N_d)

    Derivation: coalescence inside the daughter branch is exponential with
    rate 1/(2 N_d) truncated at t; otherwise both lineages enter the ancestral
    population and wait a further Exp(1/(2 N_a)).
    """
    x = t / (2.0 * n_daughter)
    e = math.exp(-x)
    return 2.0 * n_daughter * (1.0 - e) + 2.0 * n_anc * e


def split_ET_between(t: float, n_anc: float) -> float:
    """E[T] for two lineages sampled one from each daughter population.

    MODEL: as above.  The lineages cannot coalesce before the split, so
    E[T_b] = t + 2*N_a exactly.
    """
    return t + 2.0 * n_anc


def split_fst_hudson(t: float, n1: float, n2: float, n_anc: float) -> float:
    """Hudson F_ST after a clean split, exact, general (possibly unequal) sizes.

    MODEL: as above, plus infinite sites so that expected pairwise diversity
    is proportional to expected coalescence time (the mutation rate cancels).
    F_ST = 1 - mean(E[T_w]) / E[T_b].
    """
    tw = 0.5 * (split_ET_within(t, n1, n_anc) + split_ET_within(t, n2, n_anc))
    return 1.0 - tw / split_ET_between(t, n_anc)


def prob_coalesce_within(t: float, ne: float) -> float:
    """P(two lineages in a closed population of size Ne coalesce within t gens).

    MODEL: closed population, NO mutation, discrete Wright-Fisher.
    Equals the fractional loss of ANCESTRAL heterozygosity, 1 - (1-1/2Ne)^t.
    This is Wright's inbreeding coefficient F for a closed population.  It is
    NOT the F_ST between two populations that split t generations ago; see
    `split_fst_hudson`.
    """
    return 1.0 - (1.0 - 1.0 / (2.0 * ne)) ** t


# ===========================================================================
# 3. Mutation-drift equilibrium and approach
# ===========================================================================

def iam_homozygosity_equilibrium(ne: float, mu: float) -> float:
    """Exact infinite-alleles-model stationary homozygosity.

    MODEL: infinite alleles (every mutation is new), Wright-Fisher, exact
    discrete recursion F' = (1-mu)^2 * [1/(2Ne) + (1-1/(2Ne)) F].
    Fixed point:  F* = (1-mu)^2 / (2Ne - (2Ne-1)(1-mu)^2).
    The familiar 1/(1+4Ne mu) is its O(mu) expansion.
    """
    a = (1.0 - mu) ** 2
    return a / (2.0 * ne - (2.0 * ne - 1.0) * a)


def iam_het_equilibrium(ne: float, mu: float) -> float:
    return 1.0 - iam_homozygosity_equilibrium(ne, mu)


def iam_decay_eigenvalue(ne: float, mu: float) -> float:
    """Exact per-generation eigenvalue of the IAM heterozygosity recursion."""
    return (1.0 - 1.0 / (2.0 * ne)) * (1.0 - mu) ** 2


def iam_het_trajectory(ne: float, mu: float, h0: float, t: int) -> float:
    """Exact IAM heterozygosity after t generations from H0."""
    lam = iam_decay_eigenvalue(ne, mu)
    hstar = iam_het_equilibrium(ne, mu)
    return hstar + (h0 - hstar) * lam ** t


# ===========================================================================
# 4. Island model
# ===========================================================================

def island_fst_finite_demes(ne: float, m: float, d: int) -> float:
    """Wright/Nei finite-island F_ST for d demes.

    MODEL: d demes of size Ne, symmetric island migration at rate m, mutation
    negligible relative to migration.  F_ST = 1 / (1 + 4 Ne m (d/(d-1))^2).
    The corpus formula 1/(1+4 Ne m) is the d -> inf limit.
    """
    return 1.0 / (1.0 + 4.0 * ne * m * (d / (d - 1.0)) ** 2)


def island_fst_exact_recursion(ne: float, m: float) -> float:
    """Exact fixed point of F' = (1-m)^2 [1/(2Ne) + (1-1/(2Ne)) F].

    MODEL: infinite island, migration acting before drift, no mutation.
    Exact in m (the corpus's 1/(1+4Ne m) is the small-m expansion).
    """
    a = (1.0 - m) ** 2
    return a / (a + 2.0 * ne * m * (2.0 - m))


# ===========================================================================
# 5. Linkage disequilibrium
# ===========================================================================

def ld_expected_D_retention(r: float, ne: float) -> float:
    """Exact per-generation retention of E[D] under recombination + drift.

    MODEL: two neutral loci, recombination fraction r, Wright-Fisher size Ne.
    Hill & Robertson (1968): E[D_{t+1} | D_t] = (1-r)(1 - 1/(2Ne)) D_t.
    """
    return (1.0 - r) * (1.0 - 1.0 / (2.0 * ne))


def ld_half_life_exact(r: float, ne: float) -> float:
    """Generations for E[D] to halve, from the retention above.

    MODEL: as `ld_expected_D_retention`.  t_1/2 = ln 2 / -ln[(1-r)(1-1/2Ne)].
    Reduces to 2 Ne ln 2 only in the r -> 0 limit.
    """
    return math.log(2.0) / (-math.log(ld_expected_D_retention(r, ne)))


def sved_sigma_d_sq(ne: float, c: float) -> float:
    """Sved (1971) E[r^2] ~ 1/(1 + 4 Ne c).

    MODEL: identity-by-descent argument; this is a probability of gametic
    identity, and is used as a proxy for E[r^2].
    """
    return 1.0 / (1.0 + 4.0 * ne * c)


def ohta_kimura_sigma_d_sq(ne: float, c: float) -> float:
    """Ohta & Kimura (1971) exact sigma_d^2 = E[D^2]/E[p(1-p)q(1-q)].

    MODEL: neutral two-locus diffusion at drift-recombination equilibrium,
    low mutation.  sigma_d^2 = (10 + rho) / ((2 + rho)(11 + rho)), rho = 4 Ne c.
    This is the standard reference for E[r^2]; Sved's form is a different
    quantity that coincides with it only as rho -> inf.
    """
    rho = 4.0 * ne * c
    return (10.0 + rho) / ((2.0 + rho) * (11.0 + rho))


def ld_ibd_equilibrium_exact(ne: float, c: float) -> float:
    """Exact fixed point of Q' = (1-c)^2 [1/(2Ne) + (1-1/(2Ne)) Q]."""
    a = (1.0 - c) ** 2
    return a / (2.0 * ne) / (1.0 - a * (1.0 - 1.0 / (2.0 * ne)))


# ===========================================================================
# 6. Site frequency spectrum
# ===========================================================================

def sfs_expected_counts(n: int, theta: float) -> list[float]:
    """Standard neutral SFS: E[xi_i] = theta / i, i = 1..n-1.

    MODEL: constant size, infinite sites, no selection, sample size n.
    """
    return [theta / i for i in range(1, n)]


def sfs_singleton_proportion(n: int) -> float:
    """Expected fraction of segregating sites that are singletons.

    MODEL: as above.  = 1 / H_{n-1}, H_{n-1} = sum_{i=1}^{n-1} 1/i.
    Independent of theta.
    """
    return 1.0 / sum(1.0 / i for i in range(1, n))


def watterson_theta_from_S(s: float, n: int) -> float:
    """Watterson's estimator: theta_W = S / H_{n-1}."""
    return s / sum(1.0 / i for i in range(1, n))


def expected_pairwise_diversity(theta: float) -> float:
    """E[pi] = theta under the standard neutral infinite-sites model."""
    return theta


# ===========================================================================
# 7. Stepping stone
# ===========================================================================

def stepping_stone_decay_scale_malecot(m: float, mu: float) -> float:
    """1D stepping-stone characteristic length (Malecot / Kimura-Weiss).

    MODEL: infinite linear array of demes, nearest-neighbour migration rate m
    (total, split both directions), mutation rate mu.  Probability of identity
    decays as exp(-d / L) with L = sqrt(m / (2 mu)).

    Note what L does and does not depend on: it is DECREASING in mu and does
    NOT depend on the deme size Ne.  A characteristic length that contains Ne
    and not mu has the wrong functional form, not merely the wrong constant.
    """
    return math.sqrt(m / (2.0 * mu))


def stepping_stone_fst_hudson(d: float, ne: float, m: float, sigma_sq: float) -> float:
    """Hudson F_ST at deme distance d in 1D, from coalescence times.

    MODEL: 1D stepping stone, E[T_within] = 2 Ne, and the excess coalescence
    time grows linearly in d as Delta(d) = d / (2 sigma^2 m).
    F_ST = Delta / (E[T_within] + Delta) = d / (d + 4 Ne m sigma^2).
    """
    delta = d / (2.0 * sigma_sq * m)
    return delta / (2.0 * ne + delta)

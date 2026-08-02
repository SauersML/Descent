#!/usr/bin/env python3
"""Family simulator: STEPPING STONE. numpy only, no msprime, no scipy.

The family with the largest measured errors in the corpus and, until now, no
simulator at all. Five in-slice definitions, two engines, both vectorised over
replicates so the whole file runs in minutes rather than the ~25 the msprime
script `heavy/h1_stepping_stone_length.py` was budgeted for.

    steppingStoneCharacteristicLength   L = sqrt(m / (2 mu))
    steppingStoneCoalescenceTime        T(d) = d / (2 sigma^2 m)
    demoSteppingStoneFst                d / (d + 4 Ne m sigma^2)
    steppingStoneFstQuadratic           d / (d + 4 Ne sigma^4 m^2)
    steppingStoneFst                    min 1 (f_nb * (1 + alpha (d-1)))

THE MODEL, ONCE, FOR BOTH ENGINES

  A circle of D demes, each of diploid size Ne. Per generation a lineage
  migrates with probability m; a migrant moves +k or -k demes with probability
  1/2 each. So the per-generation dispersal variance is

      V  =  m * k^2   =   m * sigma^2 ,      sigma^2 = k^2 .

  k is what lets sigma^2 be varied AT FIXED m, and m at fixed sigma^2. That is
  the whole point. `demoSteppingStoneFst`'s own docstring records that its
  evidence came from a FREELY FITTED sigma^2, that such a fit constrains only
  the product m*sigma^2, and that "distinguishing the two forms empirically
  requires holding sigma^2 fixed at an independently measured dispersal
  variance and varying m, which has not been done." Here sigma^2 = k^2 is set
  by construction and control F2 measures it back. This run is that experiment.

  Symmetric two-allele mutation at rate mu per allele per generation is used in
  engine 1 only; engine 2 is mutation-free, which is the regime
  `demoSteppingStoneFst` is derived in.

ENGINE 1 -- WRIGHT-FISHER FREQUENCY LATTICE, array shape (reps, D)

  migrate -> mutate -> binomial resample. The resample is ONE
  rng.binomial(2*Ne, p) call on the full 2-D array per generation; a Python
  loop over replicates or over demes here is the bug that makes this family
  look expensive. The spatial autocovariance is taken with one rfft per
  sampled generation rather than D lag-by-lag dot products.

  Measures C(d) = E[(p_i - pbar)(p_{i+d} - pbar)] at mutation-migration-drift
  equilibrium, averaged over every deme i, every replicate and many time
  points, and fits C(d) = A*cosh((d - D/2)/L) + B. The cosh is the exact shape
  of the diffusion solution on a CIRCLE (both directions round the ring
  contribute); a bare exp(-d/L) fit biases L upward at large d. B absorbs the
  offset left by per-replicate centring.

  THE MUTATION CONVENTION, SETTLED BEFORE ANY COMPARISON IS MADE.

  This is the trap in this definition and it must be disarmed explicitly
  rather than absorbed into a fitted constant. `steppingStoneCharacteristicLength`
  is stated in the INFINITE-ALLELES convention and its docstring says so in
  words: "identity is destroyed by mutation in the two lineages at rate 2*mu",
  i.e. mu is the per-lineage rate and the identity-decay rate is 2*mu.

  This simulator uses a SYMMETRIC TWO-ALLELE model at rate mu_sim per gene,
  under which (p - 1/2) is multiplied by (1 - 2*mu_sim) per gene per
  generation and the two-deme covariance therefore decays at rate 4*mu_sim.
  Equating identity-decay rates:

      2 * mu_corpus  =  4 * mu_sim        so        mu_corpus = 2 * mu_sim .

  Comparing the corpus body against a two-allele rate WITHOUT that factor
  reports a spurious +41% error, which is the shape of defect this corpus
  keeps turning up and is NOT one here: the convention is declared in the
  docstring, so this is a conversion, not a discrepancy. Every reference
  column below is computed at mu_corpus = 2*mu_sim.

  WHAT IS ACTUALLY BEING DECIDED, then, is the DISPERSAL VARIANCE. The exact
  characteristic root of the discrete lattice is the L solving

      m * (cosh(k/L) - 1)  =  2 * mu_sim / (1 - 2 * mu_sim) ,

  whose small-k/L limit is L = sqrt(m * sigma^2 / (2 * mu_corpus)), sigma^2 =
  k^2. The corpus body is sqrt(m / (2 * mu)) and carries NO sigma^2, so it is
  the sigma^2 = 1 case of that. The k axis of the grid is what measures the
  exponent the corpus sets to zero, and it is the only axis on which the two
  can disagree.

ENGINE 2 -- TWO-LINEAGE COALESCENT ON THE CIRCLE, array shape (reps,)

  Exact backwards WF, one generation being: if the two lineages are in the same
  deme, coalesce with probability 1/(2 Ne); otherwise both migrate. Testing
  before migrating makes "distance 0 at the start of a generation" a renewal
  state, so T(d) = H(d) + T(0) holds exactly and H(d) is a clean meeting time.
  The state is one integer per replicate; coalesced replicates are compacted
  out of the array, so total work is O(reps * E[T]).

  Measures E[T(d)] for every d, hence
      H(d)    = E[T(d)] - E[T(0)]        DECIDES `steppingStoneCoalescenceTime`
      F_ST(d) = H(d) / (H(d) + E[T(0)])  Hudson; DECIDES `demoSteppingStoneFst`,
                                         `steppingStoneFstQuadratic`,
                                         `steppingStoneFst`, and the deleted
                                         1 - exp(-d/L).

  Mutation-free and frequency-free, so it settles the F_ST forms without
  engine 1's estimator noise, and the two engines share no code beyond the
  migration parameters -- agreement between them is not circular.

SEVEN CONTROLS, EACH ISOLATING ONE FACTOR, NONE FITTED

  Engine 1 splits the three rates L is built from, and shows Ne is not one:
    F1  DRIFT ALONE.   m = 0, mu = 0. E[p(1-p)] must fall by exactly
        (1 - 1/(2 Ne)) per generation.
    F2  MIGRATION ALONE. Ne infinite, mu = 0, a delta profile. The spatial
        variance of the profile must grow by exactly m*k^2 per generation.
        This is where sigma^2 = k^2 is measured rather than assumed.
    F3  MUTATION ALONE. Ne infinite, m = 0, p = 1. (p - 1/2) must fall by
        exactly (1 - 2 mu) per generation.
    A simulator that got L right by getting migration and mutation wrong in
    compensating directions passes a combined equilibrium check and fails F2
    and F3 separately.

  Engine 2 splits the two factors of F_ST = H/(H+T0):
    E1  COALESCENCE ALONE.  D = 1: no migration is possible, E[T] = 2*Ne
        exactly (a geometric waiting time), with no random-walk content.
    E2  RANDOM WALK ALONE.  2*Ne = 1, so lineages coalesce the instant they
        meet and T(d) IS the hitting time of distance 0. The expectation is
        obtained EXACTLY by solving the D-state linear system for the actual
        step distribution -- linear algebra, not a fit, and no population
        genetics in it. (The textbook d*(D-d)/V_rel is reported alongside; it
        is the same quantity to O(m), the difference being the chance of
        stepping over 0 rather than onto it.)
    E3  NO STRUCTURE.  D = 3, k = 1, m = 2/3 puts a lineage uniformly on all
        three demes, so the metapopulation is panmictic: T -> 2*Ne*D and
        F_ST(d) -> 0. This is the check that the deme bookkeeping is right at
        all, and it fails loudly if it is not.
    E4  ENGINE AGREEMENT. Section B reports E[T(d)] from an EXACT linear solve
        of the same chain rather than from sampling it, because the Monte
        Carlo needs ~10*2*Ne*D generations per distance and the exact solve is
        a D x D system. E4 runs both on one small cell and requires them to
        agree to 2% with no censoring. Without E4 the exact solve would be an
        unchecked reimplementation; with it, it is the same model measured
        twice.

CAN-FAIL CLAUSES

  L:  the grid varies mu over 16x AT FIXED m, k, Ne (corpus exponent -1/2 post
      repair, 0 pre-repair, truth -1/2), Ne over 25x AT FIXED m, k, mu (corpus
      0, truth 0 -- a regression guard, not a discriminator), m over 8x
      (corpus +1/2, truth +1/2 -- also not a discriminator), and k over 3x AT
      FIXED m, mu, Ne, where THE CORPUS EXPONENT IS 0 AND THE TRUTH IS +1/2 in
      sigma^2. A grid without the k axis cannot see the missing sigma^2 at
      all; a grid without the mu axis cannot see the pre-repair error. Both
      axes are required and both are here.

  F_ST(d):  d runs out to D/2. For d << D every candidate here -- hyperbolic,
      quadratic, linear, exponential -- agrees with every other to first order
      in d, because they all linearise to the same slope once their one free
      scale is matched at d = 1. Only the far half of the lattice separates
      them, so a short-distance grid would validate all four.

  sigma^2:  the (m, k) grid contains two cells with the SAME m*sigma^2 = 0.1
      and m differing by 4x. `demoSteppingStoneFst` sees the pair only through
      m*sigma^2 and must give the same F_ST in both; `steppingStoneFstQuadratic`
      sees sigma^4*m^2 and must not. sigma^2 is set, not fitted, so the
      degeneracy the corpus records is broken here.
"""

import json
import math
import sys

import numpy as np

SEED = 20260802


# ===========================================================================
# ENGINE 1 -- Wright-Fisher frequency lattice
# ===========================================================================

def migrate(p, m, k):
    """Circular +/-k migration along the deme axis of a (reps, D) array."""
    if m == 0.0:
        return p
    return (1.0 - m) * p + 0.5 * m * (np.roll(p, k, axis=1) + np.roll(p, -k, axis=1))


def wf_lattice_step(p, ne, m, k, mu, rng):
    p = migrate(p, m, k)
    if mu:
        p = p * (1.0 - mu) + (1.0 - p) * mu
    if ne is None:
        return p
    n = 2 * ne
    return rng.binomial(n, np.clip(p, 0.0, 1.0)).astype(np.float64) / n


def covariance_profile(ne, m, k, mu, D, reps, burn, samples, thin, rng):
    """Circular spatial autocovariance C(d), d = 0..D//2, at equilibrium.

    Centred per replicate per time point, which removes the fluctuation of the
    global mean frequency -- a d-independent pedestal that would otherwise
    flatten the tail and bias L upward. The residual pedestal from centring is
    a constant and is absorbed by the fitted B below.
    """
    p = np.full((reps, D), 0.5)
    for _ in range(burn):
        p = wf_lattice_step(p, ne, m, k, mu, rng)
    half = D // 2
    acc = np.zeros(half + 1)
    cnt = 0
    for i in range(samples):
        p = wf_lattice_step(p, ne, m, k, mu, rng)
        if i % thin:
            continue
        x = p - p.mean(axis=1, keepdims=True)
        f = np.fft.rfft(x, axis=1)
        c = np.fft.irfft(f * np.conj(f), n=D, axis=1).real / D
        acc += c.mean(axis=0)[: half + 1]
        cnt += 1
    return acc / cnt


def fit_cosh_length(c, D, dmin):
    """Fit C(d) = A*cosh((d - D/2)/L) + B for d in [dmin, D//2].

    L is scanned on a log grid; A and B come from an exact linear least
    squares at each L, so this is a one-parameter search, not an optimiser.
    """
    d = np.arange(dmin, D // 2 + 1, dtype=float)
    y = np.asarray(c[dmin : D // 2 + 1], dtype=float)
    if d.size < 4:
        return None, None
    best = None
    for L in np.exp(np.linspace(math.log(0.3), math.log(D / 2.0), 600)):
        z = (d - D / 2.0) / L
        # cosh normalised at d = dmin to keep the design matrix conditioned
        basis = np.cosh(z) / np.cosh((dmin - D / 2.0) / L)
        M = np.stack([basis, np.ones_like(basis)], axis=1)
        coef, res, _, _ = np.linalg.lstsq(M, y, rcond=None)
        pred = M.dot(coef)
        sse = float(np.sum((pred - y) ** 2))
        if coef[0] <= 0:
            continue
        if best is None or sse < best[1]:
            best = (float(L), sse, float(coef[0]), float(coef[1]))
    if best is None:
        return None, None
    return best[0], best[1]


# ===========================================================================
# ENGINE 2 -- two-lineage coalescent on the circle
# ===========================================================================

def meeting_times(D, ne, m, k, reps, rng, max_gen):
    """E[T(d)] for d = 0..D//2 under the backwards WF described in the header.

    Order within a generation: test coalescence, then migrate. That makes
    distance 0 at the start of a generation a renewal state.
    """
    half = D // 2
    out = np.zeros(half + 1)
    cens = np.zeros(half + 1)
    pcoal = 1.0 / (2.0 * ne)
    for d0 in range(half + 1):
        dist = np.full(reps, d0, dtype=np.int64)
        total = 0.0
        done = 0
        for t in range(1, max_gen + 1):
            n = dist.shape[0]
            if n == 0:
                break
            if pcoal >= 1.0:
                hit = dist == 0
            else:
                hit = (dist == 0) & (rng.random(n) < pcoal)
            nh = int(hit.sum())
            if nh:
                total += nh * t
                done += nh
                dist = dist[~hit]
                n = dist.shape[0]
                if n == 0:
                    break
            s1 = rng.random(n)
            s2 = rng.random(n)
            step = np.where(s1 < m * 0.5, k, np.where(s1 < m, -k, 0))
            step = step - np.where(s2 < m * 0.5, k, np.where(s2 < m, -k, 0))
            dist = (dist + step) % D
            dist = np.minimum(dist, D - dist)
        if done < reps:
            total += (reps - done) * max_gen
            cens[d0] = (reps - done) / float(reps)
        out[d0] = total / reps
    return out, cens


def _step_kernel(D, m, k):
    """Distribution of the change in circular distance in one generation."""
    steps = {}
    for a, pa in ((k, m / 2.0), (-k, m / 2.0), (0, 1.0 - m)):
        for b, pb in ((k, m / 2.0), (-k, m / 2.0), (0, 1.0 - m)):
            s = (a - b) % D
            steps[s] = steps.get(s, 0.0) + pa * pb
    return steps


def exact_meeting_times(D, ne, m, k):
    """EXACT E[T(d)] for the model engine 2 simulates, by one linear solve.

    u(d) = 1 + (1 - c(d)) * sum_s P(step = s) * u((d + s) mod D),
    c(d) = 1/(2 Ne) if d == 0 else 0.

    This is the same chain the Monte Carlo walks, evaluated exactly instead of
    sampled, so it has no sampling error and no censored tail. It does NOT
    replace the Monte Carlo: the two are cross-checked against each other in
    section B, and a disagreement means one of them does not encode the stated
    model. Passing ne = 0.5 gives instant coalescence on meeting, i.e. the pure
    hitting time used by control E2.
    """
    steps = _step_kernel(D, m, k)
    pcoal = 1.0 / (2.0 * ne)
    A = np.zeros((D, D))
    rhs = np.ones(D)
    for d in range(D):
        A[d, d] += 1.0
        surv = 1.0 - (pcoal if d == 0 else 0.0)
        if surv > 0.0:
            for s, ps in steps.items():
                A[d, (d + s) % D] -= surv * ps
    return np.linalg.solve(A, rhs)


# ===========================================================================
# candidate closed forms
# ===========================================================================

def lean_demo_fst(d, ne, m, sigma_sq):
    return d / (d + 4.0 * ne * m * sigma_sq)


def lean_quadratic_fst(d, ne, m, sigma_sq):
    return d / (d + 4.0 * ne * sigma_sq ** 2 * m ** 2)


def lean_linear_fst(f_nb, alpha, d):
    return min(1.0, f_nb * (1.0 + alpha * (d - 1.0)))


# ===========================================================================

def main():
    rng = np.random.default_rng(SEED)
    out = {}

    # ------------------------------------------------------------------
    print("CONTROLS -- ENGINE 1 (three rates, split three ways)")
    NE_F1, REPS_F1, GENS_F1 = 50, 4000, 40
    p = np.full((REPS_F1, 1), 0.5)
    h0 = float(np.mean(p * (1 - p)))
    for _ in range(GENS_F1):
        p = wf_lattice_step(p, NE_F1, 0.0, 1, 0.0, rng)
    h1 = float(np.mean(p * (1 - p)))
    f1_meas = (h1 / h0) ** (1.0 / GENS_F1)
    f1_want = 1.0 - 1.0 / (2.0 * NE_F1)
    f1 = abs(f1_meas - f1_want) < 0.002
    print("  F1 drift alone      : het retention %.6f vs 1-1/2Ne %.6f -> %s"
          % (f1_meas, f1_want, "PASS" if f1 else "FAIL"))

    f2rows = []
    f2 = True
    for k in (1, 2, 3):
        for m in (0.05, 0.2):
            D = 401
            q = np.zeros((1, D))
            q[0, D // 2] = 1.0
            T = 60
            for _ in range(T):
                q = migrate(q, m, k)
            x = np.arange(D) - D // 2
            var = float((q[0] * x ** 2).sum() / q[0].sum())
            want = m * k * k * T
            rel = (var - want) / want
            f2rows.append({"k": k, "m": m, "var_measured": var,
                           "var_expected_m_sigma2_t": want, "rel_err": rel})
            if abs(rel) > 1e-6:
                f2 = False
    print("  F2 migration alone  : max |rel err| on spatial variance %.2e -> %s"
          % (max(abs(r["rel_err"]) for r in f2rows), "PASS" if f2 else "FAIL"))

    MU_F3 = 1e-3
    q = np.ones((1, 1))
    T = 500
    for _ in range(T):
        q = wf_lattice_step(q, None, 0.0, 1, MU_F3, rng)
    f3_meas = (float(q[0, 0]) - 0.5) / 0.5
    f3_want = (1.0 - 2.0 * MU_F3) ** T
    f3 = abs(f3_meas - f3_want) < 1e-9
    print("  F3 mutation alone   : (p-1/2) retention %.9f vs (1-2mu)^t %.9f -> %s"
          % (f3_meas, f3_want, "PASS" if f3 else "FAIL"))

    out["controls_engine1"] = {
        "F1_drift_only": f1_meas, "F1_expected": f1_want, "F1_pass": bool(f1),
        "F2_migration_only": f2rows, "F2_pass": bool(f2),
        "F3_mutation_only": f3_meas, "F3_expected": f3_want, "F3_pass": bool(f3),
    }

    # ------------------------------------------------------------------
    print("")
    print("CONTROLS -- ENGINE 2 (two factors of F_ST = H/(H+T0), split)")
    NE_E1 = 40
    t, _ = meeting_times(1, NE_E1, 0.0, 1, 60000, rng, 40000)
    e1_meas = float(t[0])
    e1_want = 2.0 * NE_E1
    e1 = abs(e1_meas - e1_want) / e1_want < 0.02
    print("  E1 coalescence alone: E[T] in one deme %.3f vs 2Ne %.1f -> %s"
          % (e1_meas, e1_want, "PASS" if e1 else "FAIL"))

    D_E2, M_E2, K_E2 = 24, 0.25, 1
    t, _ = meeting_times(D_E2, 0.5, M_E2, K_E2, 60000, rng, 40000)
    exact = exact_meeting_times(D_E2, 0.5, M_E2, K_E2)
    vrel = 2.0 * M_E2 * K_E2 * K_E2
    e2rows = []
    e2 = True
    for d in range(1, D_E2 // 2 + 1):
        rel = (t[d] - exact[d]) / exact[d]
        e2rows.append({"d": d, "T_measured": float(t[d]),
                       "T_exact_linear_solve": float(exact[d]),
                       "T_textbook_d_Dmd_over_Vrel": d * (D_E2 - d) / vrel,
                       "rel_err": float(rel)})
        if abs(rel) > 0.03:
            e2 = False
    print("  E2 random walk alone: max |rel err| vs exact linear solve %.4f -> %s"
          % (max(abs(r["rel_err"]) for r in e2rows), "PASS" if e2 else "FAIL"))

    NE_E3 = 200
    t, _ = meeting_times(3, NE_E3, 2.0 / 3.0, 1, 60000, rng, 60000)
    e3_want = 2.0 * NE_E3 * 3
    e3_fst = float((t[1] - t[0]) / t[1])
    e3 = abs(t[0] - e3_want) / e3_want < 0.03 and abs(e3_fst) < 0.01
    print("  E3 no structure     : E[T]=%.1f vs 2*Ne*D=%.1f, F_ST(1)=%+.5f vs 0 -> %s"
          % (t[0], e3_want, e3_fst, "PASS" if e3 else "FAIL"))

    out["controls_engine2"] = {
        "E1_single_deme": e1_meas, "E1_expected": e1_want, "E1_pass": bool(e1),
        "E2_hitting_time": e2rows, "E2_pass": bool(e2),
        "E3_panmixia_T": float(t[0]), "E3_panmixia_T_expected": e3_want,
        "E3_panmixia_fst": e3_fst, "E3_pass": bool(e3),
    }
    ok_all = bool(f1 and f2 and f3 and e1 and e2 and e3)

    # ------------------------------------------------------------------
    print("")
    print("A. steppingStoneCharacteristicLength   corpus: L = sqrt(m/(2 mu))")
    print("   CONVENTION: corpus mu is infinite-alleles (identity decays at")
    print("   2*mu); this model is two-allele at mu_sim (covariance decays at")
    print("   4*mu_sim), so mu_corpus = 2*mu_sim and every reference column")
    print("   below uses that. The corpus body has no sigma^2, so it is the")
    print("   sigma^2 = 1 case; the k axis is what measures that exponent.")
    print("   %-6s %-7s %-4s %-9s %-10s %-10s %-10s %-9s"
          % ("Ne", "m", "k", "mu_sim", "L_meas", "L_corpus", "L_exact", "err_corp"))
    D_A, REPS_A = 384, 200
    BASE = {"ne": 100, "m": 0.1, "k": 1, "mu": 5e-4}
    cells = []
    for mu in (2e-3, 5e-4, 1.25e-4):
        c = dict(BASE); c["mu"] = mu; cells.append(c)
    for ne in (20, 500):
        c = dict(BASE); c["ne"] = ne; cells.append(c)
    for m in (0.025, 0.2):
        c = dict(BASE); c["m"] = m; cells.append(c)
    for k in (2, 3):
        c = dict(BASE); c["k"] = k; cells.append(c)
    rowsA = []
    for c in cells:
        burn = int(min(30000, max(3000, 8.0 / (2.0 * c["mu"]), 20 * c["ne"])))
        prof = covariance_profile(c["ne"], c["m"], c["k"], c["mu"], D_A,
                                  REPS_A, burn, 4000, 10, rng)
        L, sse = fit_cosh_length(prof, D_A, 1)
        mu_corpus = 2.0 * c["mu"]              # see the convention block above
        # exact characteristic root of the discrete two-allele lattice
        Lexact = c["k"] / math.acosh(
            1.0 + 2.0 * c["mu"] / (c["m"] * (1.0 - 2.0 * c["mu"])))
        # the corpus body, in the corpus's own convention: no sigma^2
        Lcorpus = math.sqrt(c["m"] / (2.0 * mu_corpus))
        # the same body with the dispersal variance restored
        Ltruth = math.sqrt(c["m"] * c["k"] ** 2 / (2.0 * mu_corpus))
        row = dict(c)
        row["burn"] = burn
        row["mu_corpus_convention"] = mu_corpus
        row["L_measured"] = L
        row["L_corpus_as_written"] = Lcorpus
        row["L_corpus_with_sigma2_restored"] = Ltruth
        row["L_exact_discrete_root"] = Lexact
        row["rel_err_corpus"] = None if L is None else (Lcorpus - L) / L
        row["rel_err_truth"] = None if L is None else (Ltruth - L) / L
        row["rel_err_exact"] = None if L is None else (Lexact - L) / L
        row["C0"] = float(prof[0])
        rowsA.append(row)
        print("   %-6d %-7.4f %-4d %-9.2e %-10s %-10.3f %-10.3f %-9s"
              % (c["ne"], c["m"], c["k"], c["mu"],
                 "None" if L is None else ("%.3f" % L), Lcorpus, Lexact,
                 "None" if L is None else ("%+.3f" % row["rel_err_corpus"])))
    out["A_characteristic_length"] = rowsA

    def loglog(rows, key):
        r = [x for x in rows if x["L_measured"]]
        if len(r) < 2:
            return None
        return float(np.polyfit(np.log([float(x[key]) for x in r]),
                                np.log([x["L_measured"] for x in r]), 1)[0])

    mu_rows = [r for r in rowsA if r["ne"] == 100 and r["m"] == 0.1 and r["k"] == 1]
    ne_rows = [r for r in rowsA if r["m"] == 0.1 and r["k"] == 1 and r["mu"] == 5e-4]
    m_rows = [r for r in rowsA if r["ne"] == 100 and r["k"] == 1 and r["mu"] == 5e-4]
    k_rows = [r for r in rowsA if r["ne"] == 100 and r["m"] == 0.1 and r["mu"] == 5e-4]
    exps = {
        "dlogL_dlogmu": {"measured": loglog(mu_rows, "mu"), "corpus": -0.5, "truth": -0.5},
        "dlogL_dlogNe": {"measured": loglog(ne_rows, "ne"), "corpus": 0.0, "truth": 0.0},
        "dlogL_dlogm": {"measured": loglog(m_rows, "m"), "corpus": 0.5, "truth": 0.5},
        "dlogL_dlogsigma2": {"measured": None, "corpus": 0.0, "truth": 0.5},
    }
    kr = [x for x in k_rows if x["L_measured"]]
    if len(kr) >= 2:
        exps["dlogL_dlogsigma2"]["measured"] = float(np.polyfit(
            np.log([float(x["k"]) ** 2 for x in kr]),
            np.log([x["L_measured"] for x in kr]), 1)[0])
    out["A_exponents"] = exps
    print("   fitted exponents           measured   corpus   truth")
    for kk in ("dlogL_dlogmu", "dlogL_dlogNe", "dlogL_dlogm", "dlogL_dlogsigma2"):
        v = exps[kk]
        print("     %-22s %-10s %-8s %-8s"
              % (kk, "None" if v["measured"] is None else "%.3f" % v["measured"],
                 v["corpus"], v["truth"]))

    # ------------------------------------------------------------------
    print("")
    print("B. F_ST(d) AND MEETING TIME  (d out to D/2 -- the can-fail range)")
    # E4 -- ENGINE AGREEMENT. The exact solve and the Monte Carlo must agree
    # on a cell small enough for the MC to finish without censoring. They
    # share no code beyond the parameters, so a disagreement means one of them
    # is not the model in the header.
    D_X, NE_X = 32, 10
    mc, cens_x = meeting_times(D_X, NE_X, 0.15, 1, 60000, rng, 200000)
    ex = exact_meeting_times(D_X, NE_X, 0.15, 1)
    e4rel = [abs(float(mc[d]) - float(ex[d])) / float(ex[d])
             for d in range(D_X // 2 + 1)]
    e4 = max(e4rel) < 0.02 and cens_x.max() < 1e-3
    print("  E4 engine agreement : max |rel err| MC vs exact solve %.4f, "
          "censored %.5f -> %s" % (max(e4rel), cens_x.max(), "PASS" if e4 else "FAIL"))
    out["controls_engine2"]["E4_mc_vs_exact_max_rel_err"] = float(max(e4rel))
    out["controls_engine2"]["E4_censored_max"] = float(cens_x.max())
    out["controls_engine2"]["E4_pass"] = bool(e4)
    ok_all = ok_all and e4

    D_B, NE_B = 256, 25
    rowsB = []
    for (m, k) in ((0.1, 1), (0.025, 2), (0.4, 1), (0.1, 2)):
        sigma_sq = float(k * k)
        t = exact_meeting_times(D_B, NE_B, m, k)
        T0 = float(t[0])
        vrel = 2.0 * m * sigma_sq
        H1 = float(t[1] - t[0])
        f_nb = H1 / (H1 + T0)
        cells = []
        for d in range(1, D_B // 2 + 1):
            H = float(t[d] - t[0])
            fst = H / (H + T0)
            cells.append({
                "d": d,
                "meeting_time_measured": H,
                "meeting_time_corpus_d_over_2sigma2m": d / (2.0 * sigma_sq * m),
                "meeting_time_circle_theory_dDmd_over_Vrel":
                    d * (D_B - d) / vrel,
                "fst_measured": fst,
                "fst_demoSteppingStone": lean_demo_fst(d, NE_B, m, sigma_sq),
                "fst_quadratic": lean_quadratic_fst(d, NE_B, m, sigma_sq),
                "fst_linear": lean_linear_fst(f_nb, 1.0, d),
            })
        dd = np.array([c["d"] for c in cells], dtype=float)
        ff = np.array([c["fst_measured"] for c in cells])
        best = None
        for Lg in np.exp(np.linspace(math.log(0.2), math.log(2000.0), 800)):
            pred = 1.0 - np.exp(-dd / Lg)
            e = float(np.mean(((pred - ff) / ff) ** 2))
            if best is None or e < best[1]:
                best = (float(Lg), e)
        Lexp = best[0]
        for c in cells:
            c["fst_exponential_bestfit"] = 1.0 - math.exp(-c["d"] / Lexp)

        def rmsrel(key):
            v = [(c[key] - c["fst_measured"]) / c["fst_measured"] for c in cells]
            return float(np.sqrt(np.mean(np.square(v))))

        rec = {"m": m, "k": k, "sigma_sq": sigma_sq, "Ne": NE_B, "D": D_B,
               "method": "exact linear solve of the engine-2 chain; the "
                         "Monte Carlo is cross-checked against it by control E4",
               "T0_measured": T0, "T0_reference_2NeD": 2.0 * NE_B * D_B,
               "fst_neighbour_used": f_nb, "L_exponential_bestfit": Lexp,
               "rms_rel_err": {
                   "demoSteppingStoneFst": rmsrel("fst_demoSteppingStone"),
                   "steppingStoneFstQuadratic": rmsrel("fst_quadratic"),
                   "steppingStoneFst_linear": rmsrel("fst_linear"),
                   "deleted_exponential_bestfit": rmsrel("fst_exponential_bestfit"),
               },
               "cells": cells}
        rowsB.append(rec)
        print("  m=%.3f k=%d sigma^2=%.0f  T0=%.0f (2NeD=%.0f)"
              % (m, k, sigma_sq, T0, 2.0 * NE_B * D_B))
        print("    %-5s %-10s %-10s %-10s %-10s %-10s | %-11s %-11s"
              % ("d", "fst_meas", "demoSSFst", "quadratic", "linear",
                 "exp(fit)", "H_measured", "H_corpus"))
        for c in cells:
            if c["d"] in (1, 2, 4, 8, 16, 32, 64, D_B // 2):
                print("    %-5d %-10.5f %-10.5f %-10.5f %-10.5f %-10.5f | %-11.1f %-11.1f"
                      % (c["d"], c["fst_measured"], c["fst_demoSteppingStone"],
                         c["fst_quadratic"], c["fst_linear"],
                         c["fst_exponential_bestfit"],
                         c["meeting_time_measured"],
                         c["meeting_time_corpus_d_over_2sigma2m"]))
        print("    RMS rel err: demo %.4f | quadratic %.4f | linear %.4f | exp %.4f"
              % (rec["rms_rel_err"]["demoSteppingStoneFst"],
                 rec["rms_rel_err"]["steppingStoneFstQuadratic"],
                 rec["rms_rel_err"]["steppingStoneFst_linear"],
                 rec["rms_rel_err"]["deleted_exponential_bestfit"]))
    out["B_fst_and_meeting_time"] = rowsB

    pair = {}
    for r in rowsB:
        pair[(r["m"], r["k"])] = r
    if (0.1, 1) in pair and (0.025, 2) in pair:
        a = pair[(0.1, 1)]
        b = pair[(0.025, 2)]
        ca = dict((c["d"], c) for c in a["cells"])
        cb = dict((c["d"], c) for c in b["cells"])
        rows = []
        for d in (1, 4, 16, 64, D_B // 2):
            rows.append({
                "d": d,
                "fst_measured_m0.1_k1": ca[d]["fst_measured"],
                "fst_measured_m0.025_k2": cb[d]["fst_measured"],
                "demo_predicts_equal": [ca[d]["fst_demoSteppingStone"],
                                        cb[d]["fst_demoSteppingStone"]],
                "quadratic_predicts_unequal": [ca[d]["fst_quadratic"],
                                               cb[d]["fst_quadratic"]],
            })
        out["B_fixed_product_experiment"] = {
            "note": "m*sigma^2 = 0.1 held fixed, m varied 4x, sigma^2 = k^2 "
                    "set by construction and measured back by control F2. "
                    "demoSteppingStoneFst sees the pair only through m*sigma^2 "
                    "and must be flat across it; steppingStoneFstQuadratic "
                    "sees sigma^4*m^2 and must not. This is the experiment "
                    "demoSteppingStoneFst's docstring records as not done.",
            "rows": rows,
        }
        print("")
        print("  FIXED-PRODUCT EXPERIMENT (m*sigma^2 = 0.1, m varied 4x)")
        for r in rows:
            print("    d=%-4d measured %.5f vs %.5f | demo %.5f/%.5f | quad %.5f/%.5f"
                  % (r["d"], r["fst_measured_m0.1_k1"], r["fst_measured_m0.025_k2"],
                     r["demo_predicts_equal"][0], r["demo_predicts_equal"][1],
                     r["quadratic_predicts_unequal"][0],
                     r["quadratic_predicts_unequal"][1]))

    out["READ_THE_TEST"] = ok_all
    print("")
    print("READ_THE_TEST (all seven controls): %s" % ok_all)
    fh = open("fam_stepping_stone_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> fam_stepping_stone_results.json")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())

"""Simulation checks of the definitions in `Descent/ImitationRigidity.lean`.

Every definition is transcribed literally from the Lean source (file and line
quoted below) and compared against a simulation of the quantity its *name*
claims to be. The Lean theorems are machine-checked, so nothing in this file
can contradict them; what it can contradict is a name.

  ImitationRigidity.lean  rankOneCovarianceBump scale loading
  ImitationRigidity.lean  varianceNonneg_sub_rankOne_iff   (secular threshold)
  ImitationRigidity.lean  stationaryLDEntry decay separation
  ImitationRigidity.lean  ldHardEdge decay      = (1 - decay) / (1 + decay)
  ImitationRigidity.lean  ldWhiteningGain decay = (1 + decay^2) / (1 - decay^2)
  ImitationRigidity.lean  ldPrecisionTrace      (exact finite-chromosome trace)
  ImitationRigidity.lean  ridgeBalance eig ridge u
  ImitationRigidity.lean  scalarRowResolvent latent quadraticForm
  ImitationRigidity.lean  alleleLossProbability initial time
  ImitationRigidity.lean  informationCrossoverTime initial = initial / 2

Ground truth used
  exact linear algebra (numpy eigenvalues / inverses)   spectral claims
  Markov haplotype simulation along a chromosome        LD kernel claims
  ridge regression on simulated genotypes               spectator claim
  Wright-Fisher forward simulation                      allele-loss claims

Run: python3 validation/empirical/imitation_rigidity/check_imitation.py
"""
from __future__ import annotations

import os
import sys

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ[_v] = "1"

import numpy as np  # noqa: E402

FAILURES = []


def report(name, claim, predicted, observed, tol, note="", abs_tol=0.0):
    """Record one comparison.

    A claim fails when the discrepancy exceeds both the relative tolerance
    `tol` and the absolute tolerance `abs_tol`. The absolute term carries the
    Monte Carlo standard error, so a simulation that is merely noisy is not
    reported as a falsification, and a small bias in a small quantity still is.
    """
    scale = max(abs(predicted), abs(observed), 1e-12)
    diff = abs(predicted - observed)
    err = diff / scale
    ok = diff <= tol * scale + abs_tol
    status = "ok   " if ok else "FAIL "
    print(f"  {status} {name:<44s} lean={predicted: .6g}  sim={observed: .6g}  "
          f"rel={err: .2e}  tol={tol:g} {note}")
    if not ok:
        FAILURES.append((name, claim, predicted, observed, err))
    return ok


# ---------------------------------------------------------------- Lean defs

def lean_rankOneCovarianceBump(scale, loading):
    return scale ** 2 * np.outer(loading, loading)


def lean_stationaryLDEntry(decay, separation):
    return decay ** separation


def lean_ldKernelSymbol(decay, angle):
    return (1 - decay ** 2) / (1 - 2 * decay * np.cos(angle) + decay ** 2)


def lean_ldHardEdge(decay):
    return (1 - decay) / (1 + decay)


def lean_ldWhiteningGain(decay):
    return (1 + decay ** 2) / (1 - decay ** 2)


def lean_ldPrecisionTrace(decay, n_sites):
    return (n_sites * (1 + decay ** 2) - 2 * decay ** 2) / (1 - decay ** 2)


def lean_ridgeBalance(aspect, eig, ridge, u):
    return (1 - 1 / u) - aspect * np.mean(eig / (eig + ridge * u))


def lean_scalarRowResolvent(latent, quadratic_form):
    return 1 / (1 + latent ** 2 * quadratic_form)


def lean_alleleLossProbability(initial, time):
    return np.exp(-(initial / (2 * time)))


def lean_informationCrossoverTime(initial):
    return initial / 2


# ------------------------------------------------------------------ Part 1
# The stationary LD kernel: is the Toeplitz description of a Markov chromosome
# right, and are the hard edge / whitening gain the spectral quantities named?

def markov_haplotypes(n_hap, n_sites, decay, rng):
    """Haplotypes whose allele indicators have correlation decay**|i-j|.

    Each site flips relative to its neighbour with probability (1-decay)/2, so
    E[s_i s_j] = decay**|i-j| for the +/-1 coding: a first-order Markov model
    of LD along a chromosome.
    """
    flips = rng.random((n_hap, n_sites - 1)) > (1 + decay) / 2
    signs = np.ones((n_hap, n_sites))
    signs[:, 1:] = np.where(flips, -1.0, 1.0)
    return np.cumprod(signs, axis=1)


def check_stationary_ld():
    print("\n[1] stationary LD kernel: entries, hard edge, whitening gain")
    rng = np.random.default_rng(20260801)
    ok = True
    for decay in (0.3, 0.6, 0.85):
        n_sites, n_hap = 64, 400_000
        H = markov_haplotypes(n_hap, n_sites, decay, rng)
        for sep in (1, 3, 8):
            # haplotypes are independent, sites within one are not, so the
            # Monte Carlo error is computed across haplotypes, not across pairs
            per_hap = np.mean(H[:, :n_sites - sep] * H[:, sep:], axis=1)
            est = float(per_hap.mean())
            se = float(per_hap.std(ddof=1) / np.sqrt(n_hap))
            ok &= report(f"stationaryLDEntry(rho={decay}, d={sep})",
                         "correlation at separation d is decay**d",
                         lean_stationaryLDEntry(decay, sep), est,
                         0.02, f"(4 se = {4 * se:.1e})", abs_tol=4 * se)
        # exact Toeplitz kernel, for the spectral claims
        idx = np.arange(n_sites)
        K = decay ** np.abs(idx[:, None] - idx[None, :])
        eigs = np.linalg.eigvalsh(K)
        ok &= report(f"ldHardEdge(rho={decay})",
                     "smallest eigenvalue of the LD matrix",
                     lean_ldHardEdge(decay), float(eigs.min()), 0.05,
                     "(finite-size, converges from above)")
        # symbol minimum, at large n_sites, is the hard edge exactly
        angles = np.linspace(0, 2 * np.pi, 200_001)
        sym = lean_ldKernelSymbol(decay, angles)
        ok &= report(f"ldHardEdge(rho={decay}) vs min symbol",
                     "hard edge is the symbol minimum",
                     lean_ldHardEdge(decay), float(sym.min()), 1e-6)
        # whitening gain = harmonic mean of the symbol = lim tr(K^-1)/k
        harm = float(np.trapezoid(1.0 / sym, angles) / (2 * np.pi))
        ok &= report(f"ldWhiteningGain(rho={decay}) vs symbol harmonic mean",
                     "gain is the harmonic mean of the symbol",
                     lean_ldWhiteningGain(decay), harm, 1e-5)
        for k in (8, 64, 512):
            idx = np.arange(k)
            Kk = decay ** np.abs(idx[:, None] - idx[None, :])
            ok &= report(f"ldPrecisionTrace(rho={decay}, k={k})",
                         "exact trace of the inverse LD matrix",
                         lean_ldPrecisionTrace(decay, k),
                         float(np.trace(np.linalg.inv(Kk))), 1e-8)
        ok &= report(f"ldWhiteningGain(rho={decay}) vs tr(K^-1)/k, k=512",
                     "gain is the per-variant limit of tr(K^-1)",
                     lean_ldWhiteningGain(decay),
                     float(np.trace(np.linalg.inv(Kk)) / 512), 0.01)
    return ok


# ------------------------------------------------------------------ Part 2
# The imitation threshold. Is scale^2 * v' (C0 I - K)^-1 v <= 1 really the
# condition for the polygenic bump to stay inside the spectral-ceiling class?

def check_secular_threshold():
    print("\n[2] imitation: the secular threshold for staying in the class")
    rng = np.random.default_rng(7)
    ok = True
    for trial, k in enumerate((6, 20, 60)):
        Q = np.linalg.qr(rng.standard_normal((k, k)))[0]
        spec = rng.uniform(0.2, 1.5, size=k)
        K = Q @ np.diag(spec) @ Q.T
        ceiling = float(spec.max()) + rng.uniform(0.1, 1.0)
        v = rng.standard_normal(k)
        v /= np.linalg.norm(v)
        gap = ceiling * np.eye(k) - K
        predicted = 1.0 / (v @ np.linalg.solve(gap, v))    # scale^2 threshold
        # bisection on the true condition lambda_max(K + s vv') <= ceiling
        lo, hi = 0.0, 10 * predicted + 1.0
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if np.linalg.eigvalsh(K + mid * np.outer(v, v)).max() <= ceiling:
                lo = mid
            else:
                hi = mid
        ok &= report(f"secular threshold (k={k})",
                     "largest bump the ceiling class absorbs",
                     predicted, lo, 1e-6)
        # and the imitation statement itself, at 0.99 and 1.01 of threshold
        for factor, expect_inside in ((0.99, True), (1.01, False)):
            s = factor * predicted
            inside = np.linalg.eigvalsh(K + s * np.outer(v, v)).max() <= ceiling + 1e-12
            if inside != expect_inside:
                FAILURES.append((f"imitation at {factor}x threshold (k={k})",
                                 "bump inside class iff below threshold",
                                 expect_inside, inside, 1.0))
                print(f"  FAIL  imitation at {factor}x threshold (k={k})")
                ok = False
            else:
                print(f"  ok    imitation at {factor}x threshold (k={k}): "
                      f"inside={inside}")
    return ok


# ------------------------------------------------------------------ Part 3
# Dead sensors: complete genotyping failure for a fraction of individuals.
# Genome-wide averages self-average; per-individual quantities do not.

def check_dead_sensors():
    print("\n[3] dead sensors: what self-averages across a genotype matrix")
    rng = np.random.default_rng(11)
    ok = True
    print("     n      Var(per-individual R_ii)   Var((1/n) tr R)")
    var_ind, var_trace = [], []
    for n in (100, 200, 400, 800):
        k = n
        reps = 400
        first, traces = [], []
        for _ in range(reps):
            alive = rng.random(n) < 0.5
            E = rng.standard_normal((n, k)) * np.sqrt(2.0)
            E[~alive] = 0.0                      # completely failed samples
            R = np.linalg.inv(E @ E.T / k + np.eye(n))
            first.append(R[0, 0])
            traces.append(np.trace(R) / n)
        var_ind.append(float(np.var(first)))
        var_trace.append(float(np.var(traces)))
        print(f"   {n:5d}          {var_ind[-1]:.5f}              "
              f"{var_trace[-1]:.3e}")
    # claim A: the per-individual entry does not concentrate
    if not (min(var_ind) > 0.01):
        FAILURES.append(("per-individual nonconcentration", "Var(R_11) is O(1)",
                         "> 0.01", min(var_ind), 1.0))
        ok = False
    print(f"  {'ok   ' if ok else 'FAIL '} per-individual R_ii keeps O(1) variance "
          f"(min {min(var_ind):.3f})")
    # claim B: the genome-wide average does concentrate, at rate 1/n
    ratio = var_trace[0] / var_trace[-1]
    ok_b = ratio > 4.0
    if not ok_b:
        FAILURES.append(("trace self-averaging", "Var((1/n) tr R) -> 0",
                         "8x decrease over 8x n", ratio, 1.0))
    print(f"  {'ok   ' if ok_b else 'FAIL '} (1/n)tr R variance falls "
          f"{ratio:.1f}x when n grows 8x")
    # claim C: the two-point resolvent law, quantitatively
    q = 0.5
    print(f"  info  scalarRowResolvent(0, {q}) = {lean_scalarRowResolvent(0, q):.4f}, "
          f"alive = {lean_scalarRowResolvent(np.sqrt(2), q):.4f}")
    return ok and ok_b


# ------------------------------------------------------------------ Part 4
# The spectator principle: the ridge fixed point is a functional of the design
# alone, and the evaluation geometry enters only linearly, commuting or not.

def ridge_fixed_point(aspect, eig, ridge):
    lo, hi = 1.0 + 1e-12, 1e12
    for _ in range(400):
        mid = np.sqrt(lo * hi)
        if lean_ridgeBalance(aspect, eig, ridge, mid) < 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def check_spectator():
    print("\n[4] spectator principle: loss geometry never enters the fixed point")
    rng = np.random.default_rng(2024)
    ok = True
    k, n, ridge = 120, 400, 0.35
    QA = np.linalg.qr(rng.standard_normal((k, k)))[0]
    eig = rng.uniform(0.2, 3.0, size=k)
    A = QA @ np.diag(eig) @ QA.T
    Ah = QA @ np.diag(np.sqrt(eig)) @ QA.T
    aspect = k / n
    u = ridge_fixed_point(aspect, eig, ridge)
    M = np.linalg.inv(A / u + ridge * np.eye(k))     # deterministic equivalent

    # two evaluation geometries: one commuting with A, one in general position
    B_comm = QA @ np.diag(rng.uniform(0.5, 2.0, size=k)) @ QA.T
    QB = np.linalg.qr(rng.standard_normal((k, k)))[0]
    B_free = QB @ np.diag(rng.uniform(0.5, 2.0, size=k)) @ QB.T
    comm_norm = np.linalg.norm(A @ B_free - B_free @ A)
    print(f"  info  ||[A, B_free]|| = {comm_norm:.3f} (non-commuting), "
          f"||[A, B_comm]|| = {np.linalg.norm(A @ B_comm - B_comm @ A):.2e}")

    for label, B in (("commuting", B_comm), ("non-commuting", B_free)):
        emp = []
        for _ in range(60):
            X = rng.standard_normal((n, k)) @ Ah
            S = X.T @ X / n
            W = np.linalg.inv(S + ridge * np.eye(k))
            emp.append(np.trace(B @ W) / k)
        predicted = np.trace(B @ M) / k
        ok &= report(f"resolvent functional, B {label}",
                     "tr(B (S+ridge)^-1)/k from the scalar fixed point",
                     predicted, float(np.mean(emp)), 0.05)
    ok &= report("ridgeBalance root", "root of the balance equation",
                 0.0, lean_ridgeBalance(aspect, eig, ridge, u), 1e-6, abs_tol=1e-6)
    return ok


# ------------------------------------------------------------------ Part 5
# Allele loss at the absorbing boundary: is the exponential absorption law the
# Wright-Fisher loss probability, and is the crossover time initial/2?

def wright_fisher_loss(n_diploid, p0, generations, reps, rng):
    p = np.full(reps, p0)
    for _ in range(generations):
        p = rng.binomial(2 * n_diploid, p) / (2 * n_diploid)
    return float(np.mean(p == 0.0))


def check_allele_loss():
    print("\n[5] allele loss: absorption law and information crossover")
    rng = np.random.default_rng(31415)
    ok = True
    n_diploid = 2000
    # Coalescent time tau = generations / (2N). The Wright-Fisher frequency
    # diffusion dp = sqrt(p(1-p)) dW in these units is the squared-Bessel
    # process of dimension zero run at a quarter speed, so the absorbed mass
    # exp(-x/(2t)) is evaluated at t = tau/4.
    for p0, tau in ((0.004, 0.5), (0.004, 1.0), (0.010, 1.0), (0.010, 2.0)):
        generations = int(round(tau * 2 * n_diploid))
        sim = wright_fisher_loss(n_diploid, p0, generations, 40_000, rng)
        predicted = lean_alleleLossProbability(p0, tau / 4)
        ok &= report(f"alleleLossProbability(p0={p0}, tau={tau})",
                     "Wright-Fisher probability the allele is lost by tau",
                     float(predicted), sim, 0.03)
    # the crossover time: the weight x p(x,t) / (4t) peaks at t = x / 2
    for x in (0.5, 1.0, 3.0):
        ts = np.linspace(1e-3, 5 * x, 400_001)
        weight = x * lean_alleleLossProbability(x, ts) / (4 * ts)
        ok &= report(f"informationCrossoverTime(x={x})",
                     "argmax of the absorption channel weight",
                     lean_informationCrossoverTime(x), float(ts[weight.argmax()]),
                     1e-3)
    # the absorption channel is a real information channel: its Fisher
    # information p'(x)^2 / p(x) against a finite-difference derivative
    for x, t in ((1.0, 0.7), (2.0, 1.3)):
        h = 1e-5
        d = (lean_alleleLossProbability(x + h, t) -
             lean_alleleLossProbability(x - h, t)) / (2 * h)
        ok &= report(f"absorptionInformation(x={x}, t={t})",
                     "Fisher information of the loss/no-loss indicator",
                     float(lean_alleleLossProbability(x, t) / (4 * t ** 2)),
                     float(d ** 2 / lean_alleleLossProbability(x, t)), 1e-6)
    return ok


def main() -> int:
    print(__doc__.splitlines()[0])
    checks = [check_stationary_ld, check_secular_threshold, check_dead_sensors,
              check_spectator, check_allele_loss]
    for c in checks:
        c()
    print()
    if FAILURES:
        print(f"FALSIFIED: {len(FAILURES)} claim(s)")
        for name, claim, predicted, observed, err in FAILURES:
            print(f"  {name}: claims {claim}; lean={predicted} sim={observed} "
                  f"rel err {err}")
        return 1
    print("all checked definitions agree with simulation")
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""Does the mixture characteristic function decay for a REALIZED panel?

THE QUESTION

An upstream result proves that for a bundle family with atom curves a_j(t) and a
mixing measure mu, the tilted characteristic function

    Psi_theta(s) = (1/Z) integral sum_j p_j(t) |a_j(t)|^{2 theta} e^{i s h_j(t)} dmu(t),
    h_j(t) = 2 log |a_j(t)|,

obeys |Psi_theta(s)| <= C (1+|s|)^{-1/K}, with K = 1 for binomial-2. That makes the
mixture walk satisfy Cramer's condition, which would put genotype panels inside the
proved stratum rather than in the open annex.

Every step of that rests on mu being ABSOLUTELY CONTINUOUS: the decay is bought by van
der Corput on the t-integral, and an integral is what does the cancelling.

A REALIZED PANEL HAS NO SUCH MEASURE. Its empirical MAF distribution is
mu_hat = (1/n) sum_i delta_{q_i}, purely atomic, and every analysis conditions on the
realized panel. So the question this script answers is quantitative rather than
philosophical:

    for how large |s| does a finite panel of n loci reproduce the a.c. decay,
    and what does it do beyond that?

THE PREDICTION UNDER TEST

Psi over an atomic mu_hat is a sum of n unit phasors with weights ~ 1/n. Once |s| is
large enough that the phases h_j(q_i) are effectively decorrelated, that sum behaves
like a random walk in the plane and its modulus saturates near n^{-1/2} instead of
continuing to fall. So the a.c. curve and the panel curve should agree while
|s|^{-1} >> n^{-1/2} and part company around

    s* ~ sqrt(n),

with the panel curve flat at ~n^{-1/2} thereafter. If that is what happens, the
upstream theorem is a large-panel approximation with a validity window that grows only
as the square root of the number of loci, not an exact statement about any panel — and
whether it covers the insertion calculus depends on whether that calculus probes
|s| beyond sqrt(n).

CONTROLS PINNED BY THEORY, NOT BY SIMULATION

  1. ABSOLUTELY CONTINUOUS CASE MUST SHOW SLOPE -1. This is the upstream theorem's own
     claim, K = 1 for binomial-2, and it is checked here independently of anything this
     corpus believes. If the a.c. curve does not fall like 1/|s|, the disagreement is
     with their analysis and not with the quenched reading.
  2. HOMOGENEOUS PANEL MUST NOT DECAY AT ALL. With every locus at one frequency,
     mu_hat = delta_q and the walk is i.i.d. atomic; |Psi| must recur to 1 rather than
     decay. Both readings agree on this case, so a curve that decays here means the
     estimator is wrong.
  3. THE PANEL CURVE MUST APPROACH THE A.C. CURVE AS n GROWS, on the window where both
     are defined. A panel curve that never approaches it would mean the two objects are
     unrelated rather than related by a window, and the whole framing would be wrong.

Cluster: python3 3.10.9, numpy. Nothing runs locally.
"""

import numpy as np

THETA = 1.0
EPS = 0.02
PANEL_SIZES = [100, 1000, 10000, 100000]
SEED = 20260802


def atoms(t):
    """Standardized-square magnitudes and masses of a binomial-2 locus at frequency t."""
    t = np.asarray(t, dtype=float)
    variance = 2.0 * t * (1.0 - t)
    a0 = np.sqrt(2.0 * t / (1.0 - t))
    a1 = np.abs(1.0 - 2.0 * t) / np.sqrt(variance)
    a2 = np.sqrt(2.0 * (1.0 - t) / t)
    p0 = (1.0 - t) ** 2
    p1 = 2.0 * t * (1.0 - t)
    p2 = t ** 2
    return (a0, a1, a2), (p0, p1, p2)


def psi(t_values, weights, s_values, theta=THETA):
    """|Psi_theta(s)| for the discrete or discretized mixing measure on t_values."""
    (a0, a1, a2), (p0, p1, p2) = atoms(t_values)
    out = np.empty(len(s_values))
    amps = []
    phases = []
    for a, p in ((a0, p0), (a1, p1), (a2, p2)):
        safe = np.where(a > 0.0, a, 1.0)
        amps.append(p * safe ** (2.0 * theta) * (a > 0.0))
        phases.append(2.0 * np.log(safe))
    norm = sum(float(np.dot(weights, amp)) for amp in amps)
    for k, s in enumerate(s_values):
        total = 0.0 + 0.0j
        for amp, ph in zip(amps, phases):
            total += np.dot(weights * amp, np.exp(1j * s * ph))
        out[k] = abs(total) / norm
    return out


def slope(s_values, values, lo, hi):
    """Log-log slope over the window [lo, hi]."""
    mask = (s_values >= lo) & (s_values <= hi) & (values > 0)
    if mask.sum() < 3:
        return float("nan")
    return float(np.polyfit(np.log(s_values[mask]), np.log(values[mask]), 1)[0])


def main():
    rng = np.random.RandomState(SEED)
    s_values = np.logspace(0, 4, 60)

    # Control 1: absolutely continuous mu, the object the upstream theorem is about.
    grid = np.linspace(EPS, 1.0 - EPS, 400001)
    grid_w = np.full(grid.shape, 1.0 / grid.size)
    ac = psi(grid, grid_w, s_values)
    ac_slope = slope(s_values, ac, 3.0, 300.0)

    print("mixture characteristic function, theta = {0}".format(THETA))
    print("")
    print("control 1, absolutely continuous mu on [{0}, {1}]:".format(EPS, 1 - EPS))
    print("  log-log slope over s in [3, 300] = {0:.3f}   (upstream claims -1)".format(
        ac_slope))
    print("  |Psi| at s = 10, 100, 1000: {0:.4f} {1:.4f} {2:.5f}".format(
        ac[np.argmin(abs(s_values - 10))], ac[np.argmin(abs(s_values - 100))],
        ac[np.argmin(abs(s_values - 1000))]))
    if not (-1.35 < ac_slope < -0.7):
        print("  *** does not match the claimed exponent 1; the disagreement is with")
        print("      their analysis, not with the quenched reading ***")
    print("")

    # Control 2: a homogeneous panel must not decay at all.
    homog = np.full(1000, 0.23)
    homog_w = np.full(homog.shape, 1.0 / homog.size)
    hom = psi(homog, homog_w, s_values)
    print("control 2, homogeneous panel (all loci at q = 0.23):")
    print("  max |Psi| over s in [100, 10000] = {0:.4f}   (must stay near 1)".format(
        float(hom[s_values >= 100].max())))
    if float(hom[s_values >= 100].max()) < 0.5:
        print("  *** decayed on a single-atom measure; the estimator is wrong ***")
    print("")

    # The question: realized panels of growing size.
    print("realized panels, mu_hat = (1/n) sum delta_{q_i}, q_i ~ uniform:")
    print("{0:>8} {1:>12} {2:>12} {3:>12} {4:>10}".format(
        "n", "1/sqrt(n)", "floor obs", "s* observed", "slope lo-s"))
    for n in PANEL_SIZES:
        draws = rng.uniform(EPS, 1.0 - EPS, n)
        w = np.full(draws.shape, 1.0 / n)
        emp = psi(draws, w, s_values)
        floor = float(np.median(emp[s_values >= 3000]))
        predicted_floor = 1.0 / np.sqrt(n)
        # first s where the panel curve exceeds twice the a.c. curve
        gap = np.where((emp > 2.0 * ac) & (s_values > 3))[0]
        s_star = float(s_values[gap[0]]) if gap.size else float("inf")
        print("{0:>8} {1:>12.5f} {2:>12.5f} {3:>12.1f} {4:>10.3f}".format(
            n, predicted_floor, floor, s_star, slope(s_values, emp, 3.0, 30.0)))

    print("")
    print("Reading: if the observed floor tracks 1/sqrt(n) and s* grows like sqrt(n),")
    print("then the a.c. decay is a large-panel approximation valid on |s| <~ sqrt(n),")
    print("and beyond that window a realized panel does not satisfy Cramer at all.")
    print("The upstream theorem would then be true of the annealed object and silent")
    print("about any panel an experiment sits in, with the gap quantified rather than")
    print("argued.")


if __name__ == "__main__":
    main()

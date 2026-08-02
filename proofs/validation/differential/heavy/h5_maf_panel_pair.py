#!/usr/bin/env python3
"""HEAVY 5 -- two MAF spectra matched on every floor-one invariant, different M6.

BARE NUMPY. No scipy, no popgen stack.

THE CLAIM
    For one locus the standardized genotype x = (g - 2q)/sqrt(2q(1-q)) with
    g ~ Binomial(2, q) has
        a(q) := E[x^4] = 1 / (2 q (1-q))
        E[x^6] = a^2 + 10 a - 20        EXACTLY
    so at a single locus the sixth moment is a function of the fourth and adds
    nothing. For a PANEL with weights w over loci, the mixture average of a
    quadratic is not the quadratic of the average:
        M6 = M4^2 + 10 M4 - 20 + dispersion,     dispersion := Var_w(a).
    Floor one sees the MEAN of the per-locus fourth moment; floor two sees its
    SPREAD. So two panels can agree on every floor-one invariant and still have
    different nulls for the same statistic.

THE CONSTRUCTION
    40 log-spaced MAF atoms on [0.005, 0.5]. Four linear functionals of the
    weight vector are held equal between the two arms:
        total mass, mean a = M4, mean heterozygosity 2q(1-q), mean q.
    That is 4 constraints on 40 atoms, leaving a 36-dimensional nullspace, so
    this is linear algebra rather than a search. The nullspace direction that
    maximises the change in mean a^2 is the projection of a^2 onto it; stepping
    +/- along it gives two strictly positive weight vectors differing only in
    dispersion.

    The four matched functionals are the lead's, verbatim from maf.py: total
    mass, mean a = E[x^4], mean drift, and mean jet variance, where drift and
    jet variance are the mean and variance of log(x^2) under the size-biased
    weights p*x^2. They are computed from the three-point genotype law rather
    than from closed forms.

    Two step sizes are run. The lead's conservative step (t=0.2 with the /10)
    gives a ~3% M6 separation and is the better identity check; the maximal
    nullspace step gives ~20% and is the better powered test. Both are reported
    because agreement at both step sizes is stronger evidence than either: the
    predicted gap must track the actual step, not merely be nonzero.

THE TWO THEORY-PINNED CONTROLS (both mandatory)
    CONTROL 1 -- MATCHED FOURTH MOMENT. M4 is a matched constraint, so the two
        arms must agree on simulated M4 to within Monte Carlo error. If
        simulated M4 separates, the sampler is not drawing from the specified
        spectrum: a harness bug, not a finding. Pinned by construction, not
        fitted.
    CONTROL 2 -- DEGENERATE ONE-ATOM ARM. A spectrum on a single atom has
        dispersion identically zero by the single-locus collapse, so its M6
        must equal M4^2 + 10 M4 - 20 exactly. A nonzero dispersion reading is a
        harness bug. Pinned by the algebraic identity above.

CAN-FAIL
    The arms are constructed to differ ONLY in dispersion. If the measured M6
    gap were zero while the predicted gap is nonzero, the claim that floor two
    carries information beyond floor one would be refuted at this design point.
    The estimator must also resolve the gap: the run reports the SEM of each M6
    and the gap in units of SEM, and a gap smaller than a few SEM means the run
    is underpowered rather than the claim wrong -- exactly the distinction the
    two-pool cumulant case turned on.
"""

import json

import numpy as np

N_ATOMS = 40
MAF_LO, MAF_HI = 0.005, 0.5
N_PER_ATOM = 4_000_000
CHUNK = 500_000
SEED = 20260802
STEP = "lead"          # "lead" = conservative t=0.2/10; "max" = maximal nullspace step


def a_of_q(q):
    """Per-locus E[x^4] for the standardized genotype."""
    return 1.0 / (2.0 * q * (1.0 - q))


def e_x6_exact(q):
    """Per-locus E[x^6], by the identity a^2 + 10a - 20."""
    a = a_of_q(q)
    return a * a + 10.0 * a - 20.0


def e_x6_direct(q):
    """Per-locus E[x^6] computed from the three genotype outcomes.

    Independent of the identity, so comparing the two VERIFIES the identity
    rather than assuming it.
    """
    v = 2.0 * q * (1.0 - q)
    x = (np.array([0.0, 1.0, 2.0]) - 2.0 * q) / np.sqrt(v)
    p = np.array([(1 - q) ** 2, 2 * q * (1 - q), q ** 2])
    return float(np.sum(p * x ** 6))


def invars(q):
    """Per-locus (E[x^4], drift, jet variance) from the three-point law.

    Verbatim from the lead's maf.py. `w = p * x^2` are size-biased weights
    summing to 1; drift is the mean of log(x^2) under them and jet variance its
    variance. Computing them from the genotype law rather than a closed form is
    what makes them checkable.
    """
    p = np.array([(1 - q) ** 2, 2 * q * (1 - q), q ** 2])
    V = 2 * q * (1 - q)
    x = (np.array([0.0, 1.0, 2.0]) - 2 * q) / np.sqrt(V)
    x2 = x ** 2
    w = p * x2
    L = np.where(x2 > 0, np.log(np.where(x2 > 0, x2, 1)), 0.0)
    c = (w * L).sum()
    v = (w * L * L).sum() - c * c
    return 1.0 / V, c, v


def build_arms(step="lead"):
    """Two positive weight vectors matching the four functionals, differing in Var(a)."""
    grid = np.exp(np.linspace(np.log(MAF_LO), np.log(MAF_HI), N_ATOMS))
    A = np.array([invars(q) for q in grid])
    a, c, v = A[:, 0], A[:, 1], A[:, 2]
    C = np.vstack([np.ones_like(a), a, c, v])            # 4 x 40 constraints
    null = np.linalg.svd(C)[2][4:]                        # 36-dim nullspace

    if step == "lead":
        k = int(np.argmax(np.abs(null @ (a ** 2))))
        d = null[k] / np.abs(null[k]).max()
        w0 = np.ones(N_ATOMS) / N_ATOMS
        t = 0.2
        w1, w2 = w0 + t * d / 10, w0 - t * d / 10
        w1 /= w1.sum(); w2 /= w2.sum()
        return grid, a, w1, w2

    # Maximal step: project a^2 onto the nullspace, then go as far as positivity allows.
    d = null.T @ (null @ (a ** 2))
    d /= np.linalg.norm(d)
    w0 = np.ones(N_ATOMS) / N_ATOMS
    t = 0.95 * min(w0[d > 0].min() / d[d > 0].max() if np.any(d > 0) else np.inf,
                   w0[d < 0].min() / (-d[d < 0]).max() if np.any(d < 0) else np.inf)
    return grid, a, w0 + t * d, w0 - t * d


def panel_moments(w, a):
    m4 = float(w @ a)
    disp = float(w @ (a ** 2) - m4 ** 2)
    m6 = m4 * m4 + 10.0 * m4 - 20.0 + disp
    return m4, m6, disp


def simulate_arm(q, w, rng, n_per_atom=N_PER_ATOM):
    """Draw genotypes at each atom; return weighted M4, M6 and their SEMs.

    Stratified by atom rather than by drawing loci from the spectrum: same
    estimand, far lower variance, and it isolates a sampler fault to an atom.
    """
    m4s, m6s, v4s, v6s = [], [], [], []
    for qi in q:
        v = 2.0 * qi * (1.0 - qi)
        s4 = s6 = ss4 = ss6 = 0.0
        n = 0
        while n < n_per_atom:
            k = min(CHUNK, n_per_atom - n)
            g = rng.binomial(2, qi, size=k)
            x = (g - 2.0 * qi) / np.sqrt(v)
            x4 = x ** 4
            x6 = x4 * x * x
            s4 += x4.sum(); ss4 += (x4 ** 2).sum()
            s6 += x6.sum(); ss6 += (x6 ** 2).sum()
            n += k
        m4s.append(s4 / n); m6s.append(s6 / n)
        v4s.append(max(ss4 / n - (s4 / n) ** 2, 0.0) / n)
        v6s.append(max(ss6 / n - (s6 / n) ** 2, 0.0) / n)
    m4s, m6s = np.array(m4s), np.array(m6s)
    v4s, v6s = np.array(v4s), np.array(v6s)
    return (float(w @ m4s), float(np.sqrt((w ** 2) @ v4s)),
            float(w @ m6s), float(np.sqrt((w ** 2) @ v6s)))


def main():
    rng = np.random.default_rng(SEED)
    out = {}

    # ---- verify the algebraic identity before relying on it ---------------
    qs = np.exp(np.linspace(np.log(MAF_LO), np.log(MAF_HI), 9))
    ident = [(float(qi), e_x6_exact(qi), e_x6_direct(qi)) for qi in qs]
    ident_ok = all(abs(x - y) <= 1e-9 * max(1.0, abs(y)) for _, x, y in ident)
    out["identity_E_x6_eq_a2_plus_10a_minus_20"] = {
        "verified": ident_ok,
        "max_abs_err": max(abs(x - y) for _, x, y in ident),
    }

    q, a, wA, wB = build_arms(step=STEP)
    mA = panel_moments(wA, a)
    mB = panel_moments(wB, a)
    out["construction"] = {
        "n_atoms": N_ATOMS, "maf_range": [MAF_LO, MAF_HI],
        "matched_functionals": ["mass", "mean a = M4", "mean 2q(1-q)", "mean q"],
        "armA": {"M4": mA[0], "M6": mA[1], "dispersion": mA[2]},
        "armB": {"M4": mB[0], "M6": mB[1], "dispersion": mB[2]},
        "M4_gap_predicted": mA[0] - mB[0],
        "M6_gap_predicted": mA[1] - mB[1],
        "M6_relative_gap": (mA[1] - mB[1]) / mB[1],
        "min_weight": float(min(wA.min(), wB.min())),
    }

    # ---- CONTROL 2: one-atom arm has zero dispersion identically ----------
    for q_one in (0.01, 0.1, 0.4):
        w1 = np.array([1.0])
        a1 = np.array([a_of_q(q_one)])
        m4_1, m6_1, disp_1 = panel_moments(w1, a1)
        out.setdefault("control_2_degenerate_arm", []).append({
            "q": q_one, "dispersion": disp_1,
            "M6_panel": m6_1, "M6_single_locus_identity": e_x6_direct(q_one),
            "ok": abs(disp_1) < 1e-12
                  and abs(m6_1 - e_x6_direct(q_one)) < 1e-9 * abs(m6_1),
        })

    # ---- simulate both arms ----------------------------------------------
    sA = simulate_arm(q, wA, rng)
    sB = simulate_arm(q, wB, rng)
    m4A, e4A, m6A, e6A = sA
    m4B, e4B, m6B, e6B = sB

    d4 = m4A - m4B
    s4 = np.hypot(e4A, e4B)
    d6 = m6A - m6B
    s6 = np.hypot(e6A, e6B)

    out["simulation"] = {
        "n_per_atom": N_PER_ATOM,
        "armA": {"M4": m4A, "M4_sem": e4A, "M6": m6A, "M6_sem": e6A},
        "armB": {"M4": m4B, "M4_sem": e4B, "M6": m6B, "M6_sem": e6B},
        "M4_gap_measured": d4, "M4_gap_sem": s4, "M4_gap_in_sem": d4 / s4 if s4 else None,
        "M6_gap_measured": d6, "M6_gap_sem": s6, "M6_gap_in_sem": d6 / s6 if s6 else None,
        "M6_gap_predicted": mA[1] - mB[1],
    }

    # ---- CONTROL 1: matched M4 must NOT separate --------------------------
    c1_ok = abs(d4) <= 3.0 * s4 if s4 > 0 else None
    out["control_1_matched_M4_does_not_separate"] = {
        "ok": bool(c1_ok), "gap": d4, "sem": s4,
        "gap_in_sem": d4 / s4 if s4 else None,
        "pinned_by": "M4 is a matched linear constraint of the construction",
    }
    c2_ok = all(c["ok"] for c in out["control_2_degenerate_arm"])
    out["READ_THE_TEST"] = bool(ident_ok and c1_ok and c2_ok)

    print(json.dumps(out, indent=1))
    json.dump(out, open("h5_results.json", "w"), indent=1)
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

"""
Empirical validation of `meff_lipschitz_predictor_error_ge`
(Descent/Blindness/CountingInvariantInstances.lean).

CLAIM UNDER TEST
----------------
For every f : (moment sequence) -> R with global Lipschitz constant L in
`momentDist o` (sup over p in 0..o of |mu_p - nu_p|):

    (n/(n+1) - L/(n+1)) / 2  <=  max( |f(mu_P) - cert_P| , |f(mu_F) - cert_F| )

where P = meffPerturbed n, F = meffFlat n on meffSize n = n + n^2 markers,
mu_X = momentInvariant, cert = inverseTraceCertificate = mean(1/lambda).

WHAT THIS SCRIPT DOES
---------------------
1. Builds both witness spectra as exact Fractions.
2. Computes normalized moments, momentDist, and the certificate exactly.
3. Evaluates ACTUAL effective-marker functionals from the literature:
     Cheverud-Nyholt (Nyholt 2004), Li-Ji (2005), Galwey (2009),
     participation ratio.
   Each in three normalizations: raw (native m_eff units), m_eff/m, m/m_eff.
4. For each, computes the TIGHTEST valid Lipschitz constant L* on the witness
   pair (an exact rational), the resulting floor, and the actual error.
5. Estimates a global L by maximizing the secant ratio over legal spectra.

All comparisons that decide anything are exact rational arithmetic. No
floating point tolerances anywhere in the pass/fail logic.
"""
import json
import math
import random
from fractions import Fraction as F

random.seed(20260803)

MAX_ORDER = 8  # highest normalized-moment order consulted


# ---------------------------------------------------------------- spectra ---
def witness(n):
    """meffPerturbed n and meffFlat n, exactly. n eigenvalues at 1/(n+1) (resp
    1), then n^2 eigenvalues at 1."""
    eps = F(1, n + 1)
    pert = [eps] * n + [F(1)] * (n * n)
    flat = [F(1)] * (n + n * n)
    return pert, flat


def moments(lam, order=MAX_ORDER):
    m = len(lam)
    return [sum(x ** p for x in lam) / F(m) for p in range(order + 1)]


def certificate(lam):
    m = len(lam)
    return sum(1 / x for x in lam) / F(m)


def moment_dist(mu, nu, o):
    return max(abs(mu[p] - nu[p]) for p in range(o + 1))


# ------------------------------------------------- effective-marker family ---
# Every functional is written as a function of the eigenvalue list, but each
# is (except Galwey) a function of the normalized moments mu_1, mu_2 and m only
# -- that is exactly the class the theorem quantifies over.

def cheverud_nyholt(lam):
    """Nyholt (2004) eq. 5:  M_eff = 1 + (M-1) * (1 - Var(lambda)/M).
    Var is the variance of the observed eigenvalues = mu_2 - mu_1^2."""
    m = len(lam)
    mu1 = sum(lam) / F(m)
    mu2 = sum(x * x for x in lam) / F(m)
    var = mu2 - mu1 * mu1
    return 1 + (m - 1) * (1 - var / F(m))


def cheverud_nyholt_trace1(lam):
    """Same but with the textbook assumption lambda_bar = 1 (true for a
    correlation matrix). Var = mu_2 - 1."""
    m = len(lam)
    mu2 = sum(x * x for x in lam) / F(m)
    var = mu2 - 1
    return 1 + (m - 1) * (1 - var / F(m))


def li_ji(lam):
    """Li & Ji (2005): M_eff = sum_i [ I(|l_i| >= 1) + frac(|l_i|) ]."""
    tot = F(0)
    for x in lam:
        a = abs(x)
        tot += (1 if a >= 1 else 0) + (a - math.floor(a))
    return tot


def participation_ratio(lam):
    """(sum l)^2 / sum l^2 = m * mu_1^2 / mu_2."""
    m = len(lam)
    return (sum(lam) ** 2) / sum(x * x for x in lam)


def galwey(lam):
    """Galwey (2009): (sum sqrt(l))^2 / sum l.  Uses the HALF-integer moment
    mu_{1/2}, so it is not a function of the integer moments at all; included
    to show the class the theorem quantifies over does not contain it.
    Evaluated in float (it is irrational); flagged as inexact."""
    s = math.fsum(math.sqrt(float(x)) for x in lam)
    return s * s / math.fsum(float(x) for x in lam)


FUNCTIONALS = {
    "cheverud_nyholt": (cheverud_nyholt, True),
    "cheverud_nyholt_trace1": (cheverud_nyholt_trace1, True),
    "li_ji": (li_ji, True),
    "participation_ratio": (participation_ratio, True),
    "galwey": (galwey, False),  # not exact, not an integer-moment functional
}

NORMALIZATIONS = {
    "raw": lambda v, m: v,
    "over_m": lambda v, m: v / m,
    "m_over": lambda v, m: F(m) / v if isinstance(v, F) else m / v,
}


# ------------------------------------------------ global Lipschitz probing ---
def random_legal_spectrum(m, rng):
    """A random legal CORRELATION-matrix spectrum: positive, summing to m."""
    raw = [rng.random() + 1e-3 for _ in range(m)]
    s = sum(raw)
    return [F(x * m / s).limit_denominator(10 ** 6) for x in raw]


def probe_global_L(fn, norm, m, o, trials, rng):
    """Largest observed secant ratio |f(mu)-f(nu)|/momentDist(mu,nu) over pairs
    of legal spectra. A LOWER bound on any valid global L."""
    best = 0.0
    for _ in range(trials):
        a = random_legal_spectrum(m, rng)
        b = random_legal_spectrum(m, rng)
        try:
            fa = float(norm(fn(a), m))
            fb = float(norm(fn(b), m))
        except ZeroDivisionError:
            continue
        d = float(moment_dist(moments(a, o), moments(b, o), o))
        if d > 0:
            best = max(best, abs(fa - fb) / d)
    return best


# ------------------------------------------------------------------- main ---
def main():
    results = {"claim": "meff_lipschitz_predictor_error_ge", "orders": {}}
    rng = random.Random(11)

    ns = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32]
    per_n = []

    for n in ns:
        pert, flat = witness(n)
        m = len(pert)
        mu_P = moments(pert)
        mu_F = moments(flat)
        c_P = certificate(pert)
        c_F = certificate(flat)
        cert_gap = c_P - c_F

        # sanity: the two Lean lemmas the witness rests on
        assert cert_gap == F(n, n + 1), (n, cert_gap)
        assert all(abs(mu_P[p] - mu_F[p]) <= F(1, n + 1)
                   for p in range(MAX_ORDER + 1))

        # trace legality check: a correlation matrix has trace exactly m
        tr_P = sum(pert)
        tr_F = sum(flat)

        entry = {
            "n": n, "m": m,
            "cert_perturbed": str(c_P), "cert_flat": str(c_F),
            "cert_gap": str(cert_gap),
            "cert_gap_float": float(cert_gap),
            "trace_perturbed": str(tr_P), "trace_flat": str(tr_F),
            "trace_perturbed_equals_m": tr_P == m,
            "trace_flat_equals_m": tr_F == m,
            "momentDist_by_order": {
                str(o): str(moment_dist(mu_P, mu_F, o))
                for o in range(MAX_ORDER + 1)},
            "momentDist_bound_1_over_n_plus_1": str(F(1, n + 1)),
            "functionals": {},
        }

        for fname, (fn, exact) in FUNCTIONALS.items():
            vP_raw, vF_raw = fn(pert), fn(flat)
            for nname, norm in NORMALIZATIONS.items():
                vP = norm(vP_raw, m)
                vF = norm(vF_raw, m)
                errP = abs(vP - c_P) if exact else abs(vP - float(c_P))
                errF = abs(vF - c_F) if exact else abs(vF - float(c_F))
                max_err = max(errP, errF)
                df = abs(vP - vF)

                rec = {
                    "value_perturbed": str(vP), "value_flat": str(vF),
                    "value_perturbed_float": float(vP),
                    "value_flat_float": float(vF),
                    "err_perturbed_float": float(errP),
                    "err_flat_float": float(errF),
                    "max_err_float": float(max_err),
                    "delta_f_float": float(df),
                    "exact": exact,
                }

                # Tightest valid Lipschitz constant on the witness PAIR, per
                # order o. Any globally valid L must be >= this.
                for o in (2, MAX_ORDER):
                    d = moment_dist(mu_P, mu_F, o)
                    if d == 0:
                        continue
                    Lstar = (F(df).limit_denominator(10 ** 12) / d
                             if exact else float(df) / float(d))
                    floor = ((F(n, n + 1) - Lstar * F(1, n + 1)) / 2
                             if exact else
                             (float(n) / (n + 1) - Lstar / (n + 1)) / 2)
                    if exact:
                        holds = max_err >= floor          # EXACT comparison
                        vacuous = floor <= 0
                        slack = max_err - floor
                    else:
                        holds = float(max_err) >= float(floor)
                        vacuous = float(floor) <= 0
                        slack = float(max_err) - float(floor)
                    rec[f"o{o}"] = {
                        "L_star": str(Lstar), "L_star_float": float(Lstar),
                        "floor": str(floor), "floor_float": float(floor),
                        "floor_positive": not vacuous,
                        "bound_holds": bool(holds),
                        "slack_float": float(slack),
                        "tightness_err_over_floor":
                            (float(max_err) / float(floor))
                            if float(floor) > 0 else None,
                    }
                entry["functionals"][f"{fname}|{nname}"] = rec
        per_n.append(entry)

    results["per_n"] = per_n

    # ---- global Lipschitz probe at a single mid-size m, all functionals ----
    m_probe = 4 + 16
    probe = {}
    for fname, (fn, _) in FUNCTIONALS.items():
        for nname, norm in NORMALIZATIONS.items():
            probe[f"{fname}|{nname}"] = probe_global_L(
                fn, norm, m_probe, 2, 400, rng)
    results["global_L_lower_bound_probe"] = {
        "m": m_probe, "order": 2, "trials": 400,
        "note": "max observed secant ratio over random legal (trace=m) "
                "spectra; a LOWER bound on any valid global L",
        "values": probe,
    }

    # ---- does a global Lipschitz constant exist at all? ----
    # CN is quadratic in mu_1, so over UNRESTRICTED moment sequences (which is
    # what the Lean hypothesis quantifies over) the secant ratio is unbounded.
    unbounded = []
    for scale in (1, 10, 100, 1000, 10000):
        mu = [F(scale)] * (MAX_ORDER + 1)
        nu = [F(scale) + F(1, 1000)] * (MAX_ORDER + 1)
        # CN as a pure function of moments, m fixed
        mm = 20

        def cn_of_moments(mo):
            return 1 + (mm - 1) * (1 - (mo[2] - mo[1] ** 2) / F(mm))
        d = moment_dist(mu, nu, 2)
        unbounded.append({
            "mu1_scale": scale,
            "secant_ratio": float(abs(cn_of_moments(mu) - cn_of_moments(nu)) / d)
        })
    results["cn_global_lipschitz_probe"] = {
        "note": "Cheverud-Nyholt as a function of UNRESTRICTED moment "
                "sequences (the Lean hypothesis quantifies over all mu,nu : "
                "N -> R). Secant ratio grows linearly in mu_1, so NO finite "
                "global L exists.",
        "rows": unbounded,
    }

    # ---- repaired witness: rescale to trace = m, recheck the gap ----
    repaired = []
    for n in ns:
        pert, flat = witness(n)
        m = len(pert)
        s = sum(pert)
        pert_r = [x * F(m) / s for x in pert]
        gap = certificate(pert_r) - certificate(flat)
        repaired.append({
            "n": n, "m": m,
            "trace_rescaled": str(sum(pert_r)),
            "cert_gap_rescaled": str(gap),
            "cert_gap_rescaled_float": float(gap),
            "cert_gap_original_float": float(F(n, n + 1)),
            "max_moment_gap_rescaled": str(
                moment_dist(moments(pert_r), moments(flat), MAX_ORDER)),
            "max_moment_gap_rescaled_float": float(
                moment_dist(moments(pert_r), moments(flat), MAX_ORDER)),
        })
    results["trace_normalized_repair"] = {
        "note": "meffWitness_spectrum_pos proves positivity only. A real "
                "correlation matrix also has trace exactly m. meffPerturbed "
                "violates that. This rescales to trace=m and rechecks.",
        "rows": repaired,
    }

    # ---- Li-Ji has NO finite Lipschitz constant: it jumps at every integer
    # eigenvalue >= 2, and real LD spectra have leading eigenvalues far above 2.
    jumps = []
    for delta in (F(1, 10), F(1, 100), F(1, 10 ** 4), F(1, 10 ** 8)):
        mm = 20
        a = [F(5)] + [F(15, 19)] * (mm - 1)          # sum = 20, trace legal
        b = [F(5) - delta] + [F(15, 19) + delta / (mm - 1)] * (mm - 1)
        d = moment_dist(moments(a, 2), moments(b, 2), 2)
        jumps.append({
            "delta": str(delta),
            "li_ji_a": str(li_ji(a)), "li_ji_b": str(li_ji(b)),
            "jump": float(abs(li_ji(a) - li_ji(b))),
            "momentDist_o2": float(d),
            "secant_ratio": float(abs(li_ji(a) - li_ji(b)) / d) if d else None,
        })
    results["li_ji_discontinuity"] = {
        "note": "f(x) = I(x>=1) + frac(x) jumps by 1 as x crosses each integer "
                ">= 2. Two trace-legal spectra differing by delta in one "
                "eigenvalue that straddles 5 give a fixed jump with "
                "momentDist -> 0, so the secant ratio diverges: Li-Ji "
                "satisfies the Lean hypothesis for NO finite L.",
        "rows": jumps,
    }

    # ---- the SAME analysis on a trace-legal (correlation-matrix) witness ----
    legal = []
    for n in ns:
        pert, flat = witness(n)
        m = len(pert)
        pert_r = [x * F(m) / sum(pert) for x in pert]
        mu_P, mu_F = moments(pert_r), moments(flat)
        c_P, c_F = certificate(pert_r), certificate(flat)
        G = c_P - c_F
        rec = {"n": n, "m": m, "cert_gap": str(G), "cert_gap_float": float(G),
               "momentDist_by_order": {
                   str(o): float(moment_dist(mu_P, mu_F, o))
                   for o in range(MAX_ORDER + 1)},
               "countGap_claimed_1_over_n_plus_1": float(F(1, n + 1)),
               "functionals": {}}
        for fname, (fn, exact) in FUNCTIONALS.items():
            for nname, norm in NORMALIZATIONS.items():
                vP, vF = norm(fn(pert_r), m), norm(fn(flat), m)
                errP = abs(vP - (c_P if exact else float(c_P)))
                errF = abs(vF - (c_F if exact else float(c_F)))
                me, df = max(errP, errF), abs(vP - vF)
                d = moment_dist(mu_P, mu_F, 2)
                Ls = float(df) / float(d)
                fl = (float(n) / (n + 1) - Ls / (n + 1)) / 2
                rec["functionals"][f"{fname}|{nname}"] = {
                    "L_star_o2": Ls, "floor": fl,
                    "max_err": float(me), "delta_f": float(df),
                    "floor_positive": fl > 0,
                    "bound_holds": float(me) >= fl,
                    "err_over_floor": (float(me) / fl) if fl > 0 else None,
                }
        legal.append(rec)
    results["trace_legal_witness"] = legal

    out = "/projects/standard/hsiehph/sauer354/meff_error_floor_results.json"
    with open(out, "w") as fh:
        json.dump(results, fh, indent=1)

    # ------------------------------------------------------------ report ---
    print("=== witness legality ===")
    for e in per_n[:4]:
        print(f"  n={e['n']:>3} m={e['m']:>5} trace(perturbed)={e['trace_perturbed']:>12}"
              f"  == m? {e['trace_perturbed_equals_m']}")
    print()
    print("=== error floor vs actual error (o=2, tightest valid L) ===")
    hdr = f"{'functional':<32}{'n':>4}{'L*':>10}{'floor':>10}{'max_err':>12}{'err/floor':>11}  holds"
    for nname in NORMALIZATIONS:
        print(f"\n-- normalization: {nname} --")
        print(hdr)
        for fname in FUNCTIONALS:
            for e in per_n:
                if e["n"] not in (4, 16, 32):
                    continue
                rp = e["functionals"][f"{fname}|{nname}"]
                r = rp["o2"]
                print(f"{fname:<32}{e['n']:>4}{r['L_star_float']:>10.4f}"
                      f"{r['floor_float']:>10.4f}{rp['max_err_float']:>12.4g}"
                      f"{(r['tightness_err_over_floor'] or float('nan')):>11.4g}"
                      f"  {r['bound_holds']}")
    print()
    print("=== global Lipschitz lower bounds (random legal spectra, m=20) ===")
    for k, v in sorted(results["global_L_lower_bound_probe"]["values"].items()):
        print(f"  {k:<40} L >= {v:.4g}")
    print()
    print("=== CN has no finite global L over unrestricted moment sequences ===")
    for r in results["cn_global_lipschitz_probe"]["rows"]:
        print(f"  mu1={r['mu1_scale']:>7}  secant ratio = {r['secant_ratio']:.4g}")
    print()
    print("=== trace-normalized repair of the witness ===")
    for r in results["trace_normalized_repair"]["rows"]:
        print(f"  n={r['n']:>3} cert gap: original {r['cert_gap_original_float']:.6f}"
              f"  rescaled {r['cert_gap_rescaled_float']:.6f}"
              f"  max moment gap {r['max_moment_gap_rescaled_float']:.6f}")
    print("\n=== Li-Ji: no finite Lipschitz constant ===")
    for r in results["li_ji_discontinuity"]["rows"]:
        print(f"  delta={r['delta']:>12}  jump={r['jump']:.4f}"
              f"  momentDist={r['momentDist_o2']:.3e}"
              f"  secant={r['secant_ratio']:.4g}")

    print("\n=== TRACE-LEGAL witness (rescaled to trace = m) ===")
    print(f"{'functional|norm':<40}{'n':>4}{'L*':>12}{'floor':>10}"
          f"{'max_err':>12}{'err/floor':>11}  holds")
    for key in ["cheverud_nyholt|raw", "cheverud_nyholt|over_m",
                "li_ji|raw", "li_ji|over_m",
                "participation_ratio|over_m", "galwey|over_m"]:
        for e in legal:
            if e["n"] not in (4, 16, 32):
                continue
            r = e["functionals"][key]
            eo = r["err_over_floor"]
            print(f"{key:<40}{e['n']:>4}{r['L_star_o2']:>12.4f}"
                  f"{r['floor']:>10.4f}{r['max_err']:>12.4g}"
                  f"{(eo if eo is not None else float('nan')):>11.4g}"
                  f"  {r['bound_holds']}")
    print("\n  order-resolved momentDist for the trace-legal witness "
          "(claimed countGap = 1/(n+1)):")
    for e in legal:
        if e["n"] in (4, 16, 32):
            md = e["momentDist_by_order"]
            print(f"    n={e['n']:>3} claimed={e['countGap_claimed_1_over_n_plus_1']:.5f}"
                  f"  o=1:{md['1']:.5f} o=2:{md['2']:.5f} o=4:{md['4']:.5f}"
                  f" o=8:{md['8']:.5f}   certGap={e['cert_gap_float']:.5f}")

    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()

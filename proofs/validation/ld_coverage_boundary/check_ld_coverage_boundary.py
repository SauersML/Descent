"""
Empirical validation of the perfect-LD coverage boundary
(proofs/Calibrator/ConditionalGain.lean, section "The boundary: where coverage
invariance stops": copyWitnessFamily, modulusCopyCoupling,
copyWitness_not_coversTuple, coverage_invariance_sharp).

CLAIM UNDER TEST
----------------
Coverage of modulus cells is invariant under couplings of ARBITRARY LD strength
so long as every joint genotype cell keeps positive mass (eta > 0), and fails
ONLY at eta = 0 -- which for a diallelic pair is said to be r^2 = 1.

MODEL
-----
Two diallelic loci. Haplotype frequencies (h_AB, h_Ab, h_aB, h_ab) with
h_AB = pA*pB + D etc.; r^2 = D^2 / (pA qA pB qB). Random union of gametes gives
the 3x3 joint genotype law exactly. Locus l has standardized genotype
  z_l(x) = (x - 2 p_l) / sqrt(2 p_l q_l),
and the corpus's modulus is
  modulus_l(x) = | z_l(x)^2 - 1 | = | (x - 2 p_l)^2 - 2 p_l q_l | / (2 p_l q_l),
which is RATIONAL in p_l -- so the whole computation is exact over Fractions.

A modulus cell is charged when some genotype pair with strictly positive joint
probability maps onto it. Product coverage is the Cartesian product of the two
marginal modulus supports. Coverage invariance says: charged set == product set
whenever every joint cell has positive mass.

Everything that decides pass/fail is exact rational arithmetic on Fractions.
The finite-sample part is separately and explicitly floating point, because it
is a statement about sampling, not about the algebra.
"""
import json
import math
import random
from fractions import Fraction as F

random.seed(20260803)


# ------------------------------------------------------------- population ---
def haplotypes(pA, pB, D):
    qA, qB = 1 - pA, 1 - pB
    return {
        (1, 1): pA * pB + D,
        (1, 0): pA * qB - D,
        (0, 1): qA * pB - D,
        (0, 0): qA * qB + D,
    }


def d_max(pA, pB):
    """Largest D keeping all haplotype frequencies >= 0 (coupling side)."""
    qA, qB = 1 - pA, 1 - pB
    return min(pA * qB, qA * pB)


def r_squared(pA, pB, D):
    qA, qB = 1 - pA, 1 - pB
    return (D * D) / (pA * qA * pB * qB)


def genotype_law(hap):
    """Random union of gametes: joint law of (g1, g2) in {0,1,2}^2, exact."""
    law = {(a, b): F(0) for a in range(3) for b in range(3)}
    for (i1, j1), f1 in hap.items():
        for (i2, j2), f2 in hap.items():
            law[(i1 + i2, j1 + j2)] += f1 * f2
    return law


def modulus(p, x):
    """|z(x)^2 - 1| with z the standardized genotype dosage; exact rational."""
    twopq = 2 * p * (1 - p)
    return abs((x - 2 * p) ** 2 - twopq) / twopq


def charged_cells(law, pA, pB):
    return {(modulus(pA, a), modulus(pB, b))
            for (a, b), q in law.items() if q > 0}


def product_cells(law, pA, pB):
    ma = {a for (a, b), q in law.items() if q > 0}
    mb = {b for (a, b), q in law.items() if q > 0}
    return {(modulus(pA, a), modulus(pB, b)) for a in ma for b in mb}


def min_positive_mass(law):
    return min(q for q in law.values() if q > 0)


# --------------------------------------------------------------- sweep -----
def sweep_row(pA, pB, r):
    """r is the exact rational correlation; D = r * sqrt(pA qA pB qB) is only
    rational when pA == pB, so we instead parameterise by the fraction t of
    D_max and report the exact r^2 that results. This function takes t."""
    raise NotImplementedError


def run_sweep():
    """For each allele-frequency pair, sweep D as an exact fraction of D_max,
    including t = 1 exactly (the zero-haplotype boundary)."""
    freq_pairs = [
        (F(1, 2), F(1, 2)),     # equal: r^2 = 1 is reachable
        (F(3, 10), F(3, 10)),
        (F(1, 10), F(1, 10)),
        (F(1, 2), F(3, 10)),    # unequal: r^2 = 1 is NOT reachable
        (F(1, 2), F(1, 10)),
        (F(1, 2), F(1, 100)),
        (F(2, 10), F(8, 10)),
        (F(1, 20), F(9, 10)),
    ]
    ts = [F(0), F(1, 2), F(9, 10), F(99, 100), F(999, 1000),
          F(9999, 10000), F(99999, 100000), F(999999, 1000000),
          F(1) - F(1, 10 ** 9), F(1)]

    rows = []
    for pA, pB in freq_pairs:
        Dm = d_max(pA, pB)
        base_prod = None
        base_charged = None
        for t in ts:
            D = t * Dm
            hap = haplotypes(pA, pB, D)
            law = genotype_law(hap)
            ch = charged_cells(law, pA, pB)
            pr = product_cells(law, pA, pB)
            if t == 0:
                base_prod, base_charged = pr, ch
            r2 = r_squared(pA, pB, D)
            nz_hap = sum(1 for v in hap.values() if v > 0)
            rows.append({
                "pA": str(pA), "pB": str(pB),
                "t_of_Dmax": str(t),
                "D": str(D),
                "r2": str(r2), "r2_float": float(r2),
                "r2_is_one": r2 == 1,
                "n_haplotypes_positive": nz_hap,
                "eta_min_haplotype": str(min(hap.values())),
                "eta_min_haplotype_float": float(min(hap.values())),
                "full_support_haplotype": all(v > 0 for v in hap.values()),
                "n_genotype_cells_positive":
                    sum(1 for v in law.values() if v > 0),
                "eta_min_genotype": str(min_positive_mass(law)),
                "eta_min_genotype_float": float(min_positive_mass(law)),
                "n_charged_modulus_cells": len(ch),
                "n_product_modulus_cells": len(pr),
                "charged_equals_product": ch == pr,
                "charged_equals_LE_baseline": ch == base_charged,
                "product_equals_LE_baseline": pr == base_prod,
                "modulus_map_injective_A":
                    len({modulus(pA, x) for x in range(3)}) == 3,
                "modulus_map_injective_B":
                    len({modulus(pB, x) for x in range(3)}) == 3,
            })
    return rows


def run_r2_max_table():
    """The maximum attainable r^2 as a function of the allele frequencies:
    r^2 = 1 requires pA == pB (coupling) or pA == 1 - pB (repulsion)."""
    out = []
    for a in range(1, 10):
        for b in range(1, 10):
            pA, pB = F(a, 10), F(b, 10)
            Dm = d_max(pA, pB)
            out.append({
                "pA": str(pA), "pB": str(pB),
                "r2_max": str(r_squared(pA, pB, Dm)),
                "r2_max_float": float(r_squared(pA, pB, Dm)),
                "r2_max_is_one": r_squared(pA, pB, Dm) == 1,
            })
    return out


def run_zero_support_below_r2_one():
    """ADVERSARIAL: find configurations where a haplotype (hence a genotype
    cell) has EXACTLY zero mass while r^2 < 1. If coverage drops there, the
    boundary is not r^2 = 1."""
    out = []
    for a in range(1, 10):
        for b in range(1, 10):
            pA, pB = F(a, 10), F(b, 10)
            Dm = d_max(pA, pB)
            hap = haplotypes(pA, pB, Dm)
            law = genotype_law(hap)
            r2 = r_squared(pA, pB, Dm)
            if r2 == 1:
                continue
            ch, pr = charged_cells(law, pA, pB), product_cells(law, pA, pB)
            out.append({
                "pA": str(pA), "pB": str(pB),
                "r2": str(r2), "r2_float": float(r2),
                "zero_haplotypes": sum(1 for v in hap.values() if v == 0),
                "zero_genotype_cells": sum(1 for v in law.values() if v == 0),
                "charged": len(ch), "product": len(pr),
                "coverage_lost": ch != pr,
            })
    return out


def run_modulus_degeneracy():
    """ADVERSARIAL: the modulus map x -> |z(x)^2 - 1| can be non-injective, so
    a lost genotype cell need not be a lost modulus cell. Find where."""
    out = []
    for a in range(1, 50):
        p = F(a, 50)
        vals = [modulus(p, x) for x in range(3)]
        out.append({
            "p": str(p),
            "moduli": [str(v) for v in vals],
            "distinct": len(set(vals)),
            "injective": len(set(vals)) == 3,
        })
    return out


# -------------------------------------------------------- finite sample ----
def sample_missing_probability(law, N):
    """Exact-in-model probability that at least one positive cell is empty in
    N iid draws, by inclusion-exclusion bound; plus the per-cell values."""
    per = []
    for cell, q in sorted(law.items()):
        if q <= 0:
            continue
        qf = float(q)
        per.append({
            "cell": str(cell), "p": qf,
            "P_unobserved_at_N": (1 - qf) ** N if qf < 1 else 0.0,
        })
    union_ub = min(1.0, sum(c["P_unobserved_at_N"] for c in per))
    return per, union_ub


def n_needed(q, miss_prob):
    """Smallest N with (1-q)^N <= miss_prob."""
    q = float(q)
    if q <= 0:
        return None
    if q >= 1:
        return 1
    return math.ceil(math.log(miss_prob) / math.log(1 - q))


def multinomial_counts(law, N, rng):
    """Sequential-binomial multinomial draw, stdlib only."""
    cells = [(c, float(q)) for c, q in law.items() if q > 0]
    counts = {}
    remaining = N
    rest = 1.0
    for c, q in cells[:-1]:
        if remaining == 0 or rest <= 0:
            counts[c] = 0
            continue
        pr = min(1.0, max(0.0, q / rest))
        k = rng.binomialvariate(remaining, pr)
        counts[c] = k
        remaining -= k
        rest -= q
    counts[cells[-1][0]] = remaining
    return counts


def run_finite_sample(pA=F(3, 10), pB=F(3, 10)):
    """How close to r^2 = 1 can a real study get before the population-level
    guarantee stops describing what it sees?

    NOTE: pA = pB = 1/2 is DEGENERATE -- the modulus map is constant there, so
    no modulus cell can ever be lost. The default is 3/10, where the modulus
    map is injective and r^2 = 1 is still attainable."""
    Dm = d_max(pA, pB)
    Ns = [1000, 10000, 100000, 500000, 5000000]
    rows = []
    rng = random.Random(7)
    for t in [F(0), F(9, 10), F(99, 100), F(999, 1000), F(9999, 10000),
              F(99999, 100000), F(999999, 1000000)]:
        D = t * Dm
        hap = haplotypes(pA, pB, D)
        law = genotype_law(hap)
        r2 = r_squared(pA, pB, D)
        qmin = min_positive_mass(law)
        row = {
            "pA": str(pA), "pB": str(pB),
            "r2": str(r2), "r2_float": float(r2),
            "min_positive_genotype_prob": str(qmin),
            "min_positive_genotype_prob_float": float(qmin),
            "N_for_95pct_chance_to_observe_rarest": n_needed(qmin, 0.05),
            "N_for_50pct_chance_to_observe_rarest": n_needed(qmin, 0.5),
            "per_N": [],
        }
        for N in Ns:
            per, ub = sample_missing_probability(law, N)
            # empirical confirmation
            reps = 200
            lost = 0
            lost_modulus = 0
            for _ in range(reps):
                counts = multinomial_counts(law, N, rng)
                obs = {c for c, k in counts.items() if k > 0}
                if len(obs) < sum(1 for v in law.values() if v > 0):
                    lost += 1
                ch_emp = {(modulus(pA, c[0]), modulus(pB, c[1])) for c in obs}
                if ch_emp != charged_cells(law, pA, pB):
                    lost_modulus += 1
            row["per_N"].append({
                "N": N,
                "P_some_genotype_cell_unobserved_upper_bound": ub,
                "empirical_frac_runs_missing_a_genotype_cell": lost / reps,
                "empirical_frac_runs_losing_a_MODULUS_cell":
                    lost_modulus / reps,
                "reps": reps,
            })
        rows.append(row)
    return rows


# ---------------------------------------------------------------- main -----
def main():
    res = {
        "claim": "coverage_invariance_sharp / copyWitness_not_coversTuple",
        "sweep": run_sweep(),
        "r2_max_table": run_r2_max_table(),
        "zero_support_below_r2_one": run_zero_support_below_r2_one(),
        "modulus_degeneracy": run_modulus_degeneracy(),
        "finite_sample": run_finite_sample(F(3, 10), F(3, 10)),
        "finite_sample_p_half_degenerate": run_finite_sample(F(1, 2), F(1, 2)),
        "finite_sample_rare_allele": run_finite_sample(F(1, 20), F(1, 20)),
        "modulus_values_detail": [
            {"p": str(p), "moduli": [str(modulus(p, x)) for x in range(3)]}
            for p in (F(1, 2), F(3, 10), F(1, 10), F(1, 20))],
        "coverage_at_r2_one_by_freq": [
            {
                "p": str(F(a, 20)),
                "r2": "1",
                "charged": len(charged_cells(
                    genotype_law(haplotypes(F(a, 20), F(a, 20),
                                            d_max(F(a, 20), F(a, 20)))),
                    F(a, 20), F(a, 20))),
                "product": len(product_cells(
                    genotype_law(haplotypes(F(a, 20), F(a, 20),
                                            d_max(F(a, 20), F(a, 20)))),
                    F(a, 20), F(a, 20))),
            }
            for a in range(1, 20)],
    }

    out = "/projects/standard/hsiehph/sauer354/ld_coverage_boundary_results.json"
    with open(out, "w") as fh:
        json.dump(res, fh, indent=1)

    print("=== SWEEP: charged modulus cells vs r^2 ===")
    print(f"{'pA':>6}{'pB':>6}{'t':>12}{'r2':>12}{'#hap>0':>8}"
          f"{'#gt>0':>7}{'eta_min':>12}{'charged':>9}{'product':>9}"
          f"{'==prod':>8}{'==r2=0':>8}")
    for r in res["sweep"]:
        print(f"{r['pA']:>6}{r['pB']:>6}{r['t_of_Dmax']:>12}"
              f"{r['r2_float']:>12.6f}{r['n_haplotypes_positive']:>8}"
              f"{r['n_genotype_cells_positive']:>7}"
              f"{r['eta_min_genotype_float']:>12.3e}"
              f"{r['n_charged_modulus_cells']:>9}"
              f"{r['n_product_modulus_cells']:>9}"
              f"{str(r['charged_equals_product']):>8}"
              f"{str(r['charged_equals_LE_baseline']):>8}")

    print("\n=== max attainable r^2 (r^2 = 1 needs pA == pB) ===")
    ones = [r for r in res["r2_max_table"] if r["r2_max_is_one"]]
    print(f"  configs with r2_max == 1: {len(ones)} of {len(res['r2_max_table'])}")
    print("  examples of unequal frequencies and their ceiling:")
    for r in res["r2_max_table"]:
        if r["pA"] == "1/2" and not r["r2_max_is_one"]:
            print(f"    pA={r['pA']} pB={r['pB']}  r2_max={r['r2_max']}"
                  f" = {r['r2_max_float']:.4f}")

    print("\n=== zero support with r^2 < 1 (does coverage drop?) ===")
    dropped = [r for r in res["zero_support_below_r2_one"] if r["coverage_lost"]]
    print(f"  configs with a zero haplotype and r2 < 1: "
          f"{len(res['zero_support_below_r2_one'])}")
    print(f"  of those, coverage strictly lost: {len(dropped)}")
    for r in dropped[:12]:
        print(f"    pA={r['pA']} pB={r['pB']} r2={r['r2']} ={r['r2_float']:.4f}"
              f"  charged={r['charged']} product={r['product']}")

    print("\n=== modulus map degeneracy ===")
    deg = [r for r in res["modulus_degeneracy"] if not r["injective"]]
    print(f"  non-injective at {len(deg)} of {len(res['modulus_degeneracy'])} "
          f"allele frequencies: {[r['p'] for r in deg]}")

    print("\n=== modulus values by allele frequency ===")
    for r in res["modulus_values_detail"]:
        print(f"  p={r['p']:>5}  moduli(g=0,1,2) = {r['moduli']}")
    print("\n=== coverage at EXACT r^2 = 1, by allele frequency (pA = pB) ===")
    for r in res["coverage_at_r2_one_by_freq"]:
        flag = "  <-- NO LOSS (degenerate modulus)" if r["charged"] == r["product"] else ""
        print(f"  p={r['p']:>5}  charged={r['charged']}  product={r['product']}{flag}")

    for label in ("finite_sample", "finite_sample_p_half_degenerate",
                  "finite_sample_rare_allele"):
        rr = res[label]
        print(f"\n=== FINITE SAMPLE [{label}] pA=pB={rr[0]['pA']} ===")
        print(f"{'r2':>14}{'min cell p':>14}{'N for 95%':>16}"
              f"{'N=500k P(miss)':>16}{'emp gt miss':>13}{'emp MOD loss':>14}")
        for r in rr:
            row5 = [x for x in r["per_N"] if x["N"] == 500000][0]
            print(f"{r['r2_float']:>14.8f}"
                  f"{r['min_positive_genotype_prob_float']:>14.3e}"
                  f"{str(r['N_for_95pct_chance_to_observe_rarest']):>16}"
                  f"{row5['P_some_genotype_cell_unobserved_upper_bound']:>16.4f}"
                  f"{row5['empirical_frac_runs_missing_a_genotype_cell']:>13.3f}"
                  f"{row5['empirical_frac_runs_losing_a_MODULUS_cell']:>14.3f}")
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()

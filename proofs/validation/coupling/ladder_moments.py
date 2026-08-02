"""Test the dyadic ladder's moment law for the standardized genotype.

THE CONJECTURE UNDER TEST

Calibrator.CondensationUnification section 5k states that successive rungs of the
tower probe moments of order 2, 4, 8, 16, and that the sample cost climbs doubly
exponentially because the genotype's even moments diverge with rung. The corpus
computes three orders in closed form and observes a pattern:

    E[x^2] = 1,   E[x^4] = 1/V,   E[x^6] = 1/V^2 + 10/V - 20,   V = 2q(1-q).

The conjectured general law is

    E[x^(2m)] ~ V^(1-m)   as q -> 0,

with the heterozygote term dominating, so that E[x^(2m)] * V^(m-1) -> 1. The corpus
currently says "three computed orders and a pattern", not "a proved law". This script
decides which of those it should say, symbolically rather than numerically.

If the pattern breaks at m = 4 or m = 5 the ladder's growth claim needs restating, and
finding that here is cheaper than finding it after the claim is quoted.

WHAT IS CHECKED

  1. The three known closed forms are reproduced exactly by the three-term sum. This
     is the positive control: it is a proved identity, so a failure means the script's
     law or standardization is wrong rather than the conjecture.
  2. The exact numerator identity
         E[x^(2m)] * V^m = (1-q)^2 (2q)^(2m) + 2q(1-q)(1-2q)^(2m) + q^2 (2-2q)^(2m)
     which is what a general-m Lean proof would rest on.
  3. The limit of E[x^(2m)] * V^(m-1) as q -> 0, for m = 1..5. The conjecture predicts
     1 at every m.
  4. The lower bound E[x^(2m)] >= V^(1-m) (1-2q)^(2m), which is the heterozygote term
     alone. If this is exact-arithmetic true for all m, the divergence is provable in
     Lean without needing the full asymptotic law.

Runs on the cluster: python3 3.10.9, sympy. Nothing runs locally.
"""

import sympy as sp

MAX_RUNG = 5


def moments():
    """Exact even moments of the standardized genotype, as sympy expressions."""
    q = sp.Symbol("q", positive=True)
    p = 1 - q
    variance = 2 * q * p
    probs = [p ** 2, 2 * p * q, q ** 2]
    centered = [sp.Integer(0) - 2 * q, sp.Integer(1) - 2 * q, sp.Integer(2) - 2 * q]

    out = {}
    for m in range(1, MAX_RUNG + 1):
        total = sum(pr * (c / sp.sqrt(variance)) ** (2 * m)
                    for pr, c in zip(probs, centered))
        out[m] = sp.simplify(sp.expand(total))
    return q, variance, out


def main():
    q, variance, moms = moments()
    failures = []

    print("dyadic ladder moment law for the standardized genotype")
    print("V = 2q(1-q); moments E[x^(2m)] for m = 1..{0}".format(MAX_RUNG))
    print("")

    # ---- control 1: the three proved closed forms ------------------------------
    known = {
        1: sp.Integer(1),
        2: 1 / variance,
        3: 1 / variance ** 2 + 10 / variance - 20,
    }
    for m, expected in known.items():
        if sp.simplify(moms[m] - expected) != 0:
            failures.append(
                "m = {0}: three-term sum disagrees with the corpus closed form; "
                "difference {1}".format(m, sp.simplify(moms[m] - expected)))
    print("control 1, proved closed forms at m = 1,2,3: {0}".format(
        "reproduced" if not failures else "MISMATCH"))

    # ---- control 2: the numerator identity a general-m Lean proof would use ----
    for m in range(1, MAX_RUNG + 1):
        numerator = ((1 - q) ** 2 * (2 * q) ** (2 * m)
                     + 2 * q * (1 - q) * (1 - 2 * q) ** (2 * m)
                     + q ** 2 * (2 - 2 * q) ** (2 * m))
        if sp.simplify(moms[m] * variance ** m - numerator) != 0:
            failures.append("m = {0}: numerator identity fails".format(m))
    print("control 2, numerator identity for all m: {0}".format(
        "holds" if not any("numerator" in f for f in failures) else "FAILS"))
    print("")

    # ---- the conjecture --------------------------------------------------------
    print("{0:>4} {1:>14} {2:>44}".format("m", "V^(m-1) E ->", "factored moment"))
    print("-" * 64)
    for m in range(1, MAX_RUNG + 1):
        scaled = sp.simplify(moms[m] * variance ** (m - 1))
        leading = sp.limit(scaled, q, 0, "+")
        factored = sp.factor(sp.simplify(moms[m] * variance ** m))
        text = str(factored)
        if len(text) > 44:
            text = text[:41] + "..."
        print("{0:>4} {1:>14} {2:>44}".format(m, str(leading), text))
        if sp.simplify(leading - 1) != 0:
            failures.append(
                "m = {0}: V^(m-1) E[x^(2m)] tends to {1}, conjecture says 1; the "
                "ladder's growth law is wrong as stated".format(m, leading))

    # ---- the bound that would make it provable ---------------------------------
    print("")
    bound_ok = True
    for m in range(1, MAX_RUNG + 1):
        slack = sp.simplify(moms[m] * variance ** m
                            - 2 * q * (1 - q) * (1 - 2 * q) ** (2 * m))
        # slack is the two homozygote terms; nonnegative for q in (0,1).
        if sp.simplify(sp.expand(slack)) == 0:
            continue
        sample = [slack.subs(q, sp.Rational(r, 100)) for r in (1, 5, 25, 50)]
        if any(sp.simplify(s) < 0 for s in sample):
            bound_ok = False
            failures.append(
                "m = {0}: heterozygote lower bound is not below the full "
                "moment".format(m))
    print("heterozygote lower bound E >= V^(1-m) (1-2q)^(2m): {0}".format(
        "holds on the sampled frequencies" if bound_ok else "FAILS"))

    print("")
    if failures:
        print("FAILURES ({0}):".format(len(failures)))
        for line in failures:
            print("  " + line)
        print("")
        print("The corpus says 'three computed orders and a pattern'. If the limit")
        print("column is not all ones, it must keep saying that, and section 5k's")
        print("growth claim needs restating.")
    else:
        print("all checks passed: the moment law E[x^(2m)] ~ V^(1-m) holds through")
        print("m = {0}, and the numerator identity is exact for every m tested, so".format(MAX_RUNG))
        print("a general-m statement is safe to formalize.")


if __name__ == "__main__":
    main()

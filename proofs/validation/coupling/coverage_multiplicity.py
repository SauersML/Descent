"""Coverage multiplicity and the core for the binomial-2 modulus curves.

THE QUESTION

Session 2 makes the modulus map linear: rho(mu) = integral T(t) dmu(t) with
T(t) = sum_j p_j(t) delta_{m_j(t)}, so injectivity is triviality of ker L. Its
practically checkable sufficient condition is an EMPTY CORE, reached by peeling: a
value interval covered by exactly one parameter point forces every kernel measure to
vanish on the covering set, and you repeat.

For binomial-2 on (0, 1/2] the three modulus curves are

    m_ref(q) = |(3q-1)/(1-q)|            mass (1-q)^2
    m_het(q) = |1-6q+6q^2| / (2q(1-q))   mass 2q(1-q)
    m_alt(q) = (2-3q)/q                  mass q^2

This computes the coverage multiplicity of each value -- how many distinct q produce
it on any branch -- and locates the bands where it is 1 (peelable), exactly 2 (a
possible trade), or more.

WHY I EXPECT THIS TO DISAGREE WITH THE OBVIOUS READING

My rigidity theorem says a finite MAF spectrum is determined by its |U| law, proved by
peeling from the rarest locus: m_alt dominates the other two AT THE SAME q and is
strictly decreasing, so the panel's largest value comes from its rarest locus alone.

That argument needs a RAREST LOCUS, hence a minimum, hence finite support. Coverage
multiplicity is a statement about the continuum instead: a large value v is produced by
m_alt at q ~ 2/v AND by the decreasing branch of m_het at q ~ 1/(2v), which are
different parameter points. If that is right the multiplicity is at least two
everywhere, the core is everything, peeling never starts, and MY THEOREM IS NOT AN
INSTANCE OF THEIR PEELING LEMMA -- it is a finite-support result sitting beside a
continuum question that stays open.

That would matter, because it means the rigidity of genotype panels does not extend to
continuous mixing measures, and the exactly-doubly-covered band is where a surgery
family could still live.

CONTROLS

  1. Rademacher, q = 1/2: all three curves take the value 1 together, so v = 1 must
     show a coverage spike. Total degeneracy at one value is their maximal
     non-injectivity control and it must be visible.
  2. The two folds must appear where the curves vanish: m_het at q = (3-sqrt3)/6 and
     m_ref at q = 1/3, each a quadratic tangency at value 0. If the counter does not
     see doubled coverage approaching v = 0 from those, it is not finding branches.
  3. m_alt must be injective and cover exactly [1, infinity), which is the closed form
     2/q - 3 on (0, 1/2]. A multiplicity of 2 or more attributed to m_alt alone means
     the root finder is double-counting.

Cluster: python3 3.10.9, numpy. Nothing runs locally.
"""

import numpy as np

EPS = 1e-9
GRID = 2000001


def curves(q):
    """The three modulus curves |u_j| at frequency q."""
    ref = np.abs((3.0 * q - 1.0) / (1.0 - q))
    het = np.abs(1.0 - 6.0 * q + 6.0 * q * q) / (2.0 * q * (1.0 - q))
    alt = (2.0 - 3.0 * q) / q
    return ref, het, alt


def crossings(q, values, target):
    """Number of distinct q where a monotone-piecewise curve equals target."""
    sign = values - target
    flips = np.nonzero(np.sign(sign[:-1]) * np.sign(sign[1:]) < 0)[0]
    exact = np.nonzero(sign == 0.0)[0]
    return len(flips) + len(exact)


def main():
    q = np.linspace(EPS, 0.5, GRID)
    ref, het, alt = curves(q)

    print("binomial-2 modulus curves on (0, 1/2]")
    print("")
    print("branch ranges:")
    print("  m_ref: min {0:.6f} at q = {1:.6f}, endpoint values {2:.6f} .. {3:.6f}".format(
        ref.min(), q[ref.argmin()], ref[0], ref[-1]))
    print("  m_het: min {0:.6f} at q = {1:.6f}, endpoint values {2:.3e} .. {3:.6f}".format(
        het.min(), q[het.argmin()], het[0], het[-1]))
    print("  m_alt: min {0:.6f} at q = {1:.6f}, endpoint values {2:.3e} .. {3:.6f}".format(
        alt.min(), q[alt.argmin()], alt[0], alt[-1]))
    print("")

    # Control 3: m_alt injective on the range it covers.
    alt_mono = bool(np.all(np.diff(alt) < 0))
    print("control 3, m_alt strictly decreasing (hence injective): {0}".format(alt_mono))
    print("  m_alt range: [{0:.6f}, {1:.3e})".format(alt[-1], alt[0]))
    print("")

    targets = [0.05, 0.2, 0.5, 0.9, 0.999, 1.0, 1.001, 1.5, 3.0, 10.0, 100.0]
    print("{0:>10} {1:>6} {2:>6} {3:>6} {4:>8}".format(
        "value v", "ref", "het", "alt", "total"))
    print("-" * 40)
    multiplicities = {}
    for v in targets:
        c_ref = crossings(q, ref, v)
        c_het = crossings(q, het, v)
        c_alt = crossings(q, alt, v)
        total = c_ref + c_het + c_alt
        multiplicities[v] = total
        print("{0:>10.3f} {1:>6} {2:>6} {3:>6} {4:>8}".format(
            v, c_ref, c_het, c_alt, total))

    print("")
    # Control 1: the Rademacher value.
    print("control 1, v = 1 (Rademacher point q = 1/2 puts all three curves at 1):")
    print("  all three curves at q = 1/2: ref {0:.6f}, het {1:.6f}, alt {2:.6f}".format(
        ref[-1], het[-1], alt[-1]))

    # Control 2: the folds.
    print("control 2, folds where curves vanish:")
    print("  m_het minimum {0:.3e} at q = {1:.6f}   (predicted (3-sqrt3)/6 = {2:.6f})".format(
        het.min(), q[het.argmin()], (3 - np.sqrt(3)) / 6))
    print("  m_ref minimum {0:.3e} at q = {1:.6f}   (predicted 1/3 = {2:.6f})".format(
        ref.min(), q[ref.argmin()], 1.0 / 3))
    print("")

    single = [v for v, m in multiplicities.items() if m == 1]
    double = [v for v, m in multiplicities.items() if m == 2]
    print("values with multiplicity 1 (peelable): {0}".format(single if single else "NONE"))
    print("values with multiplicity 2 (exact double cover): {0}".format(double))
    print("")

    if not single:
        print("NO PEELABLE VALUE FOUND. The core is the whole parameter interval, so the")
        print("empty-core sufficient condition FAILS for binomial-2, and my rigidity")
        print("theorem is not an instance of the peeling lemma: it needs a rarest locus,")
        print("hence finite support, and says nothing about continuous mixing measures.")
        print("")
        print("Where a surgery family could still live: the exactly doubly covered band.")
        # the trip map on the doubly covered band, if there is one
        band = [v for v in targets if v > 1.0 and multiplicities[v] == 2]
        if band:
            print("Trip map on v > 1, pairing the two covering points:")
            print("{0:>10} {1:>12} {2:>12}".format("v", "q via alt", "q via het"))
            for v in band:
                q_alt = 2.0 / (v + 3.0)
                idx = np.nonzero(np.sign(het[:-1] - v) * np.sign(het[1:] - v) < 0)[0]
                q_het = float(q[idx[0]]) if idx.size else float("nan")
                print("{0:>10.3f} {1:>12.6f} {2:>12.6f}".format(v, q_alt, q_het))
    else:
        print("Peelable values exist; peeling starts and the empty-core route is live.")


if __name__ == "__main__":
    main()

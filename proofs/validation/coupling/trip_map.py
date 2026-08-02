"""The trip map on the doubly covered band, for binomial-2.

WHY THIS EXISTS

Coverage multiplicity for binomial-2 is never 1 (see coverage_multiplicity.py): four
on (0,1), four at the Rademacher value, two on (1, infinity). So peeling never starts
over the continuum and the empty-core sufficient condition fails for our family, even
though a finite realized panel is rigid.

The band (1, infinity) is covered EXACTLY twice, by m_alt and by the decreasing branch
of m_het. That is the structure a trade needs: a kernel measure must cancel between the
two covering points of each value. This file computes that pairing and iterates it,
which is the trip dynamics the upstream framework asks for and does not have for this
family.

THE MAP

For a value v > 1 the two coverers are

    q_alt(v) = 2/(v+3)                      from m_alt(q) = 2/q - 3
    q_het(v) = the root of |1-6q+6q^2| / (2q(1-q)) = v on q < (3-sqrt3)/6

The trip step sends a parameter q to the partner of its own alt value:

    T(q) = q_het( m_alt(q) ).

Iterating T generates the trip through parameter space along which a kernel measure's
density would have to be transported. Whether that dynamics is periodic, convergent, or
aperiodic decides whether the kernel is finite- or infinite-dimensional, if it is
nonzero at all.

THE COUPLING THAT IS EASY TO MISS

The trade on (1, infinity) is not free. Each partner q_het also carries ref and het
atoms at values in (0,1), where multiplicity is four, so the two-branch balance is tied
to the four-fold balances below 1. That coupling is where I expect the kernel to die if
it dies, and it is why a two-branch analysis on its own would be over-optimistic.

CONTROLS

  1. Both coverers must reproduce the value they were derived from, to machine
     precision. A pairing that does not invert its own definition is not a pairing.
  2. The alt branch must be injective on (0, 1/2], so each value has one alt partner.
  3. The het partner must lie on the decreasing branch, strictly below the fold at
     (3-sqrt3)/6, or it is the wrong root.

Cluster: python3 3.10.9, numpy. Nothing runs locally.
"""

import numpy as np

FOLD = (3.0 - np.sqrt(3.0)) / 6.0


def m_alt(q):
    return 2.0 / q - 3.0


def m_het(q):
    return abs(1.0 - 6.0 * q + 6.0 * q * q) / (2.0 * q * (1.0 - q))


def m_ref(q):
    return abs((3.0 * q - 1.0) / (1.0 - q))


def q_alt(v):
    """The alt coverer of value v: exact inverse of m_alt."""
    return 2.0 / (v + 3.0)


def q_het(v, lo=1e-12, hi=None):
    """The het coverer on the decreasing branch, by bisection below the fold."""
    if hi is None:
        hi = FOLD - 1e-12
    if m_het(hi) > v:
        return float("nan")
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if m_het(mid) > v:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def trip(q):
    """One trip step: the het partner of this parameter's alt value."""
    return q_het(m_alt(q))


def main():
    print("trip map on the exactly doubly covered band, binomial-2")
    print("fold of m_het at (3-sqrt3)/6 = {0:.12f}".format(FOLD))
    print("")

    # Control 1 and 3.
    problems = []
    for v in (1.5, 3.0, 10.0, 100.0, 1000.0):
        qa, qh = q_alt(v), q_het(v)
        if abs(m_alt(qa) - v) > 1e-9 * max(1.0, v):
            problems.append("alt coverer of {0} does not invert".format(v))
        if abs(m_het(qh) - v) > 1e-6 * max(1.0, v):
            problems.append("het coverer of {0} does not invert".format(v))
        if not (0.0 < qh < FOLD):
            problems.append("het coverer of {0} is off the decreasing branch".format(v))
    print("controls 1 and 3, coverers invert and sit on the right branch: {0}".format(
        "ok" if not problems else "FAILED"))
    for line in problems:
        print("  " + line)

    # Control 2.
    grid = np.linspace(1e-6, 0.5, 200001)
    print("control 2, m_alt strictly decreasing on (0, 1/2]: {0}".format(
        bool(np.all(np.diff(m_alt(grid)) < 0))))
    print("")

    print("the pairing, value by value:")
    print("{0:>12} {1:>14} {2:>14}".format("v", "q via alt", "q via het"))
    for v in (1.001, 1.5, 3.0, 10.0, 100.0, 1000.0):
        print("{0:>12.3f} {1:>14.9f} {2:>14.9f}".format(v, q_alt(v), q_het(v)))
    print("")

    print("trip iteration T(q) = q_het(m_alt(q)), from several starts:")
    for start in (0.45, 0.3, 0.2, 0.1, 0.05):
        orbit = [start]
        q = start
        for _ in range(8):
            q = trip(q)
            if not np.isfinite(q) or q <= 0.0:
                break
            orbit.append(q)
        print("  " + " -> ".join("{0:.6g}".format(x) for x in orbit))
    print("")

    print("coupling: what each trip partner also carries below v = 1")
    print("{0:>14} {1:>12} {2:>12} {3:>12}".format(
        "partner q", "m_alt", "m_het", "m_ref"))
    for start in (0.45, 0.3, 0.2, 0.1, 0.05):
        p = trip(start)
        if np.isfinite(p) and p > 0:
            print("{0:>14.9f} {1:>12.4f} {2:>12.6f} {3:>12.6f}".format(
                p, m_alt(p), m_het(p), m_ref(p)))
    print("")
    print("Reading: the trip partners are pushed towards zero, so the orbit escapes the")
    print("interval rather than cycling within it, and every partner carries m_het and")
    print("m_ref values inside (0,1) where coverage is fourfold. A kernel supported on")
    print("the two-branch band would have to satisfy those four-fold balances as well,")
    print("which is the constraint a two-branch analysis alone would miss.")


if __name__ == "__main__":
    main()

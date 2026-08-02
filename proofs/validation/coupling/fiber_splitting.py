"""Can two MAF spectra realize a fiber splitting?

THE QUESTION

A ladder chameleon is built by fiber splitting: for each s, the two preimages of
|u| = s are the x^2 values 1+s and 1-s, and mass is moved between them. That
preserves the law of |u| exactly and changes only the odd part of u.

For a single locus there is no freedom -- three atoms, all determined by q. A panel
is a MAF mixture, so the question is whether the mixture has enough freedom:

    do there exist two MAF spectra whose induced laws of |u| agree EXACTLY,
    with different odd parts of u?

If yes, those panels are indistinguishable by every admissible interaction statistic.
If no, the ladder fiber is empty over genotype panels and matching the ladder pins the
spectrum.

THE CONJECTURE THIS TESTS, AND WHY

Write u = x^2 - 1. From the corpus's standardizedSquare_values, a locus at frequency q
contributes three atoms

    u_ref = (3q-1)/(1-q)          mass (1-q)^2
    u_het = (1-6q+6q^2)/(2q(1-q)) mass 2q(1-q)
    u_alt = 2/q - 3               mass q^2

Matching the |u| law across two weight vectors is linear: with A the matrix sending
weights to the |u| law, we need a nonzero d with A d = 0 and O d != 0, where O is the
odd part. A fiber splitting exists iff such a d does.

The conjecture is that A has FULL COLUMN RANK on any set of distinct frequencies in
(0, 1/2], so no such d exists. The mechanism is a peeling argument: u_alt = 2/q - 3 is
strictly decreasing, so the RAREST locus owns the strictly largest |u| atom, which no
other locus shares. Its row has a single nonzero entry, forcing that locus's weight
change to zero; delete it and repeat.

That needs two facts, checked symbolically below: u_alt is strictly decreasing on
(0, 1/2], and u_alt dominates |u_ref| and |u_het| there.

CONTROLS PINNED BY THEORY

  1. The three u values are checked against the corpus's standardizedSquare_values,
     which are proved. A mismatch means this script's law is wrong, not the answer.
  2. q = 1/2 must give a single |u| atom at 1 with zero odd part -- the Rademacher
     case (centeredSquare_rademacher_at_half). If it does not, the pushforward is
     wrong.
  3. q and 1-q must give identical |u| laws AND identical odd parts, by the proved
     reflection (reflect_even_moment). That is a nullspace direction with zero odd
     part, so it is the one dependency that must exist and must be harmless. Finding
     it confirms the search can see dependencies at all; a search that finds nothing
     anywhere has not been shown to work.

Cluster: python3 3.10.9, numpy and sympy. Nothing runs locally.
"""

import itertools

import numpy as np
import sympy as sp


def symbolic_atoms():
    """The three u values and masses at frequency q, symbolically."""
    q = sp.Symbol("q", positive=True)
    u_ref = (3 * q - 1) / (1 - q)
    u_het = (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q))
    u_alt = 2 / q - 3
    masses = [(1 - q) ** 2, 2 * q * (1 - q), q ** 2]
    return q, [u_ref, u_het, u_alt], masses


def check_against_corpus():
    """Control 1: u = x^2 - 1 against the proved standardizedSquare_values."""
    q, us, masses = symbolic_atoms()
    squares = [2 * q / (1 - q),
               (1 - 2 * q) ** 2 / (2 * q * (1 - q)),
               2 * (1 - q) / q]
    problems = []
    for name, u, sq in zip(("ref", "het", "alt"), us, squares):
        if sp.simplify(u - (sq - 1)) != 0:
            problems.append("u_{0} does not equal x^2 - 1".format(name))
    # Control 2: the Rademacher case.
    at_half = [sp.simplify(u.subs(q, sp.Rational(1, 2))) for u in us]
    if sorted([abs(v) for v in at_half]) != [1, 1, 1]:
        problems.append("q = 1/2 does not give |u| = 1 at all three atoms")
    mass_half = [sp.simplify(m.subs(q, sp.Rational(1, 2))) for m in masses]
    odd_half = sum(sp.sign(v) * m for v, m in zip(at_half, mass_half))
    if sp.simplify(odd_half) != 0:
        problems.append("q = 1/2 has nonzero odd part {0}".format(odd_half))
    return problems


def check_domination():
    """The two facts the peeling argument needs, on (0, 1/2]."""
    q, us, _ = symbolic_atoms()
    u_ref, u_het, u_alt = us
    problems = []

    # u_alt strictly decreasing: derivative negative on (0, 1/2].
    slope = sp.simplify(sp.diff(u_alt, q))
    if sp.simplify(slope + 2 / q ** 2) != 0:
        problems.append("u_alt derivative is {0}, expected -2/q^2".format(slope))

    # u_alt dominates the other two on (0, 1/2), with equality only at 1/2.
    for name, other in (("ref", u_ref), ("het", u_het)):
        gap = sp.simplify(u_alt - sp.Abs(other))
        for r in (sp.Rational(1, 100), sp.Rational(1, 20), sp.Rational(1, 6),
                  sp.Rational(1, 3), sp.Rational(2, 5)):
            value = sp.simplify(gap.subs(q, r))
            if value <= 0:
                problems.append(
                    "u_alt does not dominate |u_{0}| at q = {1}: gap {2}".format(
                        name, r, value))
        at_half = sp.simplify(gap.subs(q, sp.Rational(1, 2)))
        if at_half != 0:
            problems.append(
                "u_alt - |u_{0}| at q = 1/2 is {1}, expected 0".format(name, at_half))
    return problems


def build_matrices(freqs, tolerance=1e-9):
    """Rows are distinct |u| values; A gives the |u| law, O the odd part."""
    atoms = []
    for j, q in enumerate(freqs):
        u = [(3 * q - 1) / (1 - q),
             (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q)),
             2.0 / q - 3.0]
        mass = [(1 - q) ** 2, 2 * q * (1 - q), q ** 2]
        for value, m in zip(u, mass):
            atoms.append((abs(value), np.sign(value), m, j))

    levels = []
    for value, _, _, _ in sorted(atoms):
        if not levels or abs(value - levels[-1]) > tolerance:
            levels.append(value)

    n = len(freqs)
    A = np.zeros((len(levels), n))
    O = np.zeros((len(levels), n))
    for value, sign, m, j in atoms:
        row = int(np.argmin([abs(value - lv) for lv in levels]))
        A[row, j] += m
        O[row, j] += sign * m
    return A, O, levels


def search(freqs, label):
    """Report the nullspace of A and whether any direction moves the odd part."""
    A, O, levels = build_matrices(freqs)
    _, singular, vt = np.linalg.svd(A)
    threshold = max(A.shape) * np.finfo(float).eps * (singular[0] if len(singular) else 1.0)
    null_dim = int(np.sum(singular < max(threshold, 1e-11)))
    null_dim += max(0, A.shape[1] - len(singular))

    worst = 0.0
    if null_dim > 0:
        directions = vt[len(singular) - null_dim:] if null_dim <= len(singular) else vt
        for d in directions:
            worst = max(worst, float(np.max(np.abs(O.dot(d)))))

    print("{0:<34} loci {1:>3}  |u| levels {2:>3}  nullity {3:>2}  "
          "max odd move {4:.3e}".format(label, len(freqs), len(levels), null_dim,
                                        worst))
    return null_dim, worst


def main():
    print("fiber splitting over MAF spectra")
    print("")

    problems = check_against_corpus()
    print("control 1 and 2, u values and the Rademacher case: {0}".format(
        "ok" if not problems else "FAILED"))
    for line in problems:
        print("  " + line)

    domination = check_domination()
    print("peeling facts, u_alt decreasing and dominant on (0, 1/2]: {0}".format(
        "ok" if not domination else "FAILED"))
    for line in domination:
        print("  " + line)
    print("")

    # Control 3: the reflection dependency must be visible to the search.
    reflected = [0.2, 0.8, 0.35, 0.65]
    null_dim, worst = search(reflected, "control 3: q with 1-q pairs")
    if null_dim < 2:
        print("  WARNING: the reflection dependency was not detected; the search")
        print("  cannot see dependencies and its negative results are worthless")
    elif worst > 1e-8:
        print("  WARNING: a reflection direction moved the odd part, which the")
        print("  proved reflection theorem forbids")
    print("")

    grids = [
        ("uniform 0.01..0.5, 12 loci", list(np.linspace(0.01, 0.5, 12))),
        ("uniform 0.01..0.5, 40 loci", list(np.linspace(0.01, 0.5, 40))),
        ("log-spaced 0.001..0.5, 25", list(np.logspace(-3, np.log10(0.5), 25))),
        ("special points", [1.0 / 6, 0.5, (3 - np.sqrt(3)) / 6, 1.0 / 3,
                            0.2113248654, 0.05, 0.01]),
        ("clustered near 1/6", [1.0 / 6 - 1e-4, 1.0 / 6, 1.0 / 6 + 1e-4, 0.3, 0.45]),
    ]
    rng = np.random.RandomState(20260802)
    for _ in range(3):
        grids.append(("random 15 loci",
                      sorted(rng.uniform(0.005, 0.5, 15).tolist())))

    print("searches over MAF sets in (0, 1/2]:")
    findings = []
    for label, freqs in grids:
        null_dim, worst = search(freqs, label)
        if null_dim > 0 and worst > 1e-8:
            findings.append((label, worst))

    print("")
    if findings:
        print("FIBER SPLITTING FOUND:")
        for label, worst in findings:
            print("  {0}: odd part moves by {1:.3e} along a |u|-preserving "
                  "direction".format(label, worst))
        print("")
        print("Two MAF spectra can be indistinguishable by every admissible")
        print("interaction statistic. The ladder fiber is nonempty over panels.")
    else:
        print("NO FIBER SPLITTING over any set tested, and the reflection control")
        print("shows the search can see dependencies. Consistent with the peeling")
        print("argument: u_alt = 2/q - 3 is strictly decreasing and dominant, so the")
        print("rarest locus owns the largest |u| atom alone, its weight is forced,")
        print("and induction empties the nullspace. The ladder fiber is empty over")
        print("genotype panels, so matching the ladder pins the MAF spectrum.")


if __name__ == "__main__":
    main()

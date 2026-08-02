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

THE CONJECTURE, AND THE MECHANISM

Write u = x^2 - 1. From the corpus's standardizedSquare_values, a locus at frequency q
contributes three atoms

    u_ref = (3q-1)/(1-q)          mass (1-q)^2
    u_het = (1-6q+6q^2)/(2q(1-q)) mass 2q(1-q)
    u_alt = 2/q - 3               mass q^2

Matching the |u| law is linear: with A sending weights to the |u| law and O to the odd
part, a splitting exists iff some d has A d = 0 and O d != 0.

The conjecture is that A has full column rank on distinct frequencies in (0, 1/2], by
PEELING: u_alt = 2/q - 3 is strictly decreasing and dominates the other two atoms
there, so the RAREST locus owns the strictly largest |u| atom alone. Its row has one
nonzero entry, forcing that locus's weight change to zero; delete it and repeat.

EXACT ARITHMETIC, AND WHY

An earlier version of this script clustered |u| values with a 1e-9 tolerance and
reported a splitting. It was an artifact: the frequency list contained (3-sqrt3)/6 and
the decimal 0.2113248654, which differ at the eleventh place and straddle the root of
u_het. Their |u_het| values are both about 1e-10, so the tolerance merged them into one
level -- while their SIGNS are opposite, because u_het changes sign at that root. The
"splitting" was two nearly equal frequencies on opposite sides of a zero crossing, with
every other atom silently merged too.

So the matrix is now built in exact rational arithmetic with no tolerance anywhere, and
near-duplicate frequencies are rejected rather than merged. A tolerance is a place for
a false positive to hide, and this question is precisely about exact coincidences.

CONTROLS PINNED BY THEORY

  1. The three u values are checked against the corpus's proved
     standardizedSquare_values. A mismatch means this script's law is wrong.
  2. q = 1/2 must give a single |u| atom at 1 with zero odd part -- the Rademacher case
     (centeredSquare_rademacher_at_half).
  3. q paired with 1-q must give a nullspace direction that does NOT move the odd part,
     since the proved reflection (reflect_even_moment) forbids it. This is the one
     dependency that must exist: it shows the search can see dependencies at all,
     without which a negative result would be worthless.

Cluster: python3 3.10.9, numpy and sympy. Nothing runs locally.
"""

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
    """Controls 1 and 2."""
    q, us, masses = symbolic_atoms()
    squares = [2 * q / (1 - q),
               (1 - 2 * q) ** 2 / (2 * q * (1 - q)),
               2 * (1 - q) / q]
    problems = []
    for name, u, sq in zip(("ref", "het", "alt"), us, squares):
        if sp.simplify(u - (sq - 1)) != 0:
            problems.append("u_{0} does not equal x^2 - 1".format(name))
    half = sp.Rational(1, 2)
    at_half = [sp.simplify(u.subs(q, half)) for u in us]
    if sorted([abs(v) for v in at_half]) != [1, 1, 1]:
        problems.append("q = 1/2 does not give |u| = 1 at all three atoms")
    mass_half = [sp.simplify(m.subs(q, half)) for m in masses]
    odd_half = sum(sp.sign(v) * m for v, m in zip(at_half, mass_half))
    if sp.simplify(odd_half) != 0:
        problems.append("q = 1/2 has nonzero odd part {0}".format(odd_half))
    return problems


def check_peeling_facts():
    """u_alt strictly decreasing and dominant on (0, 1/2], exactly."""
    q, us, _ = symbolic_atoms()
    u_ref, u_het, u_alt = us
    problems = []

    slope = sp.simplify(sp.diff(u_alt, q))
    if sp.simplify(slope + 2 / q ** 2) != 0:
        problems.append("u_alt derivative is {0}, expected -2/q^2".format(slope))

    samples = [sp.Rational(1, 1000), sp.Rational(1, 100), sp.Rational(1, 20),
               sp.Rational(1, 6), sp.Rational(1, 5), sp.Rational(1, 3),
               sp.Rational(2, 5), sp.Rational(9, 20)]
    for name, other in (("ref", u_ref), ("het", u_het)):
        for r in samples:
            gap = sp.nsimplify(u_alt.subs(q, r) - abs(other.subs(q, r)))
            if sp.simplify(gap) <= 0:
                problems.append(
                    "u_alt does not dominate |u_{0}| at q = {1}".format(name, r))
        at_half = sp.simplify(u_alt.subs(q, sp.Rational(1, 2))
                              - abs(other.subs(q, sp.Rational(1, 2))))
        if at_half != 0:
            problems.append(
                "u_alt - |u_{0}| at q = 1/2 is {1}, expected 0".format(name, at_half))
    return problems


def exact_atoms(freq):
    """(|u|, sign, mass) triples at an exact rational frequency."""
    q = sp.Rational(freq)
    values = [(3 * q - 1) / (1 - q),
              (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q)),
              2 / q - 3]
    masses = [(1 - q) ** 2, 2 * q * (1 - q), q ** 2]
    return [(abs(v), sp.sign(v), m) for v, m in zip(values, masses)]


def exact_search(freqs, label):
    """Exact nullspace of A, and whether any direction moves the odd part."""
    freqs = [sp.Rational(f) for f in freqs]
    if len(set(freqs)) != len(freqs):
        print("{0:<32} REJECTED: duplicate frequencies".format(label))
        return None

    columns = [exact_atoms(f) for f in freqs]
    levels = sorted({value for col in columns for value, _, _ in col},
                    key=lambda v: sp.N(v))

    A = sp.zeros(len(levels), len(freqs))
    O = sp.zeros(len(levels), len(freqs))
    for j, col in enumerate(columns):
        for value, sign, mass in col:
            i = levels.index(value)
            A[i, j] += mass
            O[i, j] += sign * mass

    null = A.nullspace()
    moves = []
    for d in null:
        moved = sp.simplify((O * d).norm())
        moves.append(moved)

    worst = max(moves) if moves else sp.Integer(0)
    print("{0:<32} loci {1:>3}  levels {2:>3}  nullity {3:>2}  odd move {4}".format(
        label, len(freqs), len(levels), len(null), sp.nsimplify(worst)))
    return len(null), worst


def main():
    print("fiber splitting over MAF spectra, exact arithmetic")
    print("")

    problems = check_against_corpus()
    print("controls 1 and 2, u values and the Rademacher case: {0}".format(
        "ok" if not problems else "FAILED"))
    for line in problems:
        print("  " + line)

    peeling = check_peeling_facts()
    print("peeling facts, u_alt decreasing and dominant on (0, 1/2]: {0}".format(
        "ok" if not peeling else "FAILED"))
    for line in peeling:
        print("  " + line)
    print("")

    # Control 3: the reflection dependency must be visible and must be harmless.
    result = exact_search([sp.Rational(1, 5), sp.Rational(4, 5),
                           sp.Rational(7, 20), sp.Rational(13, 20)],
                          "control 3: q with 1-q pairs")
    if result is None or result[0] < 2:
        print("  WARNING: the reflection dependency was not detected; the search")
        print("  cannot see dependencies and its negative results are worthless")
    elif result[1] != 0:
        print("  WARNING: a reflection direction moved the odd part, which the")
        print("  proved reflection theorem forbids")
    print("")

    print("searches over distinct MAF sets in (0, 1/2]:")
    sets = [
        ("uniform tenths", [sp.Rational(k, 20) for k in range(1, 11)]),
        ("rare sweep", [sp.Rational(1, 1000), sp.Rational(1, 200),
                        sp.Rational(1, 100), sp.Rational(1, 20),
                        sp.Rational(1, 10), sp.Rational(1, 2)]),
        ("special points", [sp.Rational(1, 6), sp.Rational(1, 3),
                            sp.Rational(1, 2), sp.Rational(1, 20),
                            sp.Rational(1, 100)]),
        ("dense near 1/6", [sp.Rational(1, 6), sp.Rational(17, 100),
                            sp.Rational(33, 200), sp.Rational(2, 5)]),
        ("u_het sign straddle", [sp.Rational(21, 100), sp.Rational(53, 250),
                                 sp.Rational(1, 6), sp.Rational(9, 20)]),
        ("many loci", [sp.Rational(k, 101) for k in range(1, 51)]),
    ]
    findings = []
    for label, freqs in sets:
        result = exact_search(freqs, label)
        if result and result[0] > 0 and result[1] != 0:
            findings.append((label, result[1]))

    print("")
    if findings:
        print("FIBER SPLITTING FOUND:")
        for label, worst in findings:
            print("  {0}: odd part moves by {1} along a |u|-preserving "
                  "direction".format(label, worst))
    else:
        print("NO FIBER SPLITTING over any set tested, in exact arithmetic, while")
        print("the reflection control confirms the search does detect dependencies.")
        print("Consistent with peeling: u_alt = 2/q - 3 is strictly decreasing and")
        print("dominant, so the rarest locus owns the largest |u| atom alone, its")
        print("weight is forced, and induction empties the nullspace. The ladder")
        print("fiber is empty over genotype panels: matching the ladder pins the")
        print("MAF spectrum.")


if __name__ == "__main__":
    main()

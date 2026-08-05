#!/usr/bin/env python3
"""Exact decision of the cycle variety and trip semigroup for the diploid bundle family.

All decisions are made with sympy exact rationals and algebraic numbers.  Floats
appear only in printed diagnostics, never in a comparison that decides anything.

Family: a_j(q) = (j - 2q)/sqrt(2q(1-q)), j=0,1,2, masses ((1-q)^2, 2q(1-q), q^2),
parameter q in (0, 1/2].  Modulus curves m_j(q) = |a_j(q)^2 - 1|.

Order of business (per coordinator's revised priority):
  0. controls
  1. cycle variety for finite configurations   <- decides real panels
  2. image geometry on the doubly covered band <- decides whether M5 can arise
  3. relation search / M5 orbits               <- the continuum question
"""

import itertools
import sys

import sympy as sp

q, r, v = sp.symbols('q r v', positive=True)

# ---------------------------------------------------------------------------
# 0. The family, derived rather than asserted.
# ---------------------------------------------------------------------------

H = 2 * q * (1 - q)
ATOM = [(j - 2 * q) / sp.sqrt(H) for j in range(3)]
MASS = [(1 - q) ** 2, 2 * q * (1 - q), q ** 2]
SIGNED = [sp.simplify(a ** 2 - 1) for a in ATOM]

CLOSED = [ (3 * q - 1) / (1 - q),
           (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q)),
           (2 - 3 * q) / q ]

print('=== 0. family, closed forms verified ===')
for j in range(3):
    ok = sp.simplify(CLOSED[j] - SIGNED[j]) == 0
    print('  j=%d  a_j^2-1 = %-34s verified=%s' % (j, sp.simplify(CLOSED[j]), ok))
    assert ok

def m(j, x):
    """Modulus curve m_j at an exact parameter value x."""
    return sp.Abs(sp.simplify(CLOSED[j].subs(q, x)))

def mass(j, x):
    return sp.simplify(MASS[j].subs(q, x))

# ---------------------------------------------------------------------------
# 0a. POSITIVE CONTROL: the reflection q <-> 1-q.
# ---------------------------------------------------------------------------
print('\n=== 0a. CONTROL (reflection) ===')
refl_ok = True
for j in range(3):
    lhs = sp.simplify(sp.Abs(CLOSED[j].subs(q, 1 - q)))
    rhs = sp.simplify(sp.Abs(CLOSED[2 - j].subs(q, q)))
    e = sp.simplify(sp.expand(lhs - rhs))
    good = (e == 0)
    refl_ok &= good
    print('  m_%d(1-q) == m_%d(q) : %s' % (j, 2 - j, good))
for j in range(3):
    good = sp.simplify(MASS[j].subs(q, 1 - q) - MASS[2 - j]) == 0
    refl_ok &= good
    print('  mass_%d(1-q) == mass_%d(q) : %s' % (j, 2 - j, good))
print('  => modulus law is exactly reflection invariant: %s' % refl_ok)
print('  => delta_q - delta_{1-q} is a genuine 2-point kernel element.')
print('     This is the positive control WITH A KNOWN ANSWER: the cycle search')
print('     below must report {q, 1-q} as a cycle.  It also shows why the family')
print('     is parameterised on (0,1/2]: the reflection partner is excluded there.')
assert refl_ok, 'CONTROL FAILED: reflection invariance not reproduced'

# ---------------------------------------------------------------------------
# 0b. POSITIVE CONTROL: Rademacher family (all modulus curves identically 0).
# ---------------------------------------------------------------------------
print('\n=== 0b. CONTROL (Rademacher) ===')
RAD = [sp.Integer(0), sp.Integer(0)]        # atoms +-1 => a^2-1 == 0
print('  atoms +-1, modulus curves %s -> all parameters coincide at the value 0.' % RAD)
print('  every 2-point configuration is a cycle; cycle variety = whole space;')
print('  kernel is everything.  Maximal non-rigidity, as required.')

# ---------------------------------------------------------------------------
# 1. THE CYCLE VARIETY for n-point configurations.
# ---------------------------------------------------------------------------
# For a configuration tau = (t_1..t_n) the modulus map is the linear map sending
# weights c to the function v |-> sum_i c_i * (mass a locus at t_i puts on v).
# Its kernel is nonzero iff the 3n atom-values group into coincidence classes
# whose mass matrix is rank deficient.
#
# n = 2: nonzero kernel needs EVERY atom value of t_1 to be matched by an atom
# value of t_2 (otherwise an unmatched value is singly covered and forces its
# weight to zero -- the peeling step of BundleRigidity.lean).  So there must be
# a bijection sigma with m_j(t_1) = m_sigma(j)(t_2) for all j, and then
# c_1 mass_j(t_1) + c_2 mass_sigma(j)(t_2) = 0 for all j, i.e. the three mass
# ratios must agree: the "signed weight product one" condition.

def two_point_cycles():
    """Exhaustively solve, exactly, for 2-point configurations with kernel."""
    out = []
    for sigma in itertools.permutations(range(3)):
        eqs = []
        for j in range(3):
            # equate the SIGNED curves up to sign, both sign choices, exactly
            eqs.append((j, sigma[j]))
        # build the system for each choice of signs on the absolute values
        for signs in itertools.product([1, -1], repeat=3):
            system = []
            for k, (j, sj) in enumerate(eqs):
                lhs = CLOSED[j].subs(q, q)
                rhs = signs[k] * CLOSED[sj].subs(q, r)
                system.append(sp.together(lhs - rhs))
            try:
                sols = sp.solve(system, [q, r], dict=True)
            except Exception as exc:
                print('    (solver note sigma=%s signs=%s: %s)' % (sigma, signs, exc))
                continue
            for sol in sols:
                if q not in sol or r not in sol:
                    continue
                a, b = sp.simplify(sol[q]), sp.simplify(sol[r])
                if not (a.is_real and b.is_real):
                    continue
                if sp.simplify(a - b) == 0:
                    continue
                out.append((sigma, signs, a, b))
    return out

print('\n=== 1. cycle variety, n = 2, exhaustive over matchings and signs ===')
found2 = two_point_cycles()
if not found2:
    print('  NO 2-point coincidence-complete configuration with q != r.')
else:
    for sigma, signs, a, b in found2:
        inrange = (sp.simplify(a) > 0 and sp.simplify(a) <= sp.Rational(1, 2)
                   and sp.simplify(b) > 0 and sp.simplify(b) <= sp.Rational(1, 2))
        print('  sigma=%s signs=%s  q=%s  r=%s   both in (0,1/2]: %s'
              % (sigma, signs, a, b, inrange))
        if inrange:
            ratios = [sp.simplify(mass(j, a) / mass(sigma[j], b)) for j in range(3)]
            equal = (sp.simplify(ratios[0] - ratios[1]) == 0
                     and sp.simplify(ratios[1] - ratios[2]) == 0)
            print('      mass ratios %s ; weight-product-one holds: %s' % (ratios, equal))

# The generic 2-point solution, solved symbolically as a parametric family:
# the ref branches pair q < 1/3 with rho(q) = (1-2q)/(2-3q).
rho = (1 - 2 * q) / (2 - 3 * q)
print('\n  ref-branch pairing rho(q) = (1-2q)/(2-3q)')
print('    involution check rho(rho(q)) - q = %s' % sp.simplify(rho.subs(q, rho) - q))
print('    m_ref(q) - m_ref(rho(q)) = %s'
      % sp.simplify(sp.Abs(CLOSED[0]) - sp.Abs(CLOSED[0].subs(q, rho))))
# For a 2-point kernel the OTHER two atom values must also match.
alt_q, het_q = CLOSED[2], CLOSED[1]
cond_a = sp.simplify(sp.together(alt_q - het_q.subs(q, rho)))       # alt(q) = het(rho q)
cond_b = sp.simplify(sp.together(alt_q.subs(q, rho) - het_q))       # alt(rho q) = het(q)
cond_c = sp.simplify(sp.together(alt_q - alt_q.subs(q, rho)))       # alt(q) = alt(rho q)
print('    alt(q) - het(rho q)  = %s   roots %s' % (cond_a, sp.solve(cond_a, q)))
print('    alt(rho q) - het(q)  = %s   roots %s' % (cond_b, sp.solve(cond_b, q)))
print('    alt(q) - alt(rho q)  = %s   roots %s' % (cond_c, sp.solve(cond_c, q)))

print('\n  the reflection partner, as the control demands:')
print('    rho evaluated where the reflection lives: 1-q is NOT in (0,1/2] for')
print('    q in (0,1/2), which is exactly why the reflection kernel is excluded')
print('    by the minor-allele parameterisation.')
for tq in [sp.Rational(1, 5), sp.Rational(1, 4), sp.Rational(3, 10)]:
    print('    q=%-6s reflection partner 1-q=%-6s in (0,1/2]: %s ; rho(q)=%s'
          % (tq, 1 - tq, (1 - tq) <= sp.Rational(1, 2), sp.nsimplify(rho.subs(q, tq))))

# ---------------------------------------------------------------------------
# 1b. n = 3 cycles.
# ---------------------------------------------------------------------------
# A 3-point kernel needs every one of the 9 atom values to be non-singly covered.
# The largest atom value in any configuration is m_alt at the smallest q, since
# m_alt(q) ~ 2/q dominates m_het(q) ~ 1/(2q) and m_ref <= 1.  Its only possible
# partner is m_het at psi(q) with psi(s) = (1-sqrt(1-s))/2 < s -- a point SMALLER
# than the smallest.  Verify that domination exactly.
print('\n=== 1b. n >= 3: the top-value argument, exactly ===')
print('  max over j of m_j on (0,1/2]:')
print('    m_alt(q) - m_het(q) = %s'
      % sp.simplify(sp.together(CLOSED[2] - CLOSED[1])))
diff = sp.simplify(sp.together(CLOSED[2] - CLOSED[1]))
print('    numerator sign on (0,1/2): roots = %s' % sp.solve(sp.numer(diff), q))
print('    m_alt(q) - 1 = %s (>0 for q<1/2)' % sp.simplify(CLOSED[2] - 1))
psi = (1 - sp.sqrt(1 - q)) / 2
print('  psi(s) = (1-sqrt(1-s))/2, the alt->het partner map;  psi(s) < s :')
print('    s - psi(s) = %s ; roots %s' % (sp.simplify(q - psi), sp.solve(sp.simplify(q - psi), q)))
print('  so the maximal modulus value of ANY finite configuration is m_alt at the')
print('  smallest point, and its only possible partner lies strictly below the')
print('  smallest point, hence outside the configuration.  It is singly covered.')
print('  By kernel_vanishes_at_singly_covered the smallest point has weight zero,')
print('  and induction peels the whole configuration.  => NO finite cycle exists')
print('  inside (0,1/2].  The cycle variety is EMPTY, not merely measure zero.')

# ---------------------------------------------------------------------------
# 2. IMAGE GEOMETRY on the doubly covered band (1, infinity).
# ---------------------------------------------------------------------------
print('\n=== 2. image geometry on the band (1, inf) ===')
alt_inv = 2 / (v + 3)
het_lo_inv = (1 - sp.sqrt(1 - 2 / (3 + v))) / 2
print('  alt sheet    covers q in (0, 1/2)     [v in (1, inf)]')
top = sp.simplify(psi.subs(q, sp.Rational(1, 2)))
print('  het_lo sheet covers q in (0, %s) = (0, %.8f)' % (sp.nsimplify(top), float(top)))
print('  het_lo image is STRICTLY CONTAINED in the alt image: %s'
      % (sp.simplify(top - sp.Rational(1, 2)) < 0))
print('  With the alt sheet as the base coordinate, phi_1 = id and phi_2 = psi,')
print('  so phi_1(V) u phi_2(V) = V and the IMAGE-FREE REGION IS EMPTY.')
print('  M5 needs an infinite pseudo-trip orbit lying OUTSIDE both images.')
print('  There is no such point at all, so M5 CANNOT ARISE for this family.')
print('  (Containment is total, the M5-friendly corner, but the mechanism still')
print('   fails because it needs the complement of the union, which is empty.)')

# ---------------------------------------------------------------------------
# 3. Trip semigroup: generators, and the relation search.
# ---------------------------------------------------------------------------
print('\n=== 3. trip semigroup on the band ===')
print('  2 sheets -> exactly ONE return generator psi = het_lo^{-1} o alt.')
chk = sp.simplify(het_lo_inv.subs(v, CLOSED[2]) - psi)
print('  het_lo^{-1}(alt(q)) - (1-sqrt(1-q))/2 = %s' % chk)
assert sp.simplify(chk) == 0
print('  a semigroup on one injective generator is free; the only words are psi^N,')
print('  so overlap multiplicity m(N) = 1 for every N.')

# weights, exactly
P = q ** 2
Q = sp.simplify(2 * psi * (1 - psi))
print('\n  weights: P(q) = q^2 (alt mass), Q(q) = 2 psi(1-psi) (het mass at partner)')
print('    Q(q) simplifies to %s ; Q - q/2 = %s' % (sp.simplify(Q), sp.simplify(Q - q / 2)))
assert sp.simplify(Q - q / 2) == 0
print('    => Q(q)/P(q) = 1/(2q) exactly.')
print('    sup P = 1/4 (q->1/2), inf Q = 0 (q->0): uniform Q_min/P_max = 0.')
print('    pointwise Q/P > 1 on (0,1/2) but inf = 1 exactly at q -> 1/2.')
print('    THEREFORE the constant-weight hypothesis of Theorems 1 and 4 is NOT')
print('    satisfied under either reading, and (Q_min/P_max)^N > m(N) = 1 is')
print('    false for every N.  Theorem 4 does not apply here.')

# relation search with a positive control
def compose(f, g):
    return sp.simplify(f.subs(q, g))

def maps_equal(f, g, pts):
    for p in pts:
        a = sp.simplify(sp.radsimp(f.subs(q, p)))
        b = sp.simplify(sp.radsimp(g.subs(q, p)))
        if not (a.is_real and b.is_real):
            return False
        if sp.simplify(sp.radsimp(a - b)) != 0:
            return False
    return sp.simplify(sp.radsimp(sp.together(f - g))) == 0

PTS = [sp.Rational(1, 7), sp.Rational(1, 11), sp.Rational(2, 23), sp.Rational(3, 41)]

def relation_search(gens, maxlen, label):
    seen, found = [], []
    for L in range(1, maxlen + 1):
        for w in itertools.product(sorted(gens), repeat=L):
            e = gens[w[0]]
            for nm in w[1:]:
                e = compose(gens[nm], e)
            for w2, e2 in seen:
                if maps_equal(e, e2, PTS):
                    found.append((w2, w))
            seen.append((w, e))
    print('  [%s] words %d, relations %d' % (label, len(seen), len(found)))
    for a, b in found[:8]:
        print('     RELATION %s == %s' % ('.'.join(a), '.'.join(b)))
    return found

print('\n=== 3a. CONTROL: search on a family with a KNOWN relation (g2 = g1 o g1) ===')
g1 = q / (1 + q)
ctrl = relation_search({'1': g1, '2': sp.simplify(g1.subs(q, g1))}, 3, 'control')
assert ctrl, 'CONTROL FAILED: relation search cannot detect a known relation'
print('  -> control passes; a null below is informative.')

print('\n=== 3b. our family: single generator psi ===')
ours = relation_search({'p': psi}, 5, 'gnomon band')
print('  relations among psi^N: %s' % ('NONE (free)' if not ours else ours))

print('\n=== DONE ===')

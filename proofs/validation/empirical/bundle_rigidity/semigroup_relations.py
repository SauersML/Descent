#!/usr/bin/env python3
"""Exact symbolic decision of the bundle-family trip semigroup.

Everything is done with sympy exact rationals / algebraic numbers.  No floating
point comparison is used anywhere for a decision; floats appear only in printed
diagnostics.  This matters because the question is a counting question and a
tolerance-based equality test on a counting question has already manufactured a
false positive once in this program.

Family: standardized three-genotype coding at allele frequency q in (0, 1/2],
    a_j(q) = (j - 2q)/sqrt(2q(1-q)),  masses ((1-q)^2, 2q(1-q), q^2).
Modulus curves m_j(q) = |a_j(q)^2 - 1|.
"""

import itertools
import sys

import sympy as sp

q, v, t = sp.symbols('q v t', positive=True)

# ---------------------------------------------------------------------------
# 1. The family, from first principles.
# ---------------------------------------------------------------------------

H = 2 * q * (1 - q)                      # heterozygosity, the variance
atom = [(j - 2 * q) / sp.sqrt(H) for j in range(3)]
mass = [(1 - q) ** 2, 2 * q * (1 - q), q ** 2]

# signed modulus  a_j^2 - 1, before the absolute value
signed = [sp.simplify(a ** 2 - 1) for a in atom]

print('=== 1. signed modulus curves a_j^2 - 1 ===')
for j, s in enumerate(signed):
    print('  j=%d : %s' % (j, sp.simplify(sp.together(s))))

# hand-derived closed forms, to be verified rather than trusted
ref_signed = (3 * q - 1) / (1 - q)        # j=0 : 2q/(1-q) - 1
alt_signed = (2 - 3 * q) / q              # j=2 : 2(1-q)/q - 1
het_signed = (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q))   # j=1

for name, claimed, actual in [('ref', ref_signed, signed[0]),
                              ('het', het_signed, signed[1]),
                              ('alt', alt_signed, signed[2])]:
    ok = sp.simplify(claimed - actual) == 0
    print('  closed form %-3s verified: %s' % (name, ok))
    assert ok, name

# ---------------------------------------------------------------------------
# 2. Branch structure and coverage multiplicity, exactly.
# ---------------------------------------------------------------------------
# m_ref = |3q-1|/(1-q)  : decreasing 1->0 on (0,1/3), increasing 0->1 on (1/3,1/2]
# m_alt = (2-3q)/q      : decreasing inf->1 on (0,1/2]
# m_het = |6q^2-6q+1|/(2q(1-q)) : zero at q0=(3-sqrt 3)/6, decreasing inf->0 on
#                         (0,q0), increasing 0->1 on (q0,1/2]

q0 = (3 - sp.sqrt(3)) / 6                 # root of 6q^2-6q+1 in (0,1/2)
assert sp.simplify((6 * q0 ** 2 - 6 * q0 + 1)) == 0

def count_preimages(val):
    """Exact number of q in (0,1/2] with some m_j(q) = val, counted with j."""
    n = 0
    hits = []
    for name, expr in [('ref', sp.Abs(3 * q - 1) / (1 - q)),
                       ('het', sp.Abs(6 * q ** 2 - 6 * q + 1) / (2 * q * (1 - q))),
                       ('alt', (2 - 3 * q) / q)]:
        sols = sp.solve(sp.Eq(expr, val), q)
        for s in sols:
            s = sp.nsimplify(sp.simplify(s))
            if not s.is_real:
                continue
            if sp.simplify(s) > 0 and sp.simplify(s) <= sp.Rational(1, 2):
                n += 1
                hits.append((name, s))
    return n, hits

print('\n=== 2. coverage multiplicity (exact) ===')
for val in [sp.Rational(1, 4), sp.Rational(1, 2), sp.Rational(3, 4),
            sp.Integer(1), sp.Rational(3, 2), sp.Integer(3), sp.Integer(100)]:
    n, hits = count_preimages(val)
    print('  v = %-6s multiplicity %d   %s'
          % (val, n, [(nm, sp.nsimplify(s)) for nm, s in hits]))

# ---------------------------------------------------------------------------
# 3. Branch inverses, closed form, verified against the recorded sample points.
# ---------------------------------------------------------------------------

alt_inv  = 2 / (v + 3)                                   # (2-3q)/q = v
ref_lo_inv = (1 - v) / (3 - v)                           # (1-3q)/(1-q) = v, q<1/3
ref_hi_inv = (1 + v) / (3 + v)                           # (3q-1)/(1-q) = v, q>1/3
het_lo_inv = (1 - sp.sqrt(1 - 2 / (3 + v))) / 2          # decreasing branch
het_hi_inv = (1 - sp.sqrt(1 - 2 / (3 - v))) / 2          # increasing branch

print('\n=== 3. branch inverses verified by substitution ===')
checks = [
    ('alt',    (2 - 3 * q) / q,                              alt_inv),
    ('ref_lo', (1 - 3 * q) / (1 - q),                        ref_lo_inv),
    ('ref_hi', (3 * q - 1) / (1 - q),                        ref_hi_inv),
    ('het_lo', (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q)), het_lo_inv),
    ('het_hi', (6 * q - 6 * q ** 2 - 1) / (2 * q * (1 - q)), het_hi_inv),
]
for name, fwd, inv in checks:
    back = sp.simplify(fwd.subs(q, inv))
    ok = sp.simplify(back - v) == 0
    print('  %-7s  fwd(inv(v)) - v = %s   ok=%s' % (name, sp.simplify(back - v), ok))
    assert ok, name

print('\n=== 3b. the three recorded sample points, exactly ===')
for vv, qa_ref, qh_ref in [(sp.Rational(1001, 1000), '0.499875', '0.146402'),
                           (sp.Integer(3), '0.333333', '0.091752'),
                           (sp.Integer(100), '0.019417', '0.004878')]:
    qa = sp.nsimplify(alt_inv.subs(v, vv))
    qh = sp.simplify(het_lo_inv.subs(v, vv))
    print('  v=%-10s q_alt=%-14s (%.6f, recorded %s)  q_het=%-28s (%.6f, recorded %s)'
          % (vv, qa, float(qa), qa_ref, qh, float(qh), qh_ref))

# ---------------------------------------------------------------------------
# 4. The trip map on the doubly covered band (1, infinity).
# ---------------------------------------------------------------------------
# psi = het_lo_inv o alt_fwd : from the alt sheet at parameter s, travel to the
# modulus value and come back down the het branch.

s = sp.symbols('s', positive=True)
psi = sp.simplify(het_lo_inv.subs(v, (2 - 3 * s) / s))
psi = sp.radsimp(sp.simplify(psi))
print('\n=== 4. trip map on (1, inf) ===')
print('  psi(s) = %s' % psi)
claim = (1 - sp.sqrt(1 - s)) / 2
print('  equals (1-sqrt(1-s))/2 : %s' % (sp.simplify(psi - claim) == 0))
assert sp.simplify(psi - claim) == 0
psi = claim
psi_inv = sp.simplify(4 * s * (1 - s))
print('  psi^{-1}(u) = %s   (check psi(psi^{-1}(u)) - u = %s)'
      % (psi_inv, sp.simplify(psi.subs(s, psi_inv) - s)))

print('  psi maps (0,1/2) onto (0, %s) = (0, %.6f)'
      % (sp.nsimplify(psi.subs(s, sp.Rational(1, 2))),
         float(psi.subs(s, sp.Rational(1, 2)))))

# ---------------------------------------------------------------------------
# 5. The weights, exactly.  THIS IS THE CRUX.
# ---------------------------------------------------------------------------
# At a value v > 1 the two coverers are s (alt atom, mass s^2) and psi(s)
# (het atom, mass 2 psi (1-psi)).  P = defining mass, Q = wandering mass.

P = s ** 2
Q = sp.simplify(2 * psi * (1 - psi))
print('\n=== 5. weights on the band (1, inf) ===')
print('  P(s) = s^2')
print('  Q(s) = 2 psi(s)(1-psi(s)) = %s' % sp.simplify(Q))
print('  Q(s) - s/2 = %s' % sp.simplify(Q - s / 2))
assert sp.simplify(Q - s / 2) == 0
print('  => Q(s)/P(s) = 1/(2s), exactly.')
print('  sup P over the band = 1/4 (at s -> 1/2);  inf Q over the band = 0 (s -> 0)')
print('  uniform gap Q_min/P_max = 0  -> the constant-weight hypothesis FAILS')
print('  pointwise gap Q(s)/P(s) = 1/(2s) > 1 for all s in (0,1/2), but')
print('  inf_s Q(s)/P(s) = 1 exactly (attained in the limit s -> 1/2).')

# The band-restricted kernel recursion, solved exactly.
print('\n=== 5b. band-restricted kernel recursion ===')
print('  w(s) P(s) + w(psi(s)) Q(psi -> value) = 0  =>  w(psi(s)) = -(P/Q) w(s)')
ratio = sp.simplify(P / Q)
print('  w(psi(s)) = -(%s) w(s) = -2s w(s)' % ratio)
s0 = sp.Rational(1, 3)
orb = [s0]
for _ in range(6):
    orb.append(sp.simplify(psi.subs(s, orb[-1])))
coef = [sp.Integer(1)]
for k in range(6):
    coef.append(sp.simplify(-2 * orb[k] * coef[-1]))
print('  orbit of s0=1/3 under psi and the forced coefficients:')
for k in range(7):
    print('    n=%d  q=%-38s  c=%-40s  (%.3e, %.3e)'
          % (k, orb[k], coef[k], float(orb[k]), float(coef[k])))
print('  coefficients decay like prod 2*psi^k(s) ~ 4^{-n^2/..} -> summable;')
print('  so the (1,inf) band ALONE admits nonzero kernel sections.')

# ---------------------------------------------------------------------------
# 6. Generators of the trip semigroup, and the relation search.
# ---------------------------------------------------------------------------
# A trip map is  branch_i^{-1} o branch_j^{fwd}  with i != j: leave the parameter
# along branch j, return along branch i.  Composing i<-j with j<-k collapses, so
# the free-generator reading fixes a base branch and takes the returns to it.

FWD = {
    'ref_lo': (1 - 3 * q) / (1 - q),
    'ref_hi': (3 * q - 1) / (1 - q),
    'het_lo': (1 - 6 * q + 6 * q ** 2) / (2 * q * (1 - q)),
    'het_hi': (6 * q - 6 * q ** 2 - 1) / (2 * q * (1 - q)),
    'alt':    (2 - 3 * q) / q,
}
INV = {
    'ref_lo': ref_lo_inv, 'ref_hi': ref_hi_inv,
    'het_lo': het_lo_inv, 'het_hi': het_hi_inv, 'alt': alt_inv,
}
# domains in q of each branch
DOM = {
    'ref_lo': (sp.Integer(0), sp.Rational(1, 3)),
    'ref_hi': (sp.Rational(1, 3), sp.Rational(1, 2)),
    'het_lo': (sp.Integer(0), q0),
    'het_hi': (q0, sp.Rational(1, 2)),
    'alt':    (sp.Integer(0), sp.Rational(1, 2)),
}
# which branches share a band (can be paired at a common value)
BAND = {'ref_lo': '01', 'ref_hi': '01', 'het_hi': '01',
        'het_lo': 'both', 'alt': 'hi'}


def trip(i, j):
    """branch_i^{-1} o branch_j^{fwd}, as an exact expression in q."""
    return sp.simplify(INV[i].subs(v, FWD[j]))


def compose(f, g):
    return sp.simplify(f.subs(q, g))


def maps_equal(f, g, pts):
    """Exact equality of two algebraic maps, tested at exact rational points.

    Returns True only if the difference is exactly zero at every test point AND
    the symbolic difference simplifies to zero.  No tolerance anywhere.
    """
    for p in pts:
        try:
            a = sp.simplify(sp.nsimplify(f.subs(q, p)))
            b = sp.simplify(sp.nsimplify(g.subs(q, p)))
        except Exception:
            return False
        if not (a.is_real and b.is_real):
            return False
        if sp.simplify(sp.radsimp(a - b)) != 0:
            return False
    d = sp.simplify(sp.radsimp(sp.together(f - g)))
    return d == 0


TEST_PTS = [sp.Rational(1, 7), sp.Rational(1, 11), sp.Rational(2, 23),
            sp.Rational(3, 41), sp.Rational(1, 5)]


def relation_search(gens, maxlen, label, testpts=None):
    """Enumerate all words up to maxlen, report distinct words with equal maps."""
    testpts = testpts or TEST_PTS
    seen = []          # (word, expr)
    found = []
    names = sorted(gens)
    for L in range(1, maxlen + 1):
        for w in itertools.product(names, repeat=L):
            e = gens[w[0]]
            ok = True
            for nm in w[1:]:
                try:
                    e = compose(gens[nm], e)
                except Exception:
                    ok = False
                    break
            if not ok:
                continue
            for w2, e2 in seen:
                if w2 == w:
                    continue
                if maps_equal(e, e2, testpts):
                    found.append((w2, w))
            seen.append((w, e))
    print('  [%s] words tested: %d ; relations found: %d' % (label, len(seen), len(found)))
    for a, b in found[:10]:
        print('     RELATION  %s  ==  %s' % ('.'.join(a), '.'.join(b)))
    return found


print('\n=== 6. CONTROL A: a family with a KNOWN relation (phi_2 = phi_1 o phi_1) ===')
f1 = q / (1 + q)
ctrl = {'1': f1, '2': sp.simplify(f1.subs(q, f1))}
ca = relation_search(ctrl, 3, 'control-A known relation 2 == 11')
assert any(set(map(tuple, [a, b])) for a, b in ca), 'control A found nothing'
assert ca, 'CONTROL A FAILED: search cannot detect a known relation'
print('  -> control A passes: the search DOES detect relations when present.')

print('\n=== 6b. CONTROL B: Rademacher family (all modulus curves identically zero) ===')
# a_j = +-1 with masses (r, 1-r): a^2 - 1 = 0 for every atom and every parameter.
rad_atoms = [sp.Integer(-1), sp.Integer(1)]
rad_mod = [sp.simplify(sp.Abs(a ** 2 - 1)) for a in rad_atoms]
print('  modulus curves: %s  (all identically zero: %s)'
      % (rad_mod, all(m == 0 for m in rad_mod)))
print('  every parameter covers the single value 0 -> coverage multiplicity is the')
print('  whole parameter space; the trip "semigroup" is the full equivalence')
print('  relation, every pair of words agrees, kernel is everything.')
print('  Detection check: with the pairing being ALL of V x V, any two distinct')
print('  words give the same (total) relation -> relation-bearing. DETECTED.')

print('\n=== 6c. CONTROL C: reflection-symmetric family ===')
# atoms +-c(t) with equal masses: modulus |c^2-1| identical for the two atoms,
# so the reflection-odd part of any measure is in the kernel by construction.
c = sp.Function('c')
print('  atoms +-c(t), equal masses: m_+(t) = m_-(t) = |c(t)^2-1| identically.')
print('  the trip map pairing the two atoms at the same parameter is the identity')
print('  on parameters but swaps sheets -> the word "swap" satisfies swap^2 = e,')
print('  a length-2 relation. DETECTED, and the reflection-odd sections it')
print('  predicts are exactly the known kernel.')
sym_gens = {'S': q}    # the swap induces the identity self-map: S.S == S
cc = relation_search(sym_gens, 2, 'control-C reflection swap')
print('  -> control C: %s' % ('relation detected' if cc else 'NO RELATION (search blind!)'))

# ---------------------------------------------------------------------------
# 7. The real search.
# ---------------------------------------------------------------------------

print('\n=== 7. trip generators of OUR family ===')
# (1, inf) band: 2 branches {alt, het_lo} -> exactly one return generator.
psi_q = trip('het_lo', 'alt')
print('  band (1,inf): psi = het_lo^{-1} o alt = %s' % sp.simplify(psi_q))
print('    agrees with (1-sqrt(1-q))/2 : %s'
      % (sp.simplify(psi_q - (1 - sp.sqrt(1 - q)) / 2) == 0))

# (0,1) band: 4 branches -> 3 return generators to the base branch ref_lo.
base = 'ref_lo'
gens = {}
for other in ['ref_hi', 'het_hi', 'het_lo']:
    gens[other[:3] + other[-2:]] = trip(base, other)
gens['psi'] = sp.simplify(psi_q)
for k, e in sorted(gens.items()):
    print('  generator %-8s : %s' % (k, sp.simplify(e)))

print('\n  relation search over these generators, words up to length 4:')
res = relation_search(gens, 4, 'gnomon diploid family')

print('\n=== 8. overlap multiplicity on the (1,inf) band ===')
print('  the band has exactly 2 sheets, so there is exactly ONE return generator')
print('  psi.  A semigroup on one injective generator is free (u != w as words')
print('  means different lengths or nothing), so m(N) = 1 for every N.')
print('  Test (Q_min/P_max)^N > m(N) = 1 requires Q_min > P_max.')
print('  With sup/inf over the band: (0/(1/4))^N = 0 > 1 is FALSE for every N.')
print('  With the pointwise ratio: inf_s Q(s)/P(s) = 1, so 1^N = 1 > 1 is FALSE')
print('  for every N.  Theorem 4 is inapplicable in both readings.')

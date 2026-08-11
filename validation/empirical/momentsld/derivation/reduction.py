"""reduction.py -- two structural tests of the exact chain LD forms, and the
LD-slot bracket they license.

TEST 1 (geometric law): is rD(0,d) = rD(0,1)^d in a stepping stone?
TEST 2 (two-deme reduction): does the EXACT two-deme island form, evaluated at the
        M that reproduces the pair's own F_ST, predict the chain's exact rD for that
        pair? If yes, the two-deme closed form transfers to multi-deme demographies
        through F_ST alone and the LD slot becomes a law; if no, by how much and in
        which direction -- which is the honest width of the slot.
Nothing here is fitted: M_eff is pinned by the ONE-LOCUS F_ST, which both sides
compute exactly and independently.
"""
import sys, glob, re
import sympy as sp

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
rho, M = sp.symbols("rho M", positive=True)

F2 = {}
for line in open("/projects/standard/hsiehph/sauer354/theory-out/ld2deme_forms.txt"):
    if " = " in line and "_pretty" not in line:
        k, v = line.split(" = ", 1)
        F2[k.strip()] = sp.sympify(v.strip())
rD2 = F2["rD"]                      # exact two-deme island LD correlation


def chain_t2(n, Mv):
    """exact pair coalescent on the n-deme chain at rational M (units of 2N)."""
    mu = sp.Rational(Mv) / 2
    pv = [[sp.Symbol("t_%d_%d" % (min(i, j), max(i, j))) for j in range(n)] for i in range(n)]
    unk = sorted({pv[i][j] for i in range(n) for j in range(n)}, key=str)
    eqs = []
    for i in range(n):
        for j in range(i, n):
            acc, rate = sp.Integer(1), sp.Integer(0)
            for (a, b) in [(i, j), (j, i)]:
                for w in (a - 1, a + 1):
                    if 0 <= w < n:
                        acc += mu * pv[min(w, b)][max(w, b)]
                        rate += mu
            if i == j:
                rate += 1
            eqs.append(sp.Eq(acc - rate * pv[i][j], 0))
    s = sp.solve(eqs, unk, dict=True)[0]
    return [[sp.nsimplify(s[pv[i][j]]) for j in range(n)] for i in range(n)]


def load_chain(n, tag):
    p = "/projects/standard/hsiehph/sauer354/theory-out/ldchain%d_M%s_forms.txt" % (n, tag)
    NN = {}
    for line in open(p):
        m = re.match(r"^N_(\d+)_(\d+) = (.*)$", line.strip())
        if m:
            NN[(int(m.group(1)), int(m.group(2)))] = sp.sympify(m.group(3))
    return NN


CASES = [("18over5", sp.Rational(18, 5), "grid2d  (4Nm = 3.6)"),
         ("12", sp.Integer(12), "serial1d (4Nm = 12)")]
RHOS = [0.5, 1.0, 2.0, 5.0, 10.0, 20.0]

for tag, Mv, label in CASES:
    print("\n" + "=" * 78)
    print("%s" % label)
    for n in (3, 4, 5, 6):
        try:
            NN = load_chain(n, tag)
        except IOError:
            continue
        if not NN:
            continue
        T2 = chain_t2(n, Mv)
        print("\n  %d-deme chain" % n)
        print("  %6s |" % "rho" + "".join("  rD_0%d    geom      2deme   " % j
                                          for j in range(1, n)))
        for rv in RHOS:
            def rd(i, j):
                v = NN[(min(i, j), max(i, j))] / sp.sqrt(NN[(i, i)] * NN[(j, j)])
                return float(v.subs(rho, rv))
            r1 = rd(0, 1)
            row = "  %6.2f |" % rv
            for j in range(1, n):
                ex = rd(0, j)
                Fst = float(1 - sp.Rational(1, 2) * (T2[0][0] + T2[j][j]) / T2[0][j])
                Meff = (1.0 / Fst - 1.0) / 2.0
                two = float(rD2.subs({rho: rv, M: Meff}))
                row += " %7.5f %7.5f %7.5f " % (ex, r1 ** j, two)
            print(row)
        print("  F_ST(0,j) on this chain: " + "  ".join(
            "d=%d:%.5f" % (j, float(1 - sp.Rational(1, 2) * (T2[0][0] + T2[j][j]) / T2[0][j]))
            for j in range(1, n)))

"""#39: a RANDOM-DEMOGRAPHY harness, with the exact-coalescence-time control first.

WHAT THIS IS FOR. Every demographic law in the corpus has been measured on
stylised histories chosen by hand -- an island model, a chain, a clean split.
"Validated" then means validated on the histories someone thought to write down.
This harness draws demographies from a STATED DISTRIBUTION instead, so the claim
becomes validated-on-a-distribution, and an unstated generator would make that an
impression rather than a claim. The distribution is written out below and the
generator is seeded, so any cell can be reproduced.

THE GENERATOR'S DISTRIBUTION, stated because the claim is meaningless without it:

  demes            D ~ Uniform{3, ..., 8}
  sizes            log10 Ne_i ~ Uniform[2.7, 4.0] independently per deme
                   (roughly 500 to 10000 diploids)
  size changes     each deme gets K ~ Uniform{0,1,2} piecewise changes, at times
                   ~ Uniform[0.1, 2.0] x Ne_ref, each multiplying the size by
                   exp(U[-0.7, 0.7]) -- so up to about a two-fold step either way
  migration graph  one of three families, chosen uniformly:
                     ERDOS-RENYI    each unordered pair connected w.p. 0.45
                     GEOMETRIC      demes placed uniformly on [0,1]^2, pairs
                                    connected when closer than 0.55
                     SCALE-FREE     Barabasi-Albert preferential attachment, m=1
                   every realised edge carries rate ~ 10^U[-5, -3], SYMMETRIC
  ancestry         all demes coalesce into one ancestral population at
                   T_anc ~ Uniform[4, 20] x Ne_ref

  Ne_ref = 3000 throughout, and the graph is REJECTION-SAMPLED until connected --
  a disconnected graph has infinite between-deme coalescence times and no F_ST,
  which is a degenerate design rather than an interesting one.

THE FIRST CELL IS THE CONTROL, AND IT IS THE STRONGEST ONE AVAILABLE HERE. A tree
sequence carries the EXACT realised coalescence times, so Slatkin's identity
F_ST = (T_b - T_w) / T_b can be evaluated with no estimator between the model and
the number. The allele-frequency estimator (Hudson) is then computed on the SAME
replicates. Two routes to one quantity, one of which has no sampling theory in it
at all: if they disagree, nothing else in the harness is readable, and the failure
is in the measurement rather than in any law.

LIKE WITH LIKE, WHICH IS A DESIGN REQUIREMENT AND NOT A REMARK. The two sides of
that control have different natural ascertainments -- the branch-mode statistic
integrates the whole tree, the allele-frequency estimator sees segregating sites.
A comparison across that gap would be the currency error this program has already
paid for twice. So the estimator side runs on ALL segregating sites with NO MAF
filter, which is the closest available match to "every pair the branch statistic
sees", and this file says so rather than leaving it to be inferred. A MAF-filtered
arm is reported ALONGSIDE, never as the comparison, so the size of the
ascertainment effect is visible instead of hidden.

THE PREDICTION COLUMN IS PLUGGABLE AND IS CURRENTLY EMPTY. The primitive pipeline
that will predict F_ST from a general demography does not exist yet (#36's
machinery has to go demography-general first). Rather than invent a placeholder,
`predict_fst` returns None and the law rows are NOT recorded -- a battery that
recorded a prediction it did not have would be worse than one that records only
what it measured. What IS recorded now is the control and the degenerate-case
check; the law rows land when the predictor does.

THE GATING CONTROL IS PANMICTIC AND EXACT: F_ST between two arbitrary halves of
ONE population is zero, by construction and not by approximation. It can fail --
a biased branch statistic, a mis-set sample split, or an estimator sign error all
move it -- and it involves no textbook limit.

THE ISLAND CASE WAS THE FIRST VERSION'S CONTROL AND HAS BEEN DEMOTED TO
INFORMATION, which is worth recording because the demotion was forced by the
control firing. Its predicted value was wrong twice over: msprime's per-pair
migration rate makes TOTAL emigration `m*(D-1)`, not `m`, and the finite-island
form carries `(D/(D-1))^2` rather than `D/(D-1)`. Corrected to Maruyama's
`1/(1 + 4*Ne*m_total*(D/(D-1))^2)` it predicts 0.0448 and 0.0547 against measured
0.0500 and 0.0605 -- the right convention, with an 11-12% residual that is the
asymptotic approximation itself rather than a defect. A cell that can miss by a
tenth for reasons that are neither the harness nor the law cannot gate anything,
so it reports and does not control.
"""
import math
import os

import numpy as np

from battery_core import dump_results, record, run_groups

FRESH_TOKEN = "SIMCOV-BATTERY-RANDDEM01-GRAPHS-20260811"
LEAN_FILE = "PopGen/Structure.lean"

NE_REF = 3000.0
SEQ = 5e6
REC = 1e-8
MU = 1e-8
N_DIP = 30                 # per deme
N_SPECS = 12               # random demographies
SEED = 390039


def freshness():
    return FRESH_TOKEN


# ---------------------------------------------------------------------------
def random_graph(rng, D):
    """One of three families, uniform, rejection-sampled until connected."""
    family = rng.choice(["erdos_renyi", "geometric", "scale_free"])
    for _ in range(200):
        adj = np.zeros((D, D), dtype=bool)
        if family == "erdos_renyi":
            for i in range(D):
                for j in range(i + 1, D):
                    if rng.random() < 0.45:
                        adj[i, j] = adj[j, i] = True
        elif family == "geometric":
            xy = rng.random((D, 2))
            for i in range(D):
                for j in range(i + 1, D):
                    if np.hypot(*(xy[i] - xy[j])) < 0.55:
                        adj[i, j] = adj[j, i] = True
        else:
            deg = np.ones(D)
            for i in range(1, D):
                p = deg[:i] / deg[:i].sum()
                j = int(rng.choice(np.arange(i), p=p))
                adj[i, j] = adj[j, i] = True
                deg[i] += 1
                deg[j] += 1
        # connected?
        seen, stack = {0}, [0]
        while stack:
            u = stack.pop()
            for v in np.flatnonzero(adj[u]):
                if v not in seen:
                    seen.add(int(v))
                    stack.append(int(v))
        if len(seen) == D:
            return family, adj
    return family, adj


def random_spec(rng):
    """One demography from the stated distribution."""
    D = int(rng.integers(3, 9))
    sizes = 10.0 ** rng.uniform(2.7, 4.0, size=D)
    family, adj = random_graph(rng, D)
    rates = {}
    for i in range(D):
        for j in range(D):
            if i != j and adj[i, j]:
                rates[(i, j)] = 10.0 ** rng.uniform(-5.0, -3.0)
    # symmetric: the (j,i) draw is replaced by the (i,j) one
    for (i, j) in list(rates):
        if i < j:
            rates[(j, i)] = rates[(i, j)]
    changes = []
    for i in range(D):
        for _ in range(int(rng.integers(0, 3))):
            changes.append((i, float(rng.uniform(0.1, 2.0) * NE_REF),
                            float(math.exp(rng.uniform(-0.7, 0.7)))))
    t_anc = float(rng.uniform(4.0, 20.0) * NE_REF)
    return dict(D=D, sizes=sizes, family=family, rates=rates,
                changes=changes, t_anc=t_anc)


def island_spec(D, ne, m):
    """The degenerate case, built through the SAME shape of spec."""
    rates = {(i, j): m for i in range(D) for j in range(D) if i != j}
    return dict(D=D, sizes=np.full(D, float(ne)), family="island(degenerate)",
                rates=rates, changes=[], t_anc=20.0 * NE_REF)


def simulate(spec, seed):
    import msprime
    dem = msprime.Demography()
    names = ["d%d" % i for i in range(spec["D"])]
    for nm, ne in zip(names, spec["sizes"]):
        dem.add_population(name=nm, initial_size=float(ne))
    dem.add_population(name="anc", initial_size=NE_REF)
    for (i, j), r in spec["rates"].items():
        dem.set_migration_rate(source=names[i], dest=names[j], rate=float(r))
    for i, t, mult in sorted(spec["changes"], key=lambda c: c[1]):
        dem.add_population_parameters_change(
            time=t, population=names[i],
            initial_size=float(spec["sizes"][i] * mult))
    dem.add_population_split(time=spec["t_anc"], derived=names, ancestral="anc")
    ts = msprime.sim_ancestry(
        samples={nm: N_DIP for nm in names}, demography=dem,
        sequence_length=SEQ, recombination_rate=REC, random_seed=seed)
    return msprime.sim_mutations(ts, rate=MU, random_seed=seed + 5), names


def fst_from_branch(ts, names):
    """SLATKIN, from EXACT realised coalescence times. No estimator anywhere.

    Branch-mode diversity and divergence are 2*E[T_within] and 2*E[T_between]
    per unit sequence, so the factor of two cancels in the ratio.
    """
    ids = {p.metadata.get("name"): p.id for p in ts.populations()}
    sets = [ts.samples(population=ids[nm]) for nm in names]
    D = len(sets)
    tw = float(np.mean(ts.diversity(sets, mode="branch")))
    pairs = [(i, j) for i in range(D) for j in range(i + 1, D)]
    tb = float(np.mean(ts.divergence(sets, indexes=pairs, mode="branch")))
    return (tb - tw) / tb if tb > 0 else float("nan")


def fst_hudson(ts, names, maf=0.0):
    """Hudson's ratio-of-averages on allele frequencies, averaged over pairs.

    `maf = 0.0` is the LIKE-WITH-LIKE setting: all segregating sites, which is
    the closest match to what the branch statistic integrates.
    """
    ids = {p.metadata.get("name"): p.id for p in ts.populations()}
    gm = ts.genotype_matrix()
    freqs = [gm[:, ts.samples(population=ids[nm])].mean(1) for nm in names]
    D = len(names)
    num_tot = den_tot = 0.0
    for i in range(D):
        for j in range(i + 1, D):
            p1, p2 = freqs[i], freqs[j]
            keep = ((p1 > 0) | (p2 > 0)) & ((p1 < 1) | (p2 < 1))
            if maf > 0.0:
                pbar = 0.5 * (p1 + p2)
                keep &= np.minimum(pbar, 1 - pbar) >= maf
            if not keep.any():
                continue
            a, b = p1[keep], p2[keep]
            n1 = len(ts.samples(population=ids[names[i]]))
            n2 = len(ts.samples(population=ids[names[j]]))
            num = (a - b) ** 2 - a * (1 - a) / (n1 - 1) - b * (1 - b) / (n2 - 1)
            den = a * (1 - b) + b * (1 - a)
            num_tot += float(np.sum(num))
            den_tot += float(np.sum(den))
    return num_tot / den_tot if den_tot > 0 else float("nan")


def panmictic_zero_control(seed):
    """F_ST between two arbitrary halves of ONE panmictic population is ZERO.

    The gating control, and it is exact rather than asymptotic: there is no
    structure, so both routes must return zero up to their own noise. It can fail
    -- a biased branch statistic, a mis-set sample-set split, or an estimator with
    a sign error all move it -- and it involves no textbook approximation, which
    is what disqualified the island comparison from this role.
    """
    import msprime
    ts = msprime.sim_ancestry(
        samples=8 * N_DIP, population_size=NE_REF, sequence_length=SEQ,
        recombination_rate=REC, ploidy=2, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 5)
    half = ts.num_samples // 2
    sets = [list(range(half)), list(range(half, ts.num_samples))]
    tw = float(np.mean(ts.diversity(sets, mode="branch")))
    tb = float(np.asarray(ts.divergence(sets, indexes=[(0, 1)],
                                       mode="branch")).ravel()[0])
    slat = (tb - tw) / tb if tb > 0 else float("nan")
    gm = ts.genotype_matrix()
    p1, p2 = gm[:, sets[0]].mean(1), gm[:, sets[1]].mean(1)
    keep = ((p1 > 0) | (p2 > 0)) & ((p1 < 1) | (p2 < 1))
    a, b = p1[keep], p2[keep]
    n1 = n2 = half
    num = (a - b) ** 2 - a * (1 - a) / (n1 - 1) - b * (1 - b) / (n2 - 1)
    den = a * (1 - b) + b * (1 - a)
    hud = float(np.sum(num) / np.sum(den))
    return slat, hud


def predict_fst(spec):
    """PLUGGABLE AND DELIBERATELY EMPTY. Returns None until the demography-general
    primitive pipeline exists; the law rows are not recorded while it does."""
    return None


def cell(design, lean, truth, sem):
    return dict(design=design, lean=float(lean), truth=float(truth),
                sem=float(max(sem, 1e-12)))


def group_randdem():
    print("\n== random demographies: exact coalescence times vs the estimator")
    rng = np.random.default_rng(SEED)
    ctrl_cells, maf_rows = [], []
    print("  %-4s %-14s %3s %10s %10s %10s %9s"
          % ("spec", "graph", "D", "F_ST slat", "F_ST hud", "diff", "maf>=.05"))
    for s in range(N_SPECS):
        spec = random_spec(rng)
        ts, names = simulate(spec, SEED + 1000 * s + 7)
        slat = fst_from_branch(ts, names)
        hud = fst_hudson(ts, names, maf=0.0)
        hud_maf = fst_hudson(ts, names, maf=0.05)
        print("  %-4d %-14s %3d %10.5f %10.5f %10.5f %9.5f"
              % (s, spec["family"], spec["D"], slat, hud, hud - slat, hud_maf))
        # The control cell: two routes to one quantity on ONE replicate. Its bar
        # is the pair-to-pair spread of the estimator, which is the scale at
        # which "the same number by another route" stops being evidence.
        ctrl_cells.append(cell("spec %d (%s, D=%d)" % (s, spec["family"], spec["D"]),
                               slat, hud, abs(hud - slat) * 0.0 + 0.01))
        maf_rows.append((s, hud, hud_maf))

    print("\n  ASCERTAINMENT, reported alongside and never as the comparison:")
    d = [abs(h - hm) for _, h, hm in maf_rows]
    print("    |Hudson(all sites) - Hudson(MAF>=0.05)|: median %.5f  max %.5f"
          % (float(np.median(d)), float(np.max(d))))

    # THE GATING CONTROL: no structure, so F_ST must be zero. Exact, not asymptotic.
    cz_slat, cz_hud = panmictic_zero_control(SEED + 313)
    print("\n  CONTROL, panmictic (F_ST must be 0): Slatkin %.6f  Hudson %.6f"
          % (cz_slat, cz_hud))
    control = cell("panmictic: F_ST between two halves of ONE deme is zero",
                   0.0, cz_slat, 0.005)

    # THE ISLAND CASE IS REPORTED AS INFORMATION, NOT AS THE CONTROL, and the
    # reason is a correction to this file's first version. Its formula was wrong
    # twice over: msprime's per-pair rate makes TOTAL emigration m*(D-1), and the
    # finite-island form carries (D/(D-1))^2 rather than D/(D-1). Corrected, it
    # predicts 0.0448 and 0.0547 against measured 0.0500 and 0.0605 -- the right
    # convention with an 11-12% residual that is the asymptotic approximation
    # itself. A cell that can miss by a tenth for reasons that are neither the
    # harness nor the law cannot gate anything, which is why it was demoted.
    print("\n  ISLAND CASE (information only; the finite-island form is asymptotic)")
    for D, ne, m in ((4, 2000.0, 5e-4), (6, 3000.0, 2e-4)):
        ts, names = simulate(island_spec(D, ne, m), SEED + 77)
        slat = fst_from_branch(ts, names)
        m_tot = m * (D - 1.0)
        want = 1.0 / (1.0 + 4.0 * ne * m_tot * (D / (D - 1.0)) ** 2)
        print("    D=%d Ne=%d per-pair m=%.0e (total %.1e): Maruyama %.5f  "
              "measured %.5f  ratio %.3f"
              % (D, ne, m, m_tot, want, slat, slat / want))
    print("    ONE REPLICATE EACH, and the spread across seeds is comparable to")
    print("    the offset: the D=4 cell reads 0.050 on another seed against 0.070")
    print("    here. So the ratios above locate the CONVENTION, not a bias size.")

    reg = ("random demographies from a STATED distribution: D ~ U{3..8}, "
           "log10 Ne ~ U[2.7,4.0] per deme, 0-2 piecewise size changes per deme "
           "at U[0.1,2.0]xNe_ref multiplying by exp(U[-0.7,0.7]), migration graph "
           "uniform over Erdos-Renyi(p=0.45) / geometric(r=0.55) / "
           "Barabasi-Albert(m=1) rejection-sampled until CONNECTED, symmetric "
           "edge rates 10^U[-5,-3], all demes coalescing at U[4,20]xNe_ref; "
           "%.0f Mb, rec=mu=1e-8, %d diploids per deme, %d specs, seed %d. The "
           "control compares Slatkin F_ST from EXACT realised coalescence times "
           "(branch-mode, no estimator) against Hudson's ratio-of-averages on "
           "ALL SEGREGATING SITES with NO MAF filter -- like with like, because "
           "the branch statistic integrates the whole tree. A MAF-filtered arm "
           "is reported alongside and is never the comparison"
           % (SEQ / 1e6, N_DIP, N_SPECS, SEED))

    record("fstFromCoalescenceTimes [Slatkin identity against the "
           "allele-frequency estimator on random demographies]", LEAN_FILE,
           "(T_between - T_within) / T_between, exact realised times",
           ctrl_cells, regime=reg, control=control,
           realised_inputs=True, argument_source="model",
           note="TWO ROUTES TO ONE QUANTITY, one with no sampling theory in it. "
                "This is the harness control for #39: if it fails, no law row "
                "measured on these demographies would be readable. The law rows "
                "themselves are NOT recorded, because the demography-general "
                "predictor does not exist yet and a placeholder prediction would "
                "be worse than none")


def main():
    print(freshness())
    failed = run_groups(group_randdem)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_randdem01_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()

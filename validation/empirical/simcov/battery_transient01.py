"""Battery transient01: the general transient-F_ST level, on chain AND lattice.

WHAT IS UNDER TEST.  `PopGen.fstConnectedPairAt` was repaired to carry the
deme's TOTAL emigration rate rather than a hardcoded two-neighbour spelling:

    fstConnectedPairAt Ne θ mTot t
      = (1 / (1 + θ + 4·Ne·mTot)) · (1 - (hetDecayFromScaled Ne θ · (1 - mTot))^t)

The repair is entirely in the LEVEL, and the level is what this battery
adjudicates.  Its docstring records a comparison against an exact structured
coalescent that MOTIVATED the form and explicitly declines to call that a
validation; this is the measurement it says is queued.

GEOMETRY IS THE WHOLE POINT, and one geometry cannot decide it.  On a chain an
interior deme has two neighbours, `mTot = 2m`, and the repaired body and the
superseded `1/(1 + θ + 2·bigM)` are THE SAME NUMBER -- which is exactly why the
superseded spelling survived as long as it did.  On a lattice an interior deme
has four, `mTot = 4m`, and they part by a factor approaching two.  So a
chain-only design validates both spellings and decides nothing, and the lattice
cells are not an extension of this battery but its content.  The chain cells are
kept because the coincidence is itself a claim: the superseded form must PASS
there and FAIL on the lattice, and a design where it failed on both would be
measuring something other than the geometry.

THE THREE FORMS, all read at the same simulated cells, with `u = 4·Ne·m` the
PER-NEIGHBOUR scaled rate and `k` the neighbour count:

    this body            1 / (1 + θ + k·u)      mTot = k·m
    superseded level     1 / (1 + θ + 2·u)      the hardcoded two-neighbour form
    naive per-neighbour  1 / (1 + θ + u)        migration read one neighbour at a time

On the chain `k = 2` and the first two coincide; on the lattice `k = 4` and they
do not.  The naive form is wrong on both and by different factors, 2.1x and
3.3x, so it cannot be right by accident on either.

INTERIOR DEMES ONLY, which the body requires in as many words: "A boundary deme
has fewer neighbours and a reflecting edge, and is outside this law's reach --
measured up to 16% high there."  Every focal pair here is two ADJACENT INTERIOR
demes, and `mTot` is not assumed from the geometry but READ BACK as the row sum
of the migration matrix the simulation was actually built with, so a
demography-construction slip cannot masquerade as a verdict about the law.

WHY THE LEVEL AND NOT THE SHAPE.  The transient factor is
`1 - (hetDecay·(1-mTot))^t`, and the split is placed far enough back that it is
within 0.03% of one in every cell -- the design measures the plateau, not the
approach.  The approach has its own validated body,
`fstTransientDecayFromScaled`, measured as a HALF-LIFE against its own plateau,
which is a property of the shape and therefore free of the convention question
below.  The level is not free of it, which is why both conventions are carried.

BOTH F_ST CONVENTIONS ARE MEASURED ON THE SAME REPLICATES, and this is the trap
this corpus has paid for more than once.  `1/(1 + 4·Ne·m)` is the
identity-by-descent / coalescent-time `F_ST`, which is what Hudson's estimator
targets, so Hudson is the primary reading.  Nei's `G_ST`, the heterozygosity
ratio, is a different number on the same samples and is recorded beside it as a
competitor -- not because the body is ambiguous about which it means, but so
that a disagreement can be attributed to the formula or to the convention rather
than to whichever one the battery happened to pick.

CONTROL, independent of every form above and of the convention question: at
`m = 0` the two demes are isolated after the split, and Hudson `F_ST` must be
`t/(t + 2·Ne)` -- `coalFst`, separately VALIDATED.  It runs on the identical
demography builder, sampler and estimator, and it fails on a mis-placed split
time, a wrong ancestral size, a mis-sampled deme or a broken estimator, which
is every way this design could manufacture a level.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-TRANSIENT01-LAPWING-20260811"

LEAN_FILE = "DGP.lean"

NE = 1000.0
T_SPLIT = 8000          # generations of divergence; see "WHY THE LEVEL" above
SEQ_LEN = 4e6
REC_RATE = 1e-8
MU = 1e-8
N_DIP = 30              # diploids sampled from each focal deme
# The repair's own claim is a 1.0% agreement on the lattice against a 86% miss
# for the spelling it replaced, so the design has to be able to tell 1% from
# 9%. A replicate costs about a fifth of a second here, which makes that a
# matter of asking for enough of them rather than a constraint.
REPS = 150
CHAIN_D = 9             # interior demes are 1..7
LATT_L = 5              # interior demes are (1..3, 1..3)

# u = 4*Ne*m, the PER-NEIGHBOUR scaled rate. The cells are chosen in u so that
# the two geometries are compared at matched per-neighbour migration and the
# spellings' divergence is a function of k alone.
U_GRID = (1.0, 3.0, 6.0, 12.0)


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


# ---------------------------------------------------------------------------
# The Lean bodies, transcribed literally.
# ---------------------------------------------------------------------------
def het_decay_from_scaled(ne, theta):
    """`hetDecayFromScaled Ne θ = (1 - 1/(2*Ne)) * (1 - θ/(2*Ne))`."""
    return (1.0 - 1.0 / (2.0 * ne)) * (1.0 - theta / (2.0 * ne))


def fst_connected_pair_at(ne, theta, m_tot, t):
    """`fstConnectedPairAt Ne θ mTot t`."""
    return ((1.0 / (1.0 + theta + 4.0 * ne * m_tot))
            * (1.0 - (het_decay_from_scaled(ne, theta) * (1.0 - m_tot)) ** t))


def superseded_level(ne, theta, m, t):
    """The hardcoded two-neighbour spelling `1/(1 + θ + 2·bigM)`, `bigM = 4·Ne·m`,
    carried with the same transient factor so only the LEVEL differs."""
    m_tot = 2.0 * m                       # the spelling's own implicit mTot
    return ((1.0 / (1.0 + theta + 2.0 * (4.0 * ne * m)))
            * (1.0 - (het_decay_from_scaled(ne, theta) * (1.0 - m_tot)) ** t))


def naive_per_neighbour_level(ne, theta, m, m_tot, t):
    """Migration read one neighbour at a time: `1/(1 + θ + 4·Ne·m)`."""
    return ((1.0 / (1.0 + theta + 4.0 * ne * m))
            * (1.0 - (het_decay_from_scaled(ne, theta) * (1.0 - m_tot)) ** t))


# ---------------------------------------------------------------------------
# Estimators.
# ---------------------------------------------------------------------------
def hudson_fst(g1, n1, g2, n2):
    """Hudson's F_ST, ratio of averages, from allele COUNTS. Transcribed from
    `simlib.hudson_fst`, which is the corpus's pairwise convention."""
    p1 = g1 / n1
    p2 = g2 / n2
    num = (p1 - p2) ** 2 - p1 * (1 - p1) / (n1 - 1) - p2 * (1 - p2) / (n2 - 1)
    den = p1 * (1 - p2) + p2 * (1 - p1)
    keep = den > 0
    if not keep.any():
        return float("nan")
    return float(num[keep].sum() / den[keep].sum())


def nei_gst(g1, n1, g2, n2):
    """Nei's G_ST = 1 - H_S/H_T, the heterozygosity ratio, ratio of averages."""
    p1 = g1 / n1
    p2 = g2 / n2
    pbar = (p1 + p2) / 2.0
    h_s = (2 * p1 * (1 - p1) + 2 * p2 * (1 - p2)) / 2.0
    h_t = 2 * pbar * (1 - pbar)
    keep = h_t > 0
    if not keep.any():
        return float("nan")
    return float(1.0 - h_s[keep].sum() / h_t[keep].sum())


# ---------------------------------------------------------------------------
# Demographies. Built explicitly rather than through a helper, so that `mTot`
# is a property of the matrix this file wrote and can be read back from it.
# ---------------------------------------------------------------------------
def chain_demography(m, d=CHAIN_D, t_split=T_SPLIT):
    import msprime
    dem = msprime.Demography()
    names = ["d%d" % i for i in range(d)]
    for nm in names:
        dem.add_population(name=nm, initial_size=NE)
    dem.add_population(name="anc", initial_size=NE)
    for i in range(d):
        for j in (i - 1, i + 1):
            if 0 <= j < d:
                dem.set_migration_rate(source=names[i], dest=names[j], rate=m)
    dem.add_population_split(time=t_split, derived=names, ancestral="anc")
    focal = (d // 2, d // 2 + 1)          # two adjacent INTERIOR demes
    return dem, names[focal[0]], names[focal[1]], names


def lattice_demography(m, ell=LATT_L, t_split=T_SPLIT):
    import msprime
    dem = msprime.Demography()
    names = [["d%d_%d" % (i, j) for j in range(ell)] for i in range(ell)]
    flat = [nm for row in names for nm in row]
    for nm in flat:
        dem.add_population(name=nm, initial_size=NE)
    dem.add_population(name="anc", initial_size=NE)
    for i in range(ell):
        for j in range(ell):
            for di, dj in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                ii, jj = i + di, j + dj
                if 0 <= ii < ell and 0 <= jj < ell:
                    dem.set_migration_rate(source=names[i][j],
                                           dest=names[ii][jj], rate=m)
    dem.add_population_split(time=t_split, derived=flat, ancestral="anc")
    c = ell // 2
    return dem, names[c][c], names[c][c + 1], flat   # adjacent, both interior


def realised_m_tot(dem, deme):
    """The row sum of the migration matrix the simulation was BUILT with.

    Not the nominal `k*m`. A demography helper that halves a rate, or an edge
    that was never set, shows up here rather than as a verdict about the law.
    """
    idx = {p.name: i for i, p in enumerate(dem.populations)}
    row = np.asarray(dem.migration_matrix)[idx[deme]]
    return float(row.sum())


def measure(dem, a, b, seed, reps=REPS):
    """Hudson and Nei readings between the two focal demes, per replicate."""
    import msprime
    hud, gst = [], []
    for r in range(reps):
        ts = msprime.sim_ancestry(
            samples={a: N_DIP, b: N_DIP}, demography=dem,
            sequence_length=SEQ_LEN, recombination_rate=REC_RATE,
            random_seed=seed + r)
        ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 10000 + r)
        if ts.num_sites == 0:
            continue
        gm = ts.genotype_matrix()
        sa = ts.samples(population=[p.id for p in ts.populations()
                                   if p.metadata.get("name") == a][0])
        sb = ts.samples(population=[p.id for p in ts.populations()
                                   if p.metadata.get("name") == b][0])
        c1 = gm[:, sa].sum(1).astype(float)
        c2 = gm[:, sb].sum(1).astype(float)
        hud.append(hudson_fst(c1, len(sa), c2, len(sb)))
        gst.append(nei_gst(c1, len(sa), c2, len(sb)))
    return np.asarray(hud, float), np.asarray(gst, float)


def blocked(vals):
    a = np.asarray(vals, float)
    a = a[np.isfinite(a)]
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-TRANSIENT01-LAPWING-20260811")

    theta = 4.0 * NE * MU
    print("\ntheta = 4*Ne*mu = %.2e (the runs are effectively neutral, which is "
          "the regime the body's own motivating table is in)" % theta)

    geoms = (("chain", chain_demography, 2), ("lattice", lattice_demography, 4))
    rows = []
    for gname, builder, k in geoms:
        for u in U_GRID:
            m = u / (4.0 * NE)
            dem, a, b, _ = builder(m)
            m_tot = realised_m_tot(dem, a)
            nominal = k * m
            assert abs(m_tot - nominal) < 1e-12 * max(nominal, 1e-12), (
                "%s: realised mTot %.6g != nominal %.6g" % (gname, m_tot, nominal))
            hud, gst = measure(dem, a, b, seed=int(1000 * u) + (7 if k == 2 else 11))
            hm, hs = blocked(hud)
            gm, gs = blocked(gst)
            transient = 1.0 - (het_decay_from_scaled(NE, theta)
                               * (1.0 - m_tot)) ** T_SPLIT
            rows.append(dict(geom=gname, k=k, u=u, m=m, m_tot=m_tot,
                             hud=hm, hud_sem=hs, gst=gm, gst_sem=gs,
                             body=fst_connected_pair_at(NE, theta, m_tot, T_SPLIT),
                             sup=superseded_level(NE, theta, m, T_SPLIT),
                             naive=naive_per_neighbour_level(NE, theta, m, m_tot,
                                                             T_SPLIT),
                             transient=transient))
            r = rows[-1]
            print("  %-8s k=%d u=%4.1f  mTot=%.2e (realised)  body %.5f  "
                  "superseded %.5f  naive %.5f | Hudson %.5f +/- %.5f  "
                  "Nei %.5f +/- %.5f  [transient factor %.5f]"
                  % (gname, k, u, m_tot, r["body"], r["sup"], r["naive"],
                     hm, hs, gm, gs, transient))

    # ---- HABITAT SIZE, which this body has no parameter for -----------------
    #
    # `fstConnectedPairAt` takes `Ne`, `θ`, `mTot` and `t`, and NOT the number of
    # demes. It therefore claims one number for a neighbouring pair in a habitat
    # of any size. Isolation by distance says otherwise: in a longer chain a
    # deme's neighbours are themselves more strongly correlated with it, so the
    # pairwise differentiation of an adjacent pair falls below the island-model
    # mean field, and the shortfall grows with the habitat. The main grid above
    # is run on a 9-deme chain and a 5x5 lattice, which are small, so whatever
    # miss it reports is a LOWER BOUND on the miss in a larger habitat.
    #
    # This group measures that dependence directly rather than leaving it as an
    # objection. It carries no verdict of its own -- it is one body against
    # itself at two habitat sizes, and the body predicts the same number for
    # both, so the comparison is between two measurements.
    print("\nHABITAT SIZE at u=3.0, which the body has no parameter for "
          "(it predicts the same number for every size):")
    hab = []
    for label, builder, kw, k in (
            ("chain D=9", chain_demography, dict(d=9), 2),
            ("chain D=25", chain_demography, dict(d=25), 2),
            ("lattice 5x5", lattice_demography, dict(ell=5), 4),
            ("lattice 9x9", lattice_demography, dict(ell=9), 4)):
        u = 3.0
        m = u / (4.0 * NE)
        dem, a, b, _ = builder(m, **kw)
        m_tot = realised_m_tot(dem, a)
        hud, _ = measure(dem, a, b, seed=4242, reps=60)
        hm, hs = blocked(hud)
        pred = fst_connected_pair_at(NE, theta, m_tot, T_SPLIT)
        hab.append((label, pred, hm, hs))
        print("  %-14s body %.5f   Hudson %.5f +/- %.5f   measured/body %.4f"
              % (label, pred, hm, hs, hm / pred))

    # ---- CONTROL: m = 0, where Hudson F_ST must be coalFst = t/(t + 2 Ne) ----
    dem, a, b, _ = chain_demography(0.0)
    hud0, _ = measure(dem, a, b, seed=999)
    cm, cs = blocked(hud0)
    ctrl_pred = T_SPLIT / (T_SPLIT + 2.0 * NE)
    control = dict(
        design="m=0 isolation [Hudson F_ST must be coalFst = t/(t + 2*Ne)]",
        lean=ctrl_pred, truth=cm, sem=max(cs, 1e-12))
    print("\n  CONTROL %s: predicted %.6f measured %.6f +/- %.6f"
          % (control["design"], ctrl_pred, cm, cs))

    reg = (
        "msprime structured coalescent, Ne=%d per deme, all demes derived from "
        "one ancestral population of the same size %d generations ago so the "
        "pair starts undifferentiated; %d diploids from each of TWO ADJACENT "
        "INTERIOR demes, %.0f Mb at r=%.0e and mu=%.0e, %d replicates. The "
        "chain has %d demes and the lattice %dx%d, and mTot is READ BACK as the "
        "row sum of the migration matrix the run was built with rather than "
        "assumed from the geometry. The split is far enough back that the "
        "transient factor is within 0.03%% of one in every cell, so the "
        "observable is the PLATEAU and not the approach -- the approach has its "
        "own body and its own half-life measurement. Boundary demes are outside "
        "the law's stated reach and none is sampled"
        % (NE, T_SPLIT, N_DIP, SEQ_LEN / 1e6, REC_RATE, MU, REPS, CHAIN_D,
           LATT_L, LATT_L))

    def cells(pred_key, obs_key, sem_key, geom=None):
        return [dict(design="%s k=%d u=%.1f (mTot=%.2e)"
                            % (r["geom"], r["k"], r["u"], r["m_tot"]),
                     lean=r[pred_key], truth=r[obs_key],
                     sem=max(r[sem_key], 1e-12))
                for r in rows if geom is None or r["geom"] == geom]

    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    record("fstConnectedPairAt", LEAN_FILE,
           "(1 / (1 + θ + 4*Ne*mTot)) * (1 - (hetDecayFromScaled Ne θ * "
           "(1 - mTot))^t)", cells("body", "hud", "hud_sem"), **MODEL,
           note="Hudson's estimator, the corpus's pairwise convention and the "
                "one the identity-by-descent level 1/(1+4*Ne*mTot) targets")
    for g in ("chain", "lattice"):
        record("fstConnectedPairAt [%s interiors alone]" % g, LEAN_FILE,
               "same body, restricted to the %s cells" % g,
               cells("body", "hud", "hud_sem", geom=g), **MODEL,
               note="split out because the repair is invisible on the chain, "
                    "where this body and the superseded spelling are the same "
                    "number, and is the whole claim on the lattice")
        record("fstConnectedPairAt [the SUPERSEDED hardcoded two-neighbour "
               "level 1/(1 + θ + 2*bigM), %s, competing]" % g, LEAN_FILE,
               "1 / (1 + θ + 2*(4*Ne*m))",
               cells("sup", "hud", "hud_sem", geom=g), **MODEL,
               note="MUST pass on the chain and fail on the lattice: on a "
                    "two-neighbour deme it IS this body, and a design in which "
                    "it failed on both would be measuring something other than "
                    "the geometry")
        record("fstConnectedPairAt [the NAIVE per-neighbour level "
               "1/(1 + θ + 4*Ne*m), %s, competing]" % g, LEAN_FILE,
               "1 / (1 + θ + 4*Ne*m)",
               cells("naive", "hud", "hud_sem", geom=g), **MODEL,
               note="wrong on both geometries and by different factors, so it "
                    "cannot be right by accident on either")
    record("fstConnectedPairAt [read against Nei's G_ST instead of Hudson, "
           "competing]", LEAN_FILE,
           "same body, oracle replaced by 1 - H_S/H_T on the same replicates",
           cells("body", "gst", "gst_sem"), **MODEL,
           note="carried so that a disagreement can be charged to the formula "
                "or to the F_ST convention rather than to whichever one this "
                "battery happened to pick")

    dump_results("battery_transient01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-34s %-62s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:62], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

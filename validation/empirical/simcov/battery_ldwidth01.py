"""Battery ldwidth01: the bracket's WIDTH, and how much of it is ascertainment.

WHAT THE CORPUS ASKS FOR, in as many words: the migration-LD bracket's own
docstring says a battery should "measure the WIDTH against the restoration gap,
not merely report containment".  Containment is cheap -- a bracket wide enough
contains anything.  The width is the claim.

WHY THIS IS RE-POSED AND NOT THE BATTERY ORIGINALLY SPECIFIED.  The `lambda =
Lambda` candidate this file was going to adjudicate is refuted before any
simulation of mine: an exact ARG derivation rejects it at 12.1 sems pooled, and
the ascertained cross-deme LD correlation measured directly rejects it at 144.7
sems in its own units.  So no verdict row is carried against it here, and no
body is invented from a fit.  Two things that work survive from that programme
and are what this battery is:

  * THE FLOOR WAS WRONG, and is corrected here.  The bracket's lower end charged
    recombination on both branches and NOTHING for drift.  The exact law is

        floor(c, t) = exp(-2*(c + 1/(2*Ne))*t)

    which at zero recombination is `exp(-t/Ne)` rather than one: two isolated
    demes lose LD correlation to drift alone.  At the cells below that factor is
    0.78, so the superseded floor sits a uniform 1.28x above the corrected one,
    and a design testing containment against it was testing a floor that is too
    high everywhere by a constant nobody had measured.

  * THE ASCERTAINMENT GAP IS THE OPEN QUANTITY.  The derivation that corrected
    the floor modelled `MAF > 0.05` ascertainment and NOT the clumping and
    p-thresholding a real score applies, and it quantified its own ignorance:
    for the corpus's inferred `lambda` to be an LD quantity at all, an
    ascertainment factor between 1.8x and 5.9x is needed.  That is a factor of
    three of unexplained slack, and this battery closes it by MEASURING the
    same LD correlation under all three ascertainments ON THE SAME REPLICATES:

        unascertained   every segregating pair
        MAF-only        both loci common in both demes -- the derivation's scope
        score SNPs      p-thresholded then clumped -- what a PGS actually carries

THE ISOLATION ARM IS WHERE THE ASCERTAINMENT FACTOR IS CLEAN.  With no migration
there is no restoration to confound it, so the floor is the whole prediction and
any excess over it is ascertainment or an error in the floor -- nothing else is
available.  The migration arm then measures restoration ABOVE that corrected,
ascertainment-calibrated floor, which is the width the corpus asked for.

THE ESTIMATOR IS `battery_bulk55`'s, deliberately, so the two compose.  It is
the SPLIT-HALF cross-deme correlation of signed `r`: every product is between
DISJOINT halves of a deme's samples, so no `E[noise^2]` term survives.  The
naive correlation is attenuated by the sampling noise in `r` itself, which
`battery_bulk51` detected at twelve sems on a panmictic control -- and that
attenuation is not common between arms, because the noise-to-signal ratio in `r`
depends on the LD level, which is the very thing under study.

SCOPE: the per-allele score, matching the corrected clean-split law, so the two
batteries' scopes compose.

CONTROL, exact and independent of every quantity above: a split at `t = 1`
generation is one population, where the cross-deme LD correlation must be 1.  It
fails on a mislabelled deme, a broken split-half, or a sign error in `r`, and it
is `battery_bulk55`'s own control on the same code path.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import bisect
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-LDWIDTH01-CURLEW-20260811"

LEAN_FILE = "PhenomeWidePortability.lean"

NE = 1000.0
T_DIV = 250            # exp(-t/Ne) = 0.78, so the omitted drift factor bites
MIG = 1e-3             # 4*Ne*m = 4 in the migration arm
SEQ = 20e6
REC = 1e-8
MU = 1e-8
N_DIP = 200            # per deme; split-half uses 100 against 100
N_CAUSAL = 200
H2 = 0.5
MAF = 0.05
Z_THRESH = 2.0         # p-thresholding for the score arm
# A CLUMPED SCORE HAS NO PAIR CLOSER THAN ITS WINDOW, by construction, so the
# clump width sets the shortest distance at which the score-SNP ascertainment
# can be measured at all. At 100 kb the three shortest bins were structurally
# empty and returned NaN; 25 kb is the narrowest window the restoration spec
# sweeps and it lets the ascertainments be compared over a common set of bins.
CLUMP_BP = 25e3
REPS = 30
# Map-distance bins, in bp, starting at the clump width so all three
# ascertainments are compared over the SAME bins. The corrected floor moves from
# 0.599 to 0.029 across them, a factor of 21, which is this design's power.
BINS = ((25e3, 80e3), (80e3, 3.2e5), (3.2e5, 1e6))
PAIRS_PER_BIN = 300


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except OSError:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def corrected_floor(bp, t=T_DIV, ne=NE, rec=REC):
    """`exp(-2*(c + 1/(2*Ne))*t)`: recombination on both branches AND drift.

    The `1/(2*Ne)` is the term the superseded floor omitted. At zero
    recombination it leaves `exp(-t/Ne)`, so two isolated demes lose LD
    correlation even where no recombination separates the loci.
    """
    c = rec * bp
    return math.exp(-2.0 * (c + 1.0 / (2.0 * ne)) * t)


def superseded_floor(bp, t=T_DIV, rec=REC):
    """The bracket's old lower end: recombination on both branches, no drift."""
    return (1.0 - rec * bp) ** (2 * t)


# ---------------------------------------------------------------------------
def simulate(t_div, mig, seed):
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="A", initial_size=NE)
    dem.add_population(name="B", initial_size=NE)
    dem.add_population(name="ANC", initial_size=NE)
    if mig > 0:
        dem.set_symmetric_migration_rate(["A", "B"], mig)
    dem.add_population_split(time=t_div, derived=["A", "B"], ancestral="ANC")
    ts = msprime.sim_ancestry(
        samples={"A": N_DIP, "B": N_DIP}, demography=dem, sequence_length=SEQ,
        recombination_rate=REC, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 7777)
    gm = ts.genotype_matrix()
    a = ts.samples(population=0)
    b = ts.samples(population=1)
    return gm[:, a], gm[:, b], ts.tables.sites.position


def score_snps(ga, gb, pos, rng):
    """The SNPs a per-allele PGS would actually carry: p-thresholded, then
    clumped, off a marginal GWAS in deme A."""
    fa = ga.mean(1)
    usable = np.flatnonzero(np.minimum(fa, 1 - fa) >= MAF)
    if usable.size < N_CAUSAL + 10:
        return np.array([], dtype=int)
    causal = rng.choice(usable, size=N_CAUSAL, replace=False)
    beta = rng.standard_normal(N_CAUSAL)
    # diploid dosages; per-allele effects, environment set once from deme A
    da = ga.reshape(ga.shape[0], -1, 2).sum(2).astype(np.float64)
    gv = da[causal].T @ beta
    ve = float(gv.var()) * (1 - H2) / H2
    y = gv + rng.standard_normal(da.shape[1]) * math.sqrt(ve)
    y = y - y.mean()
    dc = da - da.mean(1, keepdims=True)
    sd = dc.std(1)
    ok = np.flatnonzero(sd > 0)
    z = np.zeros(da.shape[0])
    z[ok] = np.abs((dc[ok] @ y) / (sd[ok] * math.sqrt(da.shape[1]) * y.std()))
    hit = np.flatnonzero(z > Z_THRESH)
    if hit.size == 0:
        return hit
    order = hit[np.argsort(-z[hit])]
    kept, kpos = [], []
    for i in order:
        p = pos[i]
        j = bisect.bisect_left(kpos, p - CLUMP_BP)
        if j < len(kpos) and kpos[j] <= p + CLUMP_BP:
            continue
        kept.append(i)
        bisect.insort(kpos, p)
    return np.asarray(sorted(kept), dtype=int)


def pairs_in_bin(idx, pos, lo, hi, rng, want=PAIRS_PER_BIN):
    """Pairs drawn from `idx` whose separation lies in [lo, hi)."""
    if idx.size < 2:
        return []
    p = pos[idx]
    out = []
    order = rng.permutation(idx.size)
    for k in order:
        a = p[k]
        j0 = bisect.bisect_left(p, a + lo)
        j1 = bisect.bisect_left(p, a + hi)
        if j1 > j0:
            j = int(rng.integers(j0, j1))
            out.append((idx[k], idx[j]))
            if len(out) >= want:
                break
    return out


def ld_corr(ga, gb, prs, pos=None):
    """`battery_bulk55`'s split-half cross-deme correlation of signed `r`.

    Also returns the mean corrected floor over the pairs ACTUALLY USED. The
    floor is exponential in distance and the bins are wide, so evaluating it at
    a bin's midpoint is not its average over the bin: by Jensen the average is
    the larger, by about 1.5x in the widest bin here. Charging that gap to the
    body would be a false falsification manufactured by the binning, so the
    prediction is averaged over the same pairs the measurement is.
    """
    na, nb = ga.shape[1], gb.shape[1]
    a1, a2 = ga[:, :na // 2], ga[:, na // 2:]
    b1, b2 = gb[:, :nb // 2], gb[:, nb // 2:]
    ra1, ra2, rb1, rb2, fl = [], [], [], [], []
    for i, j in prs:
        v = [np.corrcoef(h[i], h[j])[0, 1] for h in (a1, a2, b1, b2)]
        if all(np.isfinite(x) for x in v):
            ra1.append(v[0]); ra2.append(v[1]); rb1.append(v[2]); rb2.append(v[3])
            if pos is not None:
                fl.append(corrected_floor(abs(float(pos[j]) - float(pos[i])))) 
    if len(ra1) < 20:
        return float("nan"), float("nan")
    ra1, ra2 = np.asarray(ra1), np.asarray(ra2)
    rb1, rb2 = np.asarray(rb1), np.asarray(rb2)
    num = float(np.mean(ra1 * rb1))
    da, db = float(np.mean(ra1 * ra2)), float(np.mean(rb1 * rb2))
    mean_floor = float(np.mean(fl)) if fl else float("nan")
    if da <= 0 or db <= 0:
        return float("nan"), mean_floor
    c = num / math.sqrt(da * db)
    return (float(c) if np.isfinite(c) else float("nan")), mean_floor


def one_replicate(t_div, mig, seed):
    rng = np.random.default_rng(seed)
    ga, gb, pos = simulate(t_div, mig, seed)
    fa, fb = ga.mean(1), gb.mean(1)
    # "unascertained" still needs `r` to EXIST: a site monomorphic within a
    # sample half has no correlation with anything, and numpy returns NaN. The
    # minimal filter is therefore a minor count of at least two in each deme,
    # which is not an MAF threshold and is the least ascertainment under which
    # the observable is defined at all.
    ca, cb = ga.sum(1), gb.sum(1)
    defined = ((np.minimum(ca, ga.shape[1] - ca) >= 2)
               & (np.minimum(cb, gb.shape[1] - cb) >= 2))
    sets = {
        "unascertained": np.flatnonzero(defined),
        "MAF-only": np.flatnonzero(defined & (np.minimum(fa, 1 - fa) > MAF)
                                   & (np.minimum(fb, 1 - fb) > MAF)),
        "score SNPs": score_snps(ga, gb, pos, rng),
    }
    out = {}
    for name, idx in sets.items():
        out[name] = {}
        out["n_" + name] = int(idx.size)
        for lo, hi in BINS:
            prs = pairs_in_bin(idx, pos, lo, hi, rng)
            c, f = (ld_corr(ga, gb, prs, pos) if prs
                    else (float("nan"), float("nan")))
            out[name][(lo, hi)] = c
            out.setdefault("floor", {})[(name, lo, hi)] = f
    return out


def blocked(v):
    a = np.asarray([x for x in v if np.isfinite(x)], float)
    if a.size < 2:
        return float("nan"), float("nan"), a.size
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size)), a.size


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-LDWIDTH01-CURLEW-20260811")

    print("\nthe corrected floor against the one it replaces "
          "(t=%d, Ne=%d, so the drift factor exp(-t/Ne) = %.4f):"
          % (T_DIV, NE, math.exp(-T_DIV / NE)))
    for lo, hi in BINS:
        mid = 0.5 * (lo + hi)
        print("  %7.0f-%-8.0f bp  corrected %.4f   superseded %.4f  "
              "(superseded high by %.2fx)"
              % (lo, hi, corrected_floor(mid), superseded_floor(mid),
                 superseded_floor(mid) / corrected_floor(mid)))

    arms = {}
    for arm, mig in (("isolation (m=0)", 0.0), ("migration (4Nem=%.0f)"
                                                % (4 * NE * MIG), MIG)):
        reps = [one_replicate(T_DIV, mig, 61000 + 97 * i) for i in range(REPS)]
        arms[arm] = reps
        print("\n%s: SNPs per set %s" % (arm, ", ".join(
            "%s %.0f" % (k, blocked([r["n_" + k] for r in reps])[0])
            for k in ("unascertained", "MAF-only", "score SNPs"))))
        print("  %-16s %10s %10s %10s %10s"
              % ("bin (bp)", "floor", "unasc.", "MAF-only", "score"))
        for lo, hi in BINS:
            f, _, _ = blocked([r["floor"][("MAF-only", lo, hi)] for r in reps])
            vals = []
            for k in ("unascertained", "MAF-only", "score SNPs"):
                m, s, _ = blocked([r[k][(lo, hi)] for r in reps])
                vals.append((m, s))
            print("  %7.0f-%-8.0f %10.4f %10.4f %10.4f %10.4f"
                  % (lo, hi, f, vals[0][0], vals[1][0], vals[2][0]))

    # ---- CONTROL: t = 1 is one population, correlation must be 1 ----------
    ctl = [one_replicate(1, 0.0, 62000 + 13 * i) for i in range(8)]
    cm, cs, _ = blocked([r["MAF-only"][BINS[1]] for r in ctl])
    control = dict(design="split at t=1 [one population: the cross-deme LD "
                          "correlation is 1]",
                   lean=1.0, truth=cm, sem=max(cs, 1e-12))
    print("\n  CONTROL %s: predicted 1.000000 measured %.6f +/- %.6f"
          % (control["design"], cm, cs))

    reg = (
        "msprime, two demes of Ne=%d split %d generations ago, %.0f Mb at "
        "r=%.0e and mu=%.0e, %d diploids per deme, %d independent replicates. "
        "The observable is battery_bulk55's SPLIT-HALF cross-deme correlation of "
        "signed r, every product taken between DISJOINT halves of a deme so no "
        "E[noise^2] term survives the attenuation battery_bulk51 detected at "
        "twelve sems. Pairs are binned by map distance, which is where the "
        "design gets its span: the corrected floor runs 0.665 to 0.052 across "
        "the bins. Three ascertainments are measured ON THE SAME REPLICATES -- "
        "every segregating pair, both loci common in both demes, and the "
        "p-thresholded-then-clumped SNPs a per-allele PGS actually carries -- "
        "because the derivation that corrected the floor modelled the second "
        "and not the third, and quantified that gap as a factor between 1.8x "
        "and 5.9x" % (NE, T_DIV, SEQ / 1e6, REC, MU, N_DIP, REPS))
    MODEL = dict(regime=reg, control=control, realised_inputs=True,
                 argument_source="model")

    # The isolation arm is where the floor is the WHOLE prediction.
    iso = arms["isolation (m=0)"]
    for setname in ("unascertained", "MAF-only", "score SNPs"):
        cells = []
        for lo, hi in BINS:
            m, s, _ = blocked([r[setname][(lo, hi)] for r in iso])
            fm, _, _ = blocked([r["floor"][(setname, lo, hi)] for r in iso])
            cells.append(dict(design="isolation, %.0f-%.0f bp, %s"
                                     % (lo, hi, setname),
                              lean=fm, truth=m, sem=max(s, 1e-12)))
        record("migrationLDBracket [CORRECTED FLOOR exp(-2(c+1/(2Ne))t) under "
               "isolation, %s]" % setname, LEAN_FILE,
               "exp(-2*(c + 1/(2*Ne))*t)", cells, **MODEL,
               note="with no migration there is no restoration, so the floor is "
                    "the whole prediction and any excess is ascertainment or an "
                    "error in the floor")
    cells = []
    for lo, hi in BINS:
        m, s, _ = blocked([r["MAF-only"][(lo, hi)] for r in iso])
        # the superseded floor is the corrected one without the drift term, so
        # it is the SAME pair-averaged quantity multiplied by exp(+t/Ne)
        fm, _, _ = blocked([r["floor"][("MAF-only", lo, hi)] for r in iso])
        cells.append(dict(design="isolation, %.0f-%.0f bp, MAF-only" % (lo, hi),
                          lean=fm * math.exp(T_DIV / NE), truth=m,
                          sem=max(s, 1e-12)))
    record("migrationLDBracket [the SUPERSEDED floor (1-c)^(2t), no drift term, "
           "competing]", LEAN_FILE, "(1 - c)^(2*t)", cells, **MODEL,
           note="carried so the size of the omitted drift factor is on the "
                "record rather than argued")

    dump_results("battery_ldwidth01_results.json",
                 battery_source=os.path.abspath(__file__))
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-30s %-58s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:58], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

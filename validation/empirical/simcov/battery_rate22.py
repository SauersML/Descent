"""#22: is `lambda * sqrt(fstGap) * distance` really `4 * Ne * c * distance`?

Task #11 settled the SHAPE of the LD-correlation decay and said so explicitly: it
did NOT settle the rate. The discrimination there came entirely from pinning
`rho = 4*Ne*x`, and with a free rate the two candidate shapes are
indistinguishable in chi^2 (3.44e-4 against 3.68e-4). So the rate carries the
discriminating information, and installing the Ohta-Kimura shape does not license
the way the rate is written.

Both bodies write it the same way --

    ldCorrelationDecay distance fstGap lambda
      = exp (-(lambda * sqrt fstGap * distance))
    ldCorrelationDecayHyperbolic distance fstGap lambda
      = ohtaKimuraSigmaDSq (1/4) (lambda * sqrt fstGap * distance) / ... 0

-- so `lambda * sqrt fstGap` stands in for a rate that #11 pinned, in a PANMICTIC
population, at `4*Ne*c`. THAT IDENTIFICATION IS WHAT THIS BATTERY TESTS, and it
is common to both bodies, so no repair that swaps one shape for the other touches
it.

THE DESIGN DECOUPLES Ne FROM F_ST, and that is the whole point. In an island
model F_ST is about 1/(1+4*Ne*m), so the obvious sweep -- vary Ne, hold m -- moves
BOTH and leaves the two readings confounded, which is how a rate parameterisation
survives untested. Six cells cross Ne over {1000, 2000, 4000} with two migration
levels each, so the realised F_ST lands in two tight clusters (about 0.025 and
about 0.10) at every Ne. The recombination map is identical in every cell.

THE READOUT IS THE FITTED RATE, NOT chi^2. A chi^2 column here would measure
nothing and would look like it measured something, for the reason #11 recorded.
Each cell's oracle is the rate that makes the Ohta-Kimura shape fit that cell's
measured curve; the prediction is `4*Ne*c`, with ZERO fitted constants. The rival
reading `lambda*sqrt(fstGap)` cannot be tested at zero constants because `lambda`
is free and the corpus pins no value for it, so it is recorded as a competitor
with ONE constant fitted globally across all six cells -- which is the most
favourable honest form of it, and it still has to explain the spread.

THE AMPLITUDE IS FITTED, and that is deliberate. Both bodies normalise to 1 at
zero distance. The measurement does not: cross-deme Corr(D) at zero recombination
distance is not 1, because D is inherited from the ancestor and then drifts
independently in the two demes. Pinning the amplitude at 1 therefore forces the
rate to absorb a real amplitude deficit, and since that deficit tracks F_ST it
would MANUFACTURE an F_ST dependence in the rate. Fitting the amplitude is not
#11's degenerate free-amplitude-and-free-rate fit: there the two SHAPES were
being discriminated and the extra freedom let each imitate the other; here the
shape is held fixed and only the rate is in question, so amplitude and rate are
separately identified. The fitted amplitudes are recorded as their own row,
because "the value at zero distance is 1" is itself a claim both bodies make.

Corr(D) IS SPLIT-HALF over disjoint haplotype halves within each deme. The naive
cross-deme correlation of LD is attenuated by the sampling noise in LD itself,
and that attenuation depends on the LD level, which is exactly what distance
changes -- so the naive version carries a DISTANCE-DEPENDENT bias, which lands
straight in the fitted rate, which is the only thing this battery measures.

F_ST is the REALISED Hudson value on the same MAF-filtered sites the curve is
measured on, never the nominal `1/(1+4*Ne*m)`. A pilot showed the nominal is
badly wrong for two demes -- two cells both nominally 0.05 realised 0.0397 and
0.0233 -- so every reading here uses where the cells actually landed.

THE CONTROL IS A PANMICTIC CELL, and it is a control that can fail for reasons
that are not the formula. A single unstructured population at known `Ne`, run
through the IDENTICAL binning, LD estimator and rate-fitting code, must return a
within-population `sigma_d^2` decay rate of `4*Ne*c`: that is not this battery's
claim, it is #11's already-measured result (0.92-1.06 against a true 1) and
`battery_sved01`'s independent one on a forward two-locus engine. If the engine's
recombination map, effective size, LD estimator, binning or fitting code were
wrong, this cell moves -- and it says nothing whatever about how the CROSS-DEME
rate should be written. A control built from the cross-deme quantities themselves
could only have confirmed that the fit fits.
"""
import math
import os
import sys

import numpy as np

from battery_core import dump_results, record, run_groups

FRESH_TOKEN = "SIMCOV-BATTERY-RATE22-IDENT-20260811"
LEAN_FILE = "PresentDayMetrics.lean"

SEQ = 4e6
REC = 1e-8
MU = 1e-8
NHAP = 300                 # per deme
MAF = 0.05
MAXPAIRS = 60000
REPS = 8
NE_CTRL = 2000.0           # the panmictic control cell

QUICK = "--quick" in sys.argv
if QUICK:
    REPS, SEQ = 2, 1e6

CELLS = [("A", 1000.0, 0.05), ("B", 1000.0, 0.20),
         ("C", 2000.0, 0.05), ("D", 2000.0, 0.20),
         ("E", 4000.0, 0.05), ("F", 4000.0, 0.20)]

BINS = np.exp(np.linspace(math.log(2e3), math.log(1.5e6), 13))
XMID = np.sqrt(BINS[1:] * BINS[:-1])
RGRID = np.exp(np.linspace(math.log(1e-9), math.log(1e-2), 6000))


def freshness():
    return FRESH_TOKEN


def mig_for(ne, fst):
    return (1.0 / fst - 1.0) / (4.0 * ne)


def ok_norm(rho):
    """Ohta-Kimura sigma_d^2, already 1 at rho = 0.

    22*(10+rho)/(10*(2+rho)*(11+rho)): numerator 220 and denominator 220 at
    rho = 0, so no normalising factor is applied. Writing one would be a silent
    second free amplitude.
    """
    return 22.0 * (10.0 + rho) / (10.0 * (2.0 + rho) * (11.0 + rho))


def exp_shape(rho):
    """`ldCorrelationDecay`'s exponential, for the rate read under ITS shape."""
    return np.exp(-rho)


def simulate_pair(ne, m, seed):
    import msprime
    dem = msprime.Demography()
    dem.add_population(name="p0", initial_size=ne)
    dem.add_population(name="p1", initial_size=ne)
    dem.set_migration_rate(source="p0", dest="p1", rate=m)
    dem.set_migration_rate(source="p1", dest="p0", rate=m)
    ts = msprime.sim_ancestry(
        samples={"p0": NHAP // 2, "p1": NHAP // 2}, demography=dem,
        sequence_length=SEQ, recombination_rate=REC, ploidy=2,
        random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 7)
    gm = ts.genotype_matrix()
    ids = {p.metadata.get("name"): p.id for p in ts.populations()}
    return (gm[:, ts.samples(population=ids["p0"])],
            gm[:, ts.samples(population=ids["p1"])],
            np.asarray(ts.tables.sites.position))


def simulate_panmictic(ne, seed):
    import msprime
    ts = msprime.sim_ancestry(
        samples=NHAP, population_size=ne, sequence_length=SEQ,
        recombination_rate=REC, ploidy=2, random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=MU, random_seed=seed + 7)
    return ts.genotype_matrix(), np.asarray(ts.tables.sites.position)


def maf_sites(*hs):
    ok = None
    for h in hs:
        p = h.mean(1)
        m = np.minimum(p, 1 - p) >= MAF
        ok = m if ok is None else (ok & m)
    return np.flatnonzero(ok)


def hudson_fst(h0, h1, sites):
    p0, p1 = h0.mean(1)[sites], h1.mean(1)[sites]
    n0, n1 = h0.shape[1], h1.shape[1]
    num = (p0 - p1) ** 2 - p0 * (1 - p0) / (n0 - 1) - p1 * (1 - p1) / (n1 - 1)
    den = p0 * (1 - p1) + p1 * (1 - p0)
    ok = den > 0
    return float(np.sum(num[ok]) / np.sum(den[ok]))


def bin_pairs(hp, rng):
    """Site-index pairs per distance bin, sampled from the kept site list."""
    out = []
    for k in range(len(BINS) - 1):
        li = rng.integers(0, hp.size, size=MAXPAIRS)
        lo_i = np.searchsorted(hp, hp[li] + BINS[k], side="left")
        hi_i = np.searchsorted(hp, hp[li] + BINS[k + 1], side="right")
        width = hi_i - lo_i
        good = width > 0
        if good.sum() < 30:
            out.append(None)
            continue
        li = li[good]
        ri = np.minimum(lo_i[good] + (rng.random(good.sum())
                                      * width[good]).astype(int), hp.size - 1)
        ok = ri != li
        out.append((li[ok], ri[ok]) if ok.sum() >= 30 else None)
    return out


def d_vec(h, ii, jj):
    a = h[ii].astype(np.float64)
    b = h[jj].astype(np.float64)
    return (a * b).mean(1) - a.mean(1) * b.mean(1)


def corr_d_curve(h0, h1, pos, rng):
    """Split-half cross-deme Corr(D) per distance bin."""
    sel = maf_sites(h0, h1)
    if sel.size < 50:
        return None, None
    hp = pos[sel]
    n0, n1 = h0.shape[1], h1.shape[1]
    s0a, s0b = h0[sel][:, :n0 // 2], h0[sel][:, n0 // 2:]
    s1a, s1b = h1[sel][:, :n1 // 2], h1[sel][:, n1 // 2:]
    y = []
    for pr in bin_pairs(hp, rng):
        if pr is None:
            y.append(float("nan"))
            continue
        li, ri = pr
        a1, a2 = d_vec(s0a, li, ri), d_vec(s0b, li, ri)
        b1, b2 = d_vec(s1a, li, ri), d_vec(s1b, li, ri)
        da, db = float(np.mean(a1 * a2)), float(np.mean(b1 * b2))
        y.append(float(np.mean(a1 * b1)) / math.sqrt(da * db)
                 if da > 0 and db > 0 else float("nan"))
    return np.asarray(y, float), sel


def sigma_d_curve(h, pos, rng):
    """Within-population sigma_d^2 per bin: a RATIO OF MEANS, not a mean ratio.

    E[r^2] has no equilibrium to measure in this regime -- the corpus records
    that -- while sigma_d^2 = E[D^2]/E[p(1-p)q(1-q)] is dominated by the still
    segregating pairs and is the scale the theory is stated in.
    """
    sel = maf_sites(h)
    if sel.size < 50:
        return None
    hp = pos[sel]
    g = h[sel]
    p = g.mean(1)
    y = []
    for pr in bin_pairs(hp, rng):
        if pr is None:
            y.append(float("nan"))
            continue
        li, ri = pr
        d = d_vec(g, li, ri)
        den = p[li] * (1 - p[li]) * p[ri] * (1 - p[ri])
        y.append(float(np.mean(d ** 2) / np.mean(den))
                 if np.mean(den) > 0 else float("nan"))
    return np.asarray(y, float)


def fit_rate(x, y, shape=ok_norm):
    """Rate and amplitude for y = A * shape(rate * x); A in closed form.

    The amplitude is a nuisance parameter here, not a second hypothesis: both
    bodies assert A = 1, the measurement rejects that, and pinning it would push
    the rejection into the rate -- which is the quantity under test.
    """
    ok = np.isfinite(y)
    if ok.sum() < 4:
        return float("nan"), float("nan")
    xx, yy = x[ok], y[ok]
    best = (float("inf"), float("nan"), float("nan"))
    for r in RGRID:
        f = shape(r * xx)
        ff = float(np.dot(f, f))
        if ff <= 0:
            continue
        a = float(np.dot(f, yy) / ff)
        res = float(np.sum((yy - a * f) ** 2))
        if res < best[0]:
            best = (res, r, a)
    return best[1], best[2]


# ---------------------------------------------------------------------------
STATE = {}


def gather():
    if STATE:
        return STATE
    cells = {}
    for lab, ne, fst_t in CELLS:
        m = mig_for(ne, fst_t)
        rates, amps, fsts, erates = [], [], [], []
        for r in range(REPS):
            h0, h1, pos = simulate_pair(
                ne, m, 1000 + 97 * r + int(ne) + int(fst_t * 1000))
            rng = np.random.default_rng(50000 + r)
            y, sel = corr_d_curve(h0, h1, pos, rng)
            if y is None:
                continue
            rr, aa = fit_rate(XMID, y)
            er, _ = fit_rate(XMID, y, shape=exp_shape)
            rates.append(rr)
            amps.append(aa)
            erates.append(er)
            fsts.append(hudson_fst(h0, h1, sel))
            print("    %s rep %d/%d F_ST=%.4f rate=%.3e amp=%.3f"
                  % (lab, r + 1, REPS, fsts[-1], rr, aa), flush=True)
        if rates:
            cells[lab] = dict(ne=ne, m=m, rates=rates, amps=amps,
                              erates=erates, fsts=fsts)
    ctrl = []
    for r in range(REPS):
        g, pos = simulate_panmictic(NE_CTRL, 900000 + 131 * r)
        rng = np.random.default_rng(77000 + r)
        y = sigma_d_curve(g, pos, rng)
        if y is None:
            continue
        rr, _ = fit_rate(XMID, y)
        ctrl.append(rr)
        print("    CTRL panmictic rep %d/%d rate=%.3e (4*Ne*c = %.3e)"
              % (r + 1, REPS, rr, 4 * NE_CTRL * REC), flush=True)
    STATE["cells"] = cells
    STATE["ctrl"] = ctrl
    return STATE


def ms(v):
    a = np.asarray([x for x in v if np.isfinite(x)], float)
    if a.size < 2:
        return (float(a[0]) if a.size else float("nan")), float("nan")
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def engine_control():
    """The panmictic cell: fitted within-population rate against 4*Ne*c."""
    st = gather()
    m, s = ms(st["ctrl"])
    return dict(design="PANMICTIC Ne=%d, within-population sigma_d^2 decay rate "
                       "through the identical estimator and fit" % NE_CTRL,
                lean=4.0 * NE_CTRL * REC, truth=m, sem=max(s, 1e-12))


REGIME = None


def regime():
    return ("two-deme island model at migration-drift equilibrium, %0.0f Mb, "
            "recombination and mutation both 1e-8 and IDENTICAL in every cell, "
            "%d haplotypes per deme, %d replicates. Six cells cross Ne over "
            "{1000,2000,4000} with two migration levels, so realised F_ST forms "
            "two clusters at every Ne and Ne is not confounded with F_ST. The "
            "oracle is the rate that makes the Ohta-Kimura shape fit that "
            "cell's measured cross-deme Corr(D) curve, with the amplitude "
            "fitted because both bodies assert an amplitude of 1 that the "
            "measurement rejects. Corr(D) is split-half over disjoint haplotype "
            "halves in each deme, so its attenuation is not distance-dependent. "
            "F_ST is the realised Hudson value on the MAF-filtered sites the "
            "curve is measured on, never the nominal 1/(1+4Nm), which a pilot "
            "showed is badly wrong for two demes"
            % (SEQ / 1e6, NHAP, REPS))


def group_rate():
    print("\n== GROUP: the rate identification")
    st = gather()
    labs = [l for l, _, _ in CELLS if l in st["cells"]]
    if not labs:
        raise RuntimeError("no usable cells")
    ctrl = engine_control()

    ok_cells, ex_cells = [], []
    fst_mean, rate_mean = {}, {}
    for l in labs:
        c = st["cells"][l]
        f, _ = ms(c["fsts"])
        r, rs = ms(c["rates"])
        e, es = ms(c["erates"])
        fst_mean[l], rate_mean[l] = f, r
        lab = "Ne=%d F_ST=%.4f" % (c["ne"], f)
        ok_cells.append(dict(design=lab, lean=4.0 * c["ne"] * REC, truth=r,
                             sem=max(rs, 1e-12)))
        ex_cells.append(dict(design=lab, lean=4.0 * c["ne"] * REC, truth=e,
                             sem=max(es, 1e-12)))
        print("    %-4s %s  fitted rate %.4e  4*Ne*c %.4e  ratio %.3f"
              % (l, lab, r, 4.0 * c["ne"] * REC, r / (4.0 * c["ne"] * REC)))

    record("ldCorrelationDecayHyperbolic", LEAN_FILE,
           "the rate slot lambda*sqrt(fstGap) IDENTIFIED as 4*Ne*c, zero "
           "fitted constants",
           ok_cells, regime=regime(), control=ctrl,
           realised_inputs=True, argument_source="model",
           note="the oracle is the freely fitted rate of the body's own shape; "
                "the prediction is the identification under test")
    record("ldCorrelationDecay", LEAN_FILE,
           "the rate slot lambda*sqrt(fstGap) IDENTIFIED as 4*Ne*c, read under "
           "the EXPONENTIAL shape this body carries",
           ex_cells, regime=regime(), control=ctrl,
           realised_inputs=True, argument_source="model",
           note="the shape is separately falsified by task #11 at 12.05 sems; "
                "this row is about the RATE slot, which both bodies share")

    # The rival reading, given its single constant. lambda is fitted GLOBALLY:
    # one constant for six cells, the most favourable honest form, since the
    # corpus pins no value for it and a per-cell lambda would be six constants
    # for six cells and could not fail.
    lam = float(np.mean([rate_mean[l] / math.sqrt(fst_mean[l]) for l in labs]))
    lam_cells = []
    for l in labs:
        c = st["cells"][l]
        r, rs = ms(c["rates"])
        lam_cells.append(dict(
            design="Ne=%d F_ST=%.4f" % (c["ne"], fst_mean[l]),
            lean=lam * math.sqrt(fst_mean[l]), truth=r, sem=max(rs, 1e-12)))
    record("ldCorrelationDecayHyperbolic [the rate read as lambda*sqrt(fstGap) "
           "with ONE global lambda fitted across all six cells, competing]",
           LEAN_FILE, "lambda * sqrt(fstGap), lambda fitted once globally",
           lam_cells, regime=regime(), control=ctrl,
           realised_inputs=True, argument_source="sample", selected_from=1,
           note="lambda = %.4e per unit sqrt(F_ST) per bp. It cannot be tested "
                "at zero constants because the corpus pins no lambda; one "
                "global constant is the most favourable honest form" % lam)

    # The amplitude, which both bodies assert is 1.
    amp_cells = []
    for l in labs:
        c = st["cells"][l]
        a, as_ = ms(c["amps"])
        amp_cells.append(dict(
            design="Ne=%d F_ST=%.4f" % (c["ne"], fst_mean[l]),
            lean=1.0, truth=a, sem=max(as_, 1e-12)))
    record("ldCorrelationDecayHyperbolic [the amplitude at zero distance, which "
           "both bodies fix at 1, competing]", LEAN_FILE,
           "the normalisation asserts Corr(D) -> 1 as distance -> 0",
           amp_cells, regime=regime(), control=ctrl,
           realised_inputs=True, argument_source="model",
           note="at zero recombination distance D is inherited from the "
                "ancestor and then drifts independently in the two demes, so "
                "there is no reason for the cross-deme correlation to be 1")

    # THE IDENTIFICATION, as a regression on the realised values. Printed rather
    # than recorded: a fitted exponent pair describes how the two readings fail
    # and is not a candidate body.
    X = np.column_stack([np.ones(len(labs)),
                         np.log([st["cells"][l]["ne"] for l in labs]),
                         np.log([fst_mean[l] for l in labs])])
    yv = np.log([rate_mean[l] for l in labs])
    coef, *_ = np.linalg.lstsq(X, yv, rcond=None)
    print("\n  regression log(rate) = k + a*log(Ne) + b*log(F_ST):")
    print("    a = %+.3f  [4*Ne*c predicts +1.000, lambda*sqrt(fstGap) 0.000]"
          % coef[1])
    print("    b = %+.3f  [4*Ne*c predicts  0.000, lambda*sqrt(fstGap) +0.500]"
          % coef[2])
    for nm, a, b in (("4*Ne*c", 1.0, 0.0), ("lambda*sqrt(fstGap)", 0.0, 0.5)):
        r = yv - (np.log([st["cells"][l]["ne"] for l in labs]) * a
                  + np.log([fst_mean[l] for l in labs]) * b)
        print("    holding %-20s fixed: implied constant spans %.2fx"
              % (nm, float(np.exp(r.max() - r.min()))))
    print("\n  NOT A PROPOSAL. A fitted exponent pair describes how both "
          "readings fail; it never becomes a body.")


def main():
    print(freshness())
    failed = run_groups(group_rate)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_rate22_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()

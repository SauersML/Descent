"""#14: the CORRECTED clean-split law, with its source-branch factor predicted.

`battery_clean01` measured the corrected composition at ONE `(NeS, NeT)` pair and
on ONE spectrum, and `cleanSplitTargetR2'`'s own docstring records the two things
that left open:

    NO `record()` NAMES THIS BODY YET ... the independence from `NeT` is untested
    because the committed design carries a single `(NeS, NeT)` pair.

This battery closes both. The body under test is

    cleanSplitTargetR2' r2_0 w p NeS NeT t ldFactor
      = neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor NeT t))
        * sourcePolymorphicSignalFraction w p NeS t * ldFactor

with THREE PREDICTED FACTORS AND ZERO FITTED CONSTANTS. Every argument is a
simulation parameter or a realised draw; nothing is estimated from the blocks the
oracle is measured on.

SCOPE, and it is narrower than the name: the PER-ALLELE score only. The
source-standardised score is a different observable with a `sqrt(h_S/h_T)` weight,
it is measured in `battery_clean01`, and it needs a derivation of its own. It is
not recorded here, because recording a body against an observable it was not
derived for is how a shape claim gets a verdict it did not earn.

WHAT EACH GROUP IS FOR.

  A. `sourcePolymorphicSignalFraction` as a FIRST-CLASS recorded quantity with a
     sem, rather than a column inside somebody else's table. Its prediction is
     Kimura's diffusion solution for still being segregating, weighted by the
     body's own weights; its oracle is the realised fraction of the target's
     signal sitting on source-polymorphic variants.

  B. THE NeT SWEEP -- the sharpest untested consequence, and the one that makes
     the correction a change of SHAPE rather than of constant. The superseded
     summed-index body made the two branches enter symmetrically; here the
     source-branch factor does not know `NeT` exists. `Phi` is measured at four
     `NeT` at fixed `(NeS, t)` against a single prediction. Note what makes this
     falsifiable rather than definitional: the MEASURED Phi weights by the
     TARGET's realised heterozygosity, which does drift with `NeT`. That the
     ratio nevertheless does not move is a claim about the engine, not about the
     formula's argument list.

  C. THE RIVALS, ON TWO SPECTRA. The summed-index body passed `battery_clean01`'s
     `t = 100` cell, and that pass was a coincidence of the spectrum: it charges
     `(1-r2_0)*F_S` for the source branch where the truth charges `1 - Phi`, and
     on a 1/p spectrum over [0.01,0.99] at `r2_0 = 0.5` those are 0.0124 and
     0.0116. On [0.05,0.95] at the IDENTICAL `F_S` they are 0.0124 and 0.00045, a
     factor of 27 apart, because a spectrum with no rare variants has almost
     nothing to fix. SPECTRUM VARIATION IS THEREFORE MANDATORY and not a
     robustness check: on one spectrum the design cannot tell the two bodies
     apart at the shallowest cell, and a battery run on that spectrum alone would
     report a rival it was never able to see.

SEMS ARE MEASUREMENT-ONLY, not paired. The paired sem subtracts the
block-to-block scatter the two sides share, and it is the right bar when the
prediction tracks each block's realised draw. It is also the smaller bar, and
these predictions are deterministic given the block, so the conservative reading
is the measurement's own scatter. Both are computed and both are printed; the
recorded cells carry the measurement-only sem, so every verdict here is at or
above the discrepancy a paired bar would report. Where that costs a rival its
falsification, the run says so rather than quietly switching bars.

INPUTS ARE REALISED. Each block's prediction is evaluated at that block's own
realised per-branch heterozygosity loss and its own realised ancestral
frequencies, never at the nominal parameter -- the gap between the two is
O(1/sqrt(M)) and is the size of a spurious finding.

NOT MEASURED HERE, AND NOT PRETENDED: the clump-window sweep for `ldFactor` and
the fstGap cell. This engine is a forward Wright-Fisher on ALLELE FREQUENCIES and
carries no linkage whatever, so `ldFactor = 1` by construction and a window sweep
would be measuring synthetic tagging noise rather than LD. Those two cells need a
coalescent engine with a recombination map and belong in a separate battery.
"""
import math
import os
import sys

import numpy as np

from battery_core import dump_results, record, run_groups

FRESH_TOKEN = "SIMCOV-BATTERY-CLEAN02-NETSWEEP-20260811"
LEAN_FILE = "PhenomeWidePortability.lean"

R2_0 = 0.5
NE_S = 2000.0
NE_T_GRID = (250.0, 500.0, 1000.0, 2000.0)
NE_T_REF = 500.0
T_GRID = (100, 250, 500, 800, 1100)
T_NET = 500                    # the NeT sweep is at one depth, four target sizes
M_LOCI = 10000
N_IND = 40000
BLOCKS = 10
CHUNK = 500
NE_S_OFF = 200000.0            # "no source drift" -- control B's source branch

QUICK = "--quick" in sys.argv
if QUICK:
    M_LOCI, N_IND, BLOCKS = 2000, 4000, 3

# The two spectra. Both are density proportional to 1/p; they differ ONLY in
# where they are truncated, which is what isolates the rare-variant tail as the
# thing the summed-index body gets wrong.
SPECTRA = {"1/p on [0.01,0.99]": (0.01, 0.99),
           "1/p on [0.05,0.95]": (0.05, 0.95)}


def freshness():
    return FRESH_TOKEN


# ---------------------------------------------------------------------------
# The Lean bodies, transcribed.
# ---------------------------------------------------------------------------
def neutral_drift_factor(ne, t):
    return (1.0 - 1.0 / (2.0 * ne)) ** t


def fst_from_drift_factor(d):
    return 1.0 - d


def neutral_portability(r2_0, fst):
    return r2_0 * (1.0 - fst) / ((1.0 - fst) * r2_0 + (1.0 - r2_0))


def gegenbauer_32(kmax, z):
    """C_k^{3/2}(z) for k = 0..kmax by the standard three-term recurrence."""
    c = np.empty((kmax + 1, z.size))
    c[0] = 1.0
    if kmax >= 1:
        c[1] = 3.0 * z
    for k in range(1, kmax):
        c[k + 1] = (2.0 * (k + 1.5) * z * c[k] - (k + 2.0) * c[k - 1]) / (k + 1.0)
    return c


def still_segregating_prob(ne, p, t, n_terms=400):
    """`stillSegregatingProb` -- Kimura's diffusion solution.

    Sum over ODD n of a_n p(1-p) C_{n-1}^{3/2}(1-2p) exp(-lambda_n t), with
    a_n = 4(2n+1)/(n(n+1)) and lambda_n = n(n+1)/(4 Ne), from expanding the
    constant function 1 in the eigenbasis under the weight 1/(p(1-p)).
    """
    if t == 0:
        return np.ones_like(p)
    z = 1.0 - 2.0 * p
    c = gegenbauer_32(n_terms, z)
    tot = np.zeros_like(p)
    for n in range(1, n_terms + 1, 2):
        lam = n * (n + 1.0) / (4.0 * ne)
        e = math.exp(-lam * t)
        if e < 1e-18:
            break
        tot += (4.0 * (2 * n + 1) / (n * (n + 1.0))) * c[n - 1] * e
    return p * (1.0 - p) * tot


def source_polymorphic_signal_fraction(w, p, ne_s, t):
    """`sourcePolymorphicSignalFraction w p NeS t`, the body verbatim."""
    return float(np.sum(w * still_segregating_prob(ne_s, p, t)) / np.sum(w))


RIVAL_PHI = (
    ("unweighted still-segregating fraction, competing",
     "mean_j stillSegregatingProb NeS (p j) t"),
    ("1 - F_S, the heterozygosity-retention reading, competing",
     "(1 - 1/(2 NeS))^t"),
    ("the diffusion at the weighted mean frequency, competing",
     "stillSegregatingProb NeS (sum_j w_j p_j / sum_j w_j) t"),
    ("leading eigenfunction only, competing",
     "sum_j w_j * 6 p_j (1-p_j) exp(-t/(2 NeS)) / sum_j w_j"),
)


def source_polymorphic_rivals(w, p, ne_s, t):
    """The four competing readings of `sourcePolymorphicSignalFraction`.

    The body's own docstring names the first two as what it OWES: "the UNWEIGHTED
    still-segregating fraction, which tests whether the `w` weighting earns its
    place, and `1 - F_S`, the heterozygosity-retention proxy a reader would
    otherwise assume. Until one of those is run and rejected, this body is
    measured and not validated." They are run here, on the cells the body was
    already measured on.

    The other two separate the remaining structural choices the transcription
    makes. The THIRD collapses the spectrum: it evaluates the same diffusion
    solution at one frequency, the weighted mean, instead of averaging the
    solution over the spectrum -- a Jensen rival, and the one that says whether
    the ancestral frequency distribution has to be carried at all. The FOURTH
    keeps the whole spectrum and truncates the SERIES, retaining Kimura's leading
    eigenfunction alone; it is what a reader who knows the large-`t` asymptotic
    would write, and it says at what depth the 400-term sum stops mattering.

    THE FOURTH RIVAL'S REJECTION IS PARTLY FORCED and is labelled so rather than
    counted. `6 p (1-p) exp(-t/(2 NeS))` exceeds one at shallow `t` on a spectrum
    with no rare variants, which `sourcePolymorphicSignalFraction_mem_Icc` forbids
    a priori, so its failure there is arithmetic and not measurement. What the row
    measures is the DEPTH at which the approximation becomes adequate. The first
    three are genuine alternative readings, false in no cell a priori, and they
    are what makes the corpus row's agreement informative.
    """
    tot = float(np.sum(w))
    seg = still_segregating_prob(ne_s, p, t)
    pbar = float(np.sum(w * p) / tot)
    lead = p * (1.0 - p) * 6.0 * math.exp(-t / (2.0 * ne_s))
    return (float(np.mean(seg)),
            float(neutral_drift_factor(ne_s, t)),
            float(still_segregating_prob(ne_s, np.array([pbar]), t)[0]),
            float(np.sum(w * lead) / tot))


def clean_split_target_r2_prime(r2_0, fst_t, phi, ld):
    """`cleanSplitTargetR2'` -- the body under test."""
    return neutral_portability(r2_0, fst_t) * phi * ld


def summed_index_r2(r2_0, fst_s, fst_t, ld):
    """The SUPERSEDED body: both branches in the chart's fst slot, no Phi."""
    return neutral_portability(r2_0, fst_s + fst_t) * ld


def target_branch_only_r2(r2_0, fst_t, ld):
    """The chart alone, i.e. the corrected body with Phi forced to 1."""
    return neutral_portability(r2_0, fst_t) * ld


# ---------------------------------------------------------------------------
# The engine.
# ---------------------------------------------------------------------------
def ancestral_frequencies(m, rng, lo_hi):
    lo, hi = math.log(lo_hi[0]), math.log(lo_hi[1])
    return np.exp(rng.random(m) * (hi - lo) + lo)


def drift(p, ne, t, rng):
    """Closed-population Wright-Fisher on frequencies: no mutation, no migration."""
    two_n = int(round(2 * ne))
    for _ in range(t):
        p = rng.binomial(two_n, p) / two_n
    return p


def het(p):
    return 2.0 * p * (1.0 - p)


def genotypes(p, n_ind, rng):
    """Diploid dosages under Hardy-Weinberg as the sum of two Bernoulli draws.

    `rng.binomial(2, p, size=...)` re-enters the binomial generator once per
    entry; two uniform comparisons draw the same distribution far faster.
    """
    return ((rng.random((n_ind, p.size)) < p).astype(np.float64)
            + (rng.random((n_ind, p.size)) < p).astype(np.float64))


def score_and_r2(p_t, beta, w_pa, ve, n_ind, rng):
    """Realised R2 of the source-built per-allele score against target phenotype."""
    gv = np.zeros(n_ind)
    s_pa = np.zeros(n_ind)
    for lo in range(0, p_t.size, CHUNK):
        hi = min(lo + CHUNK, p_t.size)
        g = genotypes(p_t[lo:hi], n_ind, rng)
        gv += g @ beta[lo:hi]
        s_pa += g @ w_pa[lo:hi]
    y = gv + rng.standard_normal(n_ind) * math.sqrt(ve)
    return float(np.corrcoef(s_pa, y)[0, 1]) ** 2


def one_block(t, ne_s, ne_t_list, lo_hi, rng, want_r2=True):
    """One replicate: a shared ancestral draw, one source branch, several targets.

    The target sizes share `p0`, `beta` and the source branch on purpose -- that
    is what makes the NeT sweep a paired comparison, so a movement in Phi across
    NeT cannot be ancestral-draw scatter.
    """
    p0 = ancestral_frequencies(M_LOCI, rng, lo_hi)
    beta = rng.standard_normal(M_LOCI) / math.sqrt(M_LOCI)
    h0 = het(p0)
    va0 = float(np.sum(beta ** 2 * h0))
    ve = va0 * (1.0 - R2_0) / R2_0        # so the ancestral R2 is exactly R2_0

    p_s = drift(p0, ne_s, t, rng)
    h_s = het(p_s)
    poly_s = (p_s > 0.0) & (p_s < 1.0)
    f_s = 1.0 - float(np.mean(h_s)) / float(np.mean(h0))
    ret_s = float(np.mean(h_s)) / float(np.mean(h0))
    w_pa = np.where(poly_s, beta, 0.0)

    # The body's weights: effect sizes and ANCESTRAL heterozygosities.
    w_body = beta ** 2 * h0
    phi_pred = source_polymorphic_signal_fraction(w_body, p0, ne_s, t)
    # THE COMPETING FORMS, on this same block. Every one of them is a function of
    # `p0`, `beta` and the pair `(ne_s, t)` alone, so none of them draws from
    # `rng`: adding them cannot move any number this battery already recorded.
    phi_rivals = source_polymorphic_rivals(w_body, p0, ne_s, t)

    per = {}
    for ne_t in ne_t_list:
        p_t = drift(p0, ne_t, t, rng)
        h_t = het(p_t)
        f_t = 1.0 - float(np.mean(h_t)) / float(np.mean(h0))
        # The oracle for Phi: the realised fraction of the TARGET's signal that
        # sits on variants still polymorphic in the source. Its weighting is the
        # target's realised heterozygosity, which is why constancy in NeT is a
        # measurement and not a restatement of the argument list.
        sig = beta ** 2 * h_t
        phi_meas = float(np.sum(sig * poly_s) / max(np.sum(sig), 1e-300))
        r2_pa = (score_and_r2(p_t, beta, w_pa, ve, N_IND, rng)
                 if want_r2 else float("nan"))
        per[ne_t] = dict(f_t=f_t, phi_meas=phi_meas, r2_pa=r2_pa,
                         ret_t=1.0 - f_t)
    return dict(f_s=f_s, ret_s=ret_s, phi_pred=phi_pred,
                phi_rivals=phi_rivals, per=per)


def blocked(vals):
    a = np.asarray(vals, float)
    if a.size < 2:
        return float(a.mean()), float("nan")
    return float(a.mean()), float(a.std(ddof=1) / math.sqrt(a.size))


def paired_sem(pred, meas):
    d = np.asarray(meas, float) - np.asarray(pred, float)
    if d.size < 2:
        return float("nan")
    return float(d.std(ddof=1) / math.sqrt(d.size))


def cell(design, pred, meas):
    """A cell carrying the MEASUREMENT-ONLY sem, with the paired sem printed.

    Both bars are computed every time so that switching between them is never
    something a reader has to take on trust.
    """
    lean = float(np.mean(pred))
    truth, sem_m = blocked(meas)
    sem_p = paired_sem(pred, meas)
    print("      %-34s pred %9.6f  meas %9.6f  sem(meas) %8.6f  "
          "sem(paired) %8.6f  -> %6.2f sems (paired %6.2f)"
          % (design, lean, truth, sem_m, sem_p,
             abs(truth - lean) / max(sem_m, 1e-12),
             abs(truth - lean) / max(sem_p, 1e-12)))
    return dict(design=design, lean=lean, truth=truth, sem=max(sem_m, 1e-12))


# ---------------------------------------------------------------------------
CACHE = {}


def runs_for(t, lo_hi, ne_t_list, want_r2=True, ne_s=NE_S):
    """Blocks for one design, cached, with a REPRODUCIBLE seed.

    The seed is a crc32 of the design rather than `hash()`: Python randomises
    string hashing per process, so a `hash()`-derived seed would give a different
    simulation on every run and the committed results could never be reproduced
    from the committed source.
    """
    import zlib
    key = (t, lo_hi, tuple(ne_t_list), want_r2, ne_s)
    if key not in CACHE:
        rng = np.random.default_rng(zlib.crc32(repr(key).encode()))
        CACHE[key] = [one_block(t, ne_s, ne_t_list, lo_hi, rng, want_r2)
                      for _ in range(BLOCKS)]
    return CACHE[key]


def drift_control(t, lo_hi):
    """ENGINE control: realised heterozygosity retention against (1-1/2Ne)^t.

    Deliberately NOT about any formula under test. It is a property of the
    Wright-Fisher sampler alone, it is exact rather than asymptotic, and it fails
    if the sampler, the generation count or the heterozygosity bookkeeping is
    wrong -- the failure modes that would otherwise be attributed to a body.
    """
    b = runs_for(t, lo_hi, (NE_T_REF,), want_r2=False)
    m, s = blocked([x["ret_s"] for x in b])
    return dict(design="H_S/H_0 after t=%d at NeS=%d, %s" % (t, NE_S, lo_hi[0]),
                lean=neutral_drift_factor(NE_S, t), truth=m, sem=max(s, 1e-12))


# ---------------------------------------------------------------------------
def r2_zero_time_control(lo_hi):
    """ENGINE control: at t=0 the measured target R2 must be the constructed r2_0.

    No drift has happened, so this is a statement about the genotype sampler, the
    phenotype construction and the score, and about nothing under test. It CAN
    fail: a wrong environmental variance, a Hardy-Weinberg error or a misaligned
    weight vector all move it, and none of those is a formula. That is the point
    -- a control built out of the quantities the body is made of could only
    confirm that arithmetic is arithmetic.
    """
    b = runs_for(0, lo_hi, (NE_T_REF,))
    m, s = blocked([x["per"][NE_T_REF]["r2_pa"] for x in b])
    return dict(design="t=0, no drift: measured target R2 is the constructed "
                       "V_A/(V_A+V_E)",
                lean=R2_0, truth=m, sem=max(s, 1e-12))


# ---------------------------------------------------------------------------
# The designs. Every row below is measured on ALL of them, so that the corpus
# row for a body carries its spectrum variation, its NeT variation and its
# source-off limit in ONE record rather than in several -- several untagged
# records for one declaration is how a design gets counted twice, and a TAGGED
# record is read by the ledger as a COMPETITOR, which a second design of the
# same body is not.
# ---------------------------------------------------------------------------
def designs():
    """(label, blocks, ne_t, is_source_off) over every cell in the battery."""
    out = []
    for name, lo_hi in SPECTRA.items():
        for t in T_GRID:
            out.append(("t=%d %s" % (t, name),
                        runs_for(t, lo_hi, (NE_T_REF,)), NE_T_REF, False))
    lo_hi = SPECTRA["1/p on [0.01,0.99]"]
    b = runs_for(T_NET, lo_hi, NE_T_GRID)
    for ne_t in NE_T_GRID:
        out.append(("NeT=%d (NeS=%d t=%d)" % (ne_t, NE_S, T_NET), b, ne_t, False))
    for t in T_GRID:
        out.append(("t=%d NeS=%d source drift off" % (t, NE_S_OFF),
                    runs_for(t, lo_hi, (NE_T_REF,), ne_s=NE_S_OFF),
                    NE_T_REF, True))
    return out


def group_phi():
    """A. `sourcePolymorphicSignalFraction`, first class, with a sem.

    Cells span both spectra and, at fixed (NeS, t), four target sizes. The NeT
    cells are what makes the record more than a restatement: the prediction has
    no NeT argument, but the ORACLE weights by the target's realised
    heterozygosity, which does drift with NeT.
    """
    print("\n== GROUP A: sourcePolymorphicSignalFraction, recorded first class")
    # THE SOURCE-OFF DESIGNS ARE EXCLUDED HERE, and this is not tidying. With
    # NeS = 200000 no locus fixes in 10000 draws, so Phi is 1 in the prediction
    # AND 1.0 in every block of the measurement: the cell cannot fail, and its
    # replicates being identical drives the sem onto the 1e-12 floor, which
    # reported a MATCH whose worst cell was "1888130 sems off". A cell that can
    # only agree contributes no evidence and destroys the error bar it is scored
    # against. Those designs earn their place in the R2 record, where Phi = 1
    # separates the chart from the source-branch factor and the measurement has
    # real variance; they earn nothing here.
    cells = []
    rival_cells = [[] for _ in RIVAL_PHI]
    for lab, b, ne_t, source_off in designs():
        if source_off:
            continue
        meas = [x["per"][ne_t]["phi_meas"] for x in b]
        cells.append(cell("Phi " + lab, [x["phi_pred"] for x in b], meas))
        for k in range(len(RIVAL_PHI)):
            rival_cells[k].append(
                cell("Phi " + lab + " [rival %d]" % (k + 1),
                     [x["phi_rivals"][k] for x in b], meas))
    record("sourcePolymorphicSignalFraction", LEAN_FILE,
           "(sum_j w_j * stillSegregatingProb NeS (p j) t) / sum_j w_j, "
           "w_j = beta_j^2 * h_0,j",
           cells,
           regime=(
               "clean two-branch split, forward Wright-Fisher on allele "
               "frequencies, %d loci, NeS=%d closed (raised to %d in the "
               "source-off cells), no mutation and no migration, %d blocks per "
               "cell. Two spectra, both 1/p, truncated at [0.01,0.99] and "
               "[0.05,0.95]. The oracle is the realised fraction of the "
               "TARGET's signal carried by variants still polymorphic in the "
               "source, sum beta^2 h_T 1[poly_S] / sum beta^2 h_T. The "
               "prediction is Kimura's diffusion solution at each block's own "
               "realised ancestral frequencies. Error bars are measurement-only"
               % (M_LOCI, NE_S, NE_S_OFF, BLOCKS)),
           control=drift_control(T_GRID[-1], SPECTRA["1/p on [0.01,0.99]"]),
           realised_inputs=True, argument_source="model",
           note="the NeT cells carry a single prediction against four target "
                "sizes; the oracle's weighting drifts with NeT even though the "
                "prediction has no NeT argument. The two competing forms this "
                "body's docstring said it OWED are now carried on these same "
                "fourteen cells -- the unweighted still-segregating fraction and "
                "the heterozygosity-retention reading 1 - F_S -- together with "
                "the spectrum-collapsed and series-truncated readings, so the "
                "agreement above is scored against designs that could have "
                "disagreed rather than against nothing")
    reg_rival = ("the fourteen cells of the corpus row above, same blocks, same "
                 "oracle: the realised fraction of the TARGET's signal carried "
                 "by variants still polymorphic in the source")
    ctrl = drift_control(T_GRID[-1], SPECTRA["1/p on [0.01,0.99]"])
    for k, (tag, src) in enumerate(RIVAL_PHI):
        record("sourcePolymorphicSignalFraction [%s]" % tag, LEAN_FILE, src,
               rival_cells[k], regime=reg_rival, control=ctrl,
               realised_inputs=True, argument_source="model",
               note=("this rival's rejection is PARTLY FORCED and is labelled "
                     "so rather than counted: 6 p (1-p) exp(-t/(2 NeS)) exceeds "
                     "one at shallow t on the spectrum with no rare variants, "
                     "which sourcePolymorphicSignalFraction_mem_Icc forbids a "
                     "priori, so its failure there is arithmetic and not "
                     "measurement. What the row measures is the depth at which "
                     "the leading-eigenfunction approximation becomes adequate. "
                     "The other three rivals are false in no cell a priori and "
                     "are the ones that make the corpus row informative"
                     if k == 3 else ""))


def group_r2():
    """B/C/D. The composed law, and the two rivals, on every design at once."""
    print("\n== GROUP B: cleanSplitTargetR2' and its rivals, over spectrum, "
          "NeT and the source-off limit")
    ds = designs()
    cells, sum_cells, tbo_cells = [], [], []
    for lab, b, ne_t, _ in ds:
        meas = [x["per"][ne_t]["r2_pa"] for x in b]
        cells.append(cell(lab,
                          [clean_split_target_r2_prime(
                              R2_0, x["per"][ne_t]["f_t"], x["phi_pred"], 1.0)
                           for x in b], meas))
        sum_cells.append(cell("[summed] " + lab,
                              [summed_index_r2(R2_0, x["f_s"],
                                               x["per"][ne_t]["f_t"], 1.0)
                               for x in b], meas))
        tbo_cells.append(cell("[chart only] " + lab,
                              [target_branch_only_r2(
                                  R2_0, x["per"][ne_t]["f_t"], 1.0)
                               for x in b], meas))

    reg = ("same engine, %d target individuals per block, %d blocks, TRUE causal "
           "effects so no GWAS-inefficiency confound is present, r2_0 = %.2f "
           "realised in every block because the environmental variance is set "
           "from that block's own realised ancestral V_A. ldFactor = 1: the "
           "frequency engine carries no linkage, so the LD slot is exercised "
           "rather than measured. PER-ALLELE score only. Cells span two spectra "
           "at five depths, four NeT at fixed (NeS,t) sharing their ancestral "
           "draw and source branch, and a source-off limit at NeS=%d. Each "
           "prediction is re-evaluated in every block at that block's own "
           "realised per-branch heterozygosity loss and realised ancestral "
           "frequencies. Error bars are MEASUREMENT-ONLY, which is at or above "
           "the paired bar the design could claim"
           % (N_IND, BLOCKS, R2_0, NE_S_OFF))
    ctrl = r2_zero_time_control(SPECTRA["1/p on [0.01,0.99]"])

    record("cleanSplitTargetR2'", LEAN_FILE,
           "neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor "
           "NeT t)) * sourcePolymorphicSignalFraction w p NeS t * ldFactor",
           cells, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model",
           note="per-allele score only; the source-standardised score is a "
                "different observable, is measured in battery_clean01, and is "
                "deliberately NOT recorded against this body")
    record("cleanSplitTargetR2' [the SUPERSEDED summed-index body, both "
           "branches in the chart's fst slot and no source-branch factor, "
           "competing]", LEAN_FILE,
           "neutralPortability r2_0 (cleanSplitFst NeS NeT t) * ldFactor",
           sum_cells, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model",
           note="it passed battery_clean01's t=100 cell on the [0.01,0.99] "
                "spectrum by a cancellation; the [0.05,0.95] cells are where "
                "that pass dies, and a battery on one spectrum could not have "
                "seen it")
    record("cleanSplitTargetR2' [the chart alone, Phi forced to 1, competing]",
           LEAN_FILE,
           "neutralPortability r2_0 (fstFromDriftFactor (neutralDriftFactor "
           "NeT t)) * ldFactor",
           tbo_cells, regime=reg, control=ctrl,
           realised_inputs=True, argument_source="model",
           note="the upper bound cleanSplitTargetR2'_le_targetBranchOnly fixes. "
                "In the source-off cells it COINCIDES with the corrected body, "
                "because Phi is 1 there; those cells therefore test the chart "
                "alone and are what separates the two factors instead of "
                "fitting them jointly")


def group_source_branch_charge():
    """The 27x, printed as the arithmetic it is rather than asserted."""
    print("\n== The source-branch charge, truth against the summed body")
    print("    %-22s %10s %12s %10s" % ("spectrum, t", "1-Phi",
                                        "(1-r2_0)F_S", "ratio"))
    for name, lo_hi in SPECTRA.items():
        for t in T_GRID:
            b = runs_for(t, lo_hi, (NE_T_REF,))
            src_true = 1.0 - float(np.mean([x["phi_pred"] for x in b]))
            src_summed = (1.0 - R2_0) * float(np.mean([x["f_s"] for x in b]))
            print("    %-22s %10.5f %12.5f %9.1fx"
                  % ("%s t=%d" % (name, t), src_true, src_summed,
                     src_summed / max(src_true, 1e-12)))


def main():
    print(freshness())
    print("M_LOCI=%d N_IND=%d BLOCKS=%d R2_0=%.2f NeS=%d"
          % (M_LOCI, N_IND, BLOCKS, R2_0, NE_S))
    failed = run_groups(group_phi, group_r2, group_source_branch_charge)
    here = os.path.dirname(os.path.abspath(__file__))
    sha = dump_results(os.path.join(here, "battery_clean02_results.json"),
                       failed_groups=failed)
    print("\nbattery sha %s" % sha)


if __name__ == "__main__":
    main()

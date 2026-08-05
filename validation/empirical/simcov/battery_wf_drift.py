"""In-regime test of ClosedPopulationNoMutation.retention.

CLAIM UNDER TEST:  H_t / H_0 == (1 - 1/(2 Ne))^t
REGIME:            closed population, NO mutation. This is the regime the
                   structure's `mutation_negligible` field enforces; the run
                   that produced the FALSIFIED verdict was at demographic
                   equilibrium, where mutation is not negligible.

DESIGN.  Forward Wright-Fisher on independent biallelic loci, mutation rate
zero, starting from standing variation. Per generation each locus draws
Binomial(2Ne, p)/(2Ne). The decay H_{t+1} = H_t (1 - 1/(2Ne)) is exact in
EXPECTATION for Wright-Fisher irrespective of linkage -- linkage changes the
variance, not the mean -- so independent loci is the correct design and gives
tighter bars than a linked one.

THE DENOMINATOR TRAP, handled explicitly.  H is averaged over ALL loci,
including those that have fixed (which contribute 0). Conditioning on loci that
are still segregating inflates H exactly where drift has done its work, which
is this regime. The conditioned estimator is printed in sems from the all-loci
value, so a reader can see the design is sensitive to the trap. It is neither
the `control=` argument nor a ledger row, and both exclusions are deliberate:
`verdict.classify` requires a control to PASS, and the trap is built to fail;
and as a competitor its oracle is nearly constant across the design (0.9174
against 0.9173), so the DEGENERATE ORACLE gate fires and the row asserts
nothing in either direction. The positive control is instead the martingale
`E[p_t] = p_0`, which no ploidy or normalisation slip in the resampling loop
can survive.

COMPETITORS, on the same cells, because a match against no alternative is not a
measurement:
    (1 - 1/Ne)^t        haploid ploidy
    (1 - 1/(2Ne))^(2t)  doubled exponent
    exp(-t/(2Ne))       diffusion limit
    1                   no decay at all

WHY THIS FILE WAS REWRITTEN. It ran, printed a correct table, and reached the
ledger as nothing at all: it dumped to `wf_drift_results.json`, which the
ledger's `battery_*_results.json` glob does not match, and it called `record()`
nowhere, so its competitors were columns in a printout rather than rows a gate
could count. `retention`'s docstring cited it and the citation dangled. A
battery that bypasses `record()`/`dump_results` is evidence nobody's guard can
read, which is the same as no evidence.

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import json, math, os, sys
import numpy as np

from battery_core import RESULTS, dump_results, record

GUARD = "wf-drift-in-regime-v1"
FRESH_TOKEN = "SIMCOV-BATTERY-WFDRIFT-HARRIER-20260805"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def run(ne, n_loci, n_reps, generations, seed):
    rng = np.random.default_rng(seed)
    two_n = 2 * ne
    # Standing variation at t = 0. Uniform on (0,1) keeps the initial spectrum
    # broad rather than concentrating it where drift is slowest.
    p = rng.uniform(0.05, 0.95, size=(n_reps, n_loci))
    h0_all = (2 * p * (1 - p)).mean(axis=1)
    h0_seg = h0_all.copy()
    # POSITIVE CONTROL, on the same draws and the same code path: Wright-Fisher
    # drift is a martingale in the allele frequency, so E[p_t] = p_0 exactly,
    # for every t, independently of the heterozygosity claim under test. If the
    # binomial resampling loop is wrong -- a ploidy slip in `two_n`, a
    # normalisation error -- the mean moves and the control fails. The
    # segregating-only estimator is NOT used as the control: a control must be
    # a cell whose answer is independently KNOWN and which the code path
    # reproduces, and that one is a trap designed to fail, which is a different
    # instrument. It rides along as a competitor instead.
    pbar0 = p.mean(axis=1)

    out = []
    checkpoints = sorted(set(int(round(g)) for g in generations))
    for gen in range(1, max(checkpoints) + 1):
        p = rng.binomial(two_n, p) / two_n
        if gen in checkpoints:
            het = 2 * p * (1 - p)
            ratio_all = het.mean(axis=1) / h0_all
            seg = het > 0
            with np.errstate(invalid="ignore"):
                seg_mean = np.where(seg.sum(axis=1) > 0,
                                    (het * seg).sum(axis=1) / np.maximum(seg.sum(axis=1), 1),
                                    np.nan)
            ratio_seg = seg_mean / h0_seg
            pbar_ratio = p.mean(axis=1) / pbar0
            out.append({
                "generations": gen,
                "pbar_ratio": float(pbar_ratio.mean()),
                "pbar_ratio_sem": float(pbar_ratio.std(ddof=1) / np.sqrt(n_reps)),
                "measured": float(ratio_all.mean()),
                "sem": float(ratio_all.std(ddof=1) / np.sqrt(n_reps)),
                "measured_segregating_only": float(np.nanmean(ratio_seg)),
                "predicted": float((1 - 1 / two_n) ** gen),
                "competitor_haploid": float((1 - 1 / ne) ** gen),
                "competitor_doubled": float((1 - 1 / two_n) ** (2 * gen)),
                "competitor_diffusion": float(np.exp(-gen / two_n)),
                "competitor_no_decay": 1.0,
            })
    return out


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-WFDRIFT-HARRIER-20260805")
    print(f"GUARD={GUARD}")
    print(f"numpy={np.__version__}")
    results = {}
    for ne in (100, 250):
        gens = [int(ne * f) for f in (0.25, 0.5, 1.0, 2.0)]
        rows = run(ne=ne, n_loci=5000, n_reps=40, generations=gens, seed=20260804 + ne)
        results[ne] = rows
        print(f"\n=== Ne = {ne}, 5000 loci, 40 replicates, mutation rate 0 ===")
        print(f"{'t':>6} {'measured':>10} {'sem':>8} {'predicted':>10} {'sems':>7}"
              f" {'haploid':>9} {'doubled':>9} {'diffusion':>10} {'segOnly':>9}")
        for r in rows:
            def sems(x):
                return abs(r["measured"] - x) / r["sem"] if r["sem"] > 0 else float("inf")
            print(f"{r['generations']:>6} {r['measured']:>10.5f} {r['sem']:>8.5f} "
                  f"{r['predicted']:>10.5f} {sems(r['predicted']):>7.2f} "
                  f"{sems(r['competitor_haploid']):>9.1f} {sems(r['competitor_doubled']):>9.1f} "
                  f"{sems(r['competitor_diffusion']):>10.1f} "
                  f"{sems(r['measured_segregating_only']):>9.1f}")

    # ---- into the harness, so the ledger can read this ---------------------
    # One cell per (Ne, t). `lean` is the transcribed body, `truth` the measured
    # ratio, `sem` its across-replicate standard error. Every competitor is a
    # ROW rather than a printed column, because `ledger.py` clears a MATCH only
    # when a competing formula was REJECTED on the same cells, and it can only
    # count rows.
    cells, c_haploid, c_doubled, c_diffusion, c_nodecay, c_segonly = (
        [], [], [], [], [], [])
    control = None
    for ne, rows in results.items():
        for r in rows:
            lab = "Ne=%d t=%d" % (ne, r["generations"])
            common = dict(design=lab, truth=r["measured"], sem=r["sem"])
            cells.append(dict(lean=r["predicted"], **common))
            c_haploid.append(dict(lean=r["competitor_haploid"], **common))
            c_doubled.append(dict(lean=r["competitor_doubled"], **common))
            c_diffusion.append(dict(lean=r["competitor_diffusion"], **common))
            c_nodecay.append(dict(lean=r["competitor_no_decay"], **common))
            # The trap, as a competitor: conditioning on still-segregating loci
            # inflates H exactly where drift has done its work. Its `truth` is
            # the conditioned measurement and its `lean` the body, so a large
            # miss here is the design demonstrating it is sensitive to the trap.
            c_segonly.append(dict(design=lab, lean=r["predicted"],
                                  truth=r["measured_segregating_only"],
                                  sem=r["sem"]))
            if control is None:
                control = dict(design=lab + " [E[p_t]/p_0, martingale]",
                               lean=1.0, truth=r["pbar_ratio"],
                               sem=r["pbar_ratio_sem"])

    reg = ("forward Wright-Fisher on 5000 independent biallelic loci per "
           "replicate, 40 replicates, MUTATION RATE ZERO -- the closed-"
           "population no-mutation regime `mutation_negligible` enforces, not "
           "the demographic equilibrium at which the superseded FALSIFIED "
           "verdict was taken. Per generation each locus draws "
           "Binomial(2Ne, p)/(2Ne); H is averaged over ALL loci including "
           "fixed ones. Ne in {100, 250}, t in {Ne/4, Ne/2, Ne, 2Ne}")
    # `realised_inputs=True`, and why it is not a fudge: every input to the
    # prediction is an EXACT model constant. `Ne` is the integer the binomial
    # was given and `t` is a loop counter; neither is estimated from the sample,
    # so there is no nominal/realised gap that could be the size of a finding.
    # The one quantity that IS measured, H_0, appears in both the prediction's
    # denominator and the oracle's, per replicate.
    MODEL = dict(regime=reg, control=control, realised_inputs=True)

    record("ClosedPopulationNoMutation.retention", "PortabilityDrift.lean", "(1 - 1 / (2 * Ne))^t", cells,
           **MODEL)
    record("retention [haploid ploidy, competing]", "PortabilityDrift.lean",
           "(1 - 1 / Ne)^t", c_haploid, **MODEL)
    record("retention [doubled exponent, competing]", "PortabilityDrift.lean",
           "(1 - 1 / (2 * Ne))^(2 * t)", c_doubled, **MODEL)
    record("retention [diffusion limit, competing]", "PortabilityDrift.lean",
           "exp(-t / (2 * Ne))", c_diffusion, **MODEL)
    record("retention [no decay at all, competing]", "PortabilityDrift.lean",
           "1", c_nodecay, **MODEL)
    # NOT recorded as a competitor row. The conditioned estimator is not a
    # competing FORMULA -- it is the same body read against a different
    # denominator -- and its oracle is nearly constant across the design
    # (0.9174 at Ne=250 t=250 against 0.9173 at t=500), so `verdict.classify`
    # correctly calls it a DEGENERATE ORACLE and it asserts nothing either way.
    # The trap is real and the design is sensitive to it; that is what the
    # printed `segOnly` column above shows, in sems, and it is quoted in the
    # docstring. A row that can carry no verdict does not belong in the ledger.
    print("\ntrap sensitivity (NOT a ledger row): the same ratio over only "
          "the still-segregating loci, in sems from the all-loci value:")
    for c in c_segonly:
        print("  %-14s %8.1f sems" % (c["design"],
                                      abs(c["lean"] - c["truth"]) / c["sem"]))

    dump_results("battery_wf_drift_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-10s %-62s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    sys.exit(main())

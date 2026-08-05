"""Battery drift05: the drift/covariance-retention chain, five definitions on ONE design.

The chain, as the corpus composes it:

    targetHetFromFst              het_source * (1 - fst)
    covarianceRetentionFactorFromFst              1 - fst
    covarianceDivergenceMutationDrift   fst + (1 - fst)*(1 - shared_ld)
    presentDayPGSVarianceMutationDrift  (1 - covarianceDivergence) * V_A
    presentDayR2MutationDrift           v / (v + V_E),  v the line above

One Wright-Fisher simulation with recombination supplies every observable, which
is the point: these five are a single claim written in five pieces, and a
battery per piece would test the composition nowhere. Here the LAST one is
compared against a realised R-squared computed from the same run that supplied
the first, so the whole chain is on trial at once.

WHERE THE ARGUMENTS COME FROM, because that is what decides whether any of this
means anything. `fst` is the MODEL's per-branch drift coefficient
`1 - (1 - 1/(2*Ne))^t`, computed from the simulation's own `Ne` and `t` and
nothing else. It is never estimated from the replicates the oracle measures --
that is the `battery_bulk21` mistake, where a sample-estimated F turned
`p0(1-p0)*F` into the estimator's own definition of `Var(p)` and nothing was on
trial. Declared as `argument_source="model"`.

`shared_ld` likewise comes from the recombination fraction and elapsed time as
`(1-r)^(2t)`, the corrected `sharedLDRetention`, not from a measured LD decay.

WHAT THIS BATTERY DOES NOT ESTABLISH, and why it records only two of the five.
A first version recorded all five and all five matched at under 0.6 sems with
every competitor refuted. Three of those were not measurements. `shared_ld` is
computed from the model on BOTH sides -- it multiplies the prediction and it
was multiplied into the "measured" divergence by hand -- so the LD half of
`covarianceDivergenceMutationDrift` was never on trial, and the refutation of
its LD-term-dropped competitor was manufactured by inserting the very factor
the competitor omits. `presentDayPGSVarianceMutationDrift` and
`presentDayR2MutationDrift` inherit that, being the same quantity through two
more maps. A common factor on both sides of a comparison cancels, and a
competitor rejected by a factor the design put there is the identity failure in
its clearest form.

So only the two definitions whose oracle is a genuine Wright-Fisher measurement
are recorded. Establishing the other three needs `shared_ld` MEASURED -- a
recombination simulation of haplotype sharing, as `battery_sld03` does -- and
that is a different design, not a relabelling of this one.

COMPETITORS, one per recorded definition:
    targetHetFromFst              het*(1-2*fst)      -- the pairwise reading
    covarianceRetentionFactor     (1-fst)^2          -- retention squared

FRESHNESS: prints FRESHNESS=OK only if its own source carries the token below,
and `dump_results` records this file's SHA inside the results.
"""
import math
import os

import numpy as np

from battery_core import RESULTS, dump_results, record

FRESH_TOKEN = "SIMCOV-BATTERY-DRIFT05-SHEARWATER-20260804"


def freshness():
    try:
        src = open(os.path.abspath(__file__)).read()
    except Exception:
        print("FRESHNESS=STALE (cannot read own source)")
        return
    print("FRESHNESS=%s (token %s)"
          % ("OK" if src.count(FRESH_TOKEN) >= 2 else "STALE", FRESH_TOKEN))


def main():
    freshness()
    print("FRESHNESS token literal: SIMCOV-BATTERY-DRIFT05-SHEARWATER-20260804")
    rng = np.random.default_rng(50501)
    nloci = 300000
    p0 = 0.3
    V_E = 1.0

    het_cells, het_comp = [], []
    cov_cells, cov_comp = [], []
    div_cells, div_comp = [], []
    var_cells, var_comp = [], []
    r2_cells, r2_comp = [], []
    control = None

    designs = ((200, 40, 0.02), (200, 120, 0.02), (500, 80, 0.05),
               (100, 30, 0.10))
    for Ne, t, recomb in designs:
        # --- Wright-Fisher drift in one deme from a common ancestor ---------
        p = np.full(nloci, p0)
        for _ in range(t):
            p = rng.binomial(2 * Ne, p) / (2.0 * Ne)
        F = 1.0 - (1.0 - 1.0 / (2.0 * Ne)) ** t          # MODEL value
        shared = (1.0 - recomb) ** (2 * t)               # MODEL value

        # heterozygosity retention, measured
        het_anc = 2 * p0 * (1 - p0)
        het_now = float(np.mean(2 * p * (1 - p)))
        sem_het = float(np.std(2 * p * (1 - p), ddof=1)) / math.sqrt(nloci)

        # additive-variance retention with FIXED effects: the ancestral-weighted
        # score's genetic variance in the drifted deme is sum b^2 2p(1-p), so
        # the retention is the heterozygosity ratio on the same draws
        cov_ret = het_now / het_anc
        sem_cov = sem_het / het_anc

        # the LD-sharing factor is applied to the retained covariance: only the
        # fraction of the score's covariance carried by still-shared haplotypes
        # survives, so the measured divergence is 1 - retention*shared
        div_meas = 1.0 - cov_ret * shared
        sem_div = sem_cov * shared

        V_A = 0.5
        v_meas = (1.0 - div_meas) * V_A
        sem_v = sem_div * V_A
        r2_meas = v_meas / (v_meas + V_E)
        sem_r2 = sem_v * V_E / (v_meas + V_E) ** 2

        lab = "Ne=%d t=%d r=%.2f (F=%.4f, shared=%.4f)" % (Ne, t, recomb, F,
                                                           shared)
        print("  %-44s het %.5f ± %.5f (body %.5f) | ret %.5f (body %.5f) | "
              "div %.5f (body %.5f)"
              % (lab, het_now, sem_het, het_anc * (1 - F), cov_ret, 1 - F,
                 div_meas, F + (1 - F) * (1 - shared)))

        het_cells.append(dict(design=lab, lean=het_anc * (1 - F),
                              truth=het_now, sem=sem_het))
        het_comp.append(dict(design=lab, lean=het_anc * (1 - 2 * F),
                             truth=het_now, sem=sem_het))
        cov_cells.append(dict(design=lab, lean=1 - F, truth=cov_ret,
                              sem=sem_cov))
        cov_comp.append(dict(design=lab, lean=(1 - F) ** 2, truth=cov_ret,
                             sem=sem_cov))
        div_cells.append(dict(design=lab, lean=F + (1 - F) * (1 - shared),
                              truth=div_meas, sem=sem_div))
        div_comp.append(dict(design=lab, lean=F, truth=div_meas, sem=sem_div))
        var_cells.append(dict(design=lab,
                              lean=(1 - (F + (1 - F) * (1 - shared))) * V_A,
                              truth=v_meas, sem=sem_v))
        var_comp.append(dict(design=lab, lean=(1 - F) * V_A, truth=v_meas,
                             sem=sem_v))
        vb = (1 - (F + (1 - F) * (1 - shared))) * V_A
        r2_cells.append(dict(design=lab, lean=vb / (vb + V_E), truth=r2_meas,
                             sem=sem_r2))
        vc = (1 - F) * V_A
        r2_comp.append(dict(design=lab, lean=vc / (vc + V_E), truth=r2_meas,
                            sem=sem_r2))

        if Ne == 200 and t == 40:
            # Control: drift is unbiased, so the mean frequency is still p0.
            # Independent of every body under test and it can fail.
            control = dict(design="Ne=200 t=40 [drift unbiased: E[p_t] = p0]",
                           lean=p0, truth=float(p.mean()),
                           sem=float(p.std(ddof=1)) / math.sqrt(nloci))

    reg = ("Wright-Fisher binomial sampling in one deme from a common ancestor "
           "at p0 = 0.3, 300000 independent loci, t generations, no mutation; "
           "the observables are the realised mean heterozygosity and the "
           "additive-variance retention it implies for a fixed-effect score. "
           "fst is the MODEL's 1-(1-1/(2Ne))^t and shared_ld the model's "
           "(1-r)^(2t) -- neither is estimated from the replicates the oracle "
           "measures, which is what keeps this from being the battery_bulk21 "
           "identity. Ne, t and r are swept so the prediction spans a factor "
           "of four")
    MODEL = dict(regime=reg, control=control, argument_source="model",
                 realised_inputs=True)

    record("targetHetFromFst", "PortabilityDrift.lean",
           "het_source * (1 - fst)", het_cells, **MODEL)
    record("targetHetFromFst [pairwise reading 1 - 2*fst, competing]",
           "PortabilityDrift.lean", "het_source * (1 - 2*fst)", het_comp,
           **MODEL)
    record("covarianceRetentionFactorFromFst", "PortabilityDrift.lean",
           "1 - fst", cov_cells, **MODEL)
    record("covarianceRetentionFactorFromFst [retention squared, competing]",
           "PortabilityDrift.lean", "(1 - fst)^2", cov_comp, **MODEL)
    # covarianceDivergenceMutationDrift, presentDayPGSVarianceMutationDrift and
    # presentDayR2MutationDrift are DELIBERATELY NOT RECORDED. See the module
    # docstring: `shared_ld` is a model value multiplied into both the
    # prediction and the oracle, so it cancels, the LD half of the composition
    # is untested, and the competitor that drops it is rejected by a factor
    # this design inserted rather than measured. They matched at under 0.6 sems
    # and that number means nothing.
    _ = (div_cells, div_comp, var_cells, var_comp, r2_cells, r2_comp)

    dump_results("battery_drift05_results.json")
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {}) or {}
        print("%-24s %-62s worst %9.2f sems, %8.2f%% rel"
              % (r["verdict"], r["name"][:62], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

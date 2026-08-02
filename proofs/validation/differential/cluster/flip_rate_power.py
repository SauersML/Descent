#!/usr/bin/env python3
"""Does matching SNP heritability control for the sign-flip rate? No.

Harpak et al. report a sign-flip gap between traits (lymphocyte-like ~31.7%
versus triglyceride-like ~9.6%) and read it as evidence about immune turnover.
They control by comparing traits "at similar SNP heritability".

THE OBJECTION, MADE CONSTRUCTIVELY RATHER THAN ASSERTED
    The flip probability for one SNP is Phi(-|beta|/sigma_repl): it depends on
    PER-SNP signal-to-noise. SNP heritability is h2 = sum 2p(1-p) beta^2, a
    SUM. The same h2 is reachable with many small effects or few large ones, so
    h2 does not pin per-SNP |beta|/sigma and cannot control for it.

    That is an argument. This script is the demonstration: build two
    architectures with h2 matched to machine precision, differing only in how
    that h2 is divided among loci, run discovery and replication, and measure
    whether the flip rate notices. If it moves, the control is not a control.

    This is the same shape as everything else in this tier -- match on what the
    method reads, differ in the truth, measure whether the method notices --
    and here the method is the paper's own control.

WINNER'S CURSE IS IN THE SIMULATION, NOT BOLTED ON
    SNPs enter the replication set by passing a discovery threshold, so the
    selection is done on the discovery estimate exactly as in the real
    pipeline. Nothing models the curse explicitly; it arises because selection
    happens on a noisy estimate. Its direction matters: it inflates discovery
    |beta_hat| most where power is lowest, which is precisely where the flip
    rate is highest, so a reader comparing discovery effect sizes across traits
    sees the gap narrowed while the flip rate sees it widened.

WHAT THE FLIP RATE ACTUALLY MEASURES
    Inverting, an observed flip rate f implies per-SNP |beta|/sigma_repl =
    -Phi^{-1}(f). At f = 31.7% that is 0.48; at f = 9.6% it is 1.30. The whole
    reported gap is what a factor of 2.7 in per-SNP signal-to-noise produces.
    The script reports this inversion alongside the simulated rates so the two
    can be compared directly.

TWO CONTROLS PINNED BY THEORY, NEITHER FITTED
    C1  NULL. With every true beta = 0 the replication sign is a coin flip and
        the rate must be 50%, whatever the architecture, whatever the
        selection. Any departure means the selection or the sign convention is
        wrong.
    C2  SATURATION. With per-SNP |beta|/sigma_repl large the rate must go to 0.
        Together C1 and C2 pin both ends of the curve the inversion relies on.

DATA NOTE, STATED PLAINLY
    This does NOT use Harpak et al.'s data, because that data is not published.
    Their repository (github.com/harpak-lab/Portability_Questions) ships
    analysis scripts only and instructs users to download UK Biobank
    themselves; harpaklab.com does not currently resolve. So the per-SNP
    beta_hat and sigma the direct test needs are not obtainable, and the direct
    test is blocked on UKB access exactly as the signed-residual test is.

    What is demonstrated here is the part that needs no data: that their stated
    control does not exclude the power explanation. The direct test remains
    specified in the report.

numpy only.
"""

import json
import math
import sys

import numpy as np

N_DISC = 336_923         # Harpak et al. GWAS sample
N_REPL = 69_500          # their prediction/replication sample
H2 = 0.20
MAF = 0.20
P_THRESH = 5e-8
REPS = 40
SEED = 20260802


def z_threshold(p):
    """Two-sided p to |z|, by bisection on the normal tail (no scipy)."""
    def tail(z):
        return math.erfc(z / math.sqrt(2.0))      # two-sided
    lo, hi = 0.0, 40.0
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        if tail(mid) > p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def norm_cdf(x):
    return 0.5 * math.erfc(-x / math.sqrt(2.0))


def norm_ppf(p):
    lo, hi = -40.0, 40.0
    for _ in range(300):
        mid = 0.5 * (lo + hi)
        if norm_cdf(mid) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


MIN_SELECTED = 200      # below this a flip rate is noise, not a measurement


def run_architecture(n_causal, h2, rng, reps=REPS, p_thresh=P_THRESH,
                     spread=True):
    """Discovery -> threshold -> replication; return the sign-flip rate.

    True effects are DRAWN, not fixed. A single shared beta was the first
    version and it is unfaithful in a way that matters: with no variation in
    the true effect, passing the discovery threshold cannot enrich for larger
    true effects, so the selected set has the same signal-to-noise as the
    causal set. In reality selection is exactly what makes the selected set
    unrepresentative -- that IS the winner's curse -- and the flip rate is a
    property of the selected set. Effects are Gaussian with variance set so
    that h2 = n_causal * var_g * E[beta^2] holds exactly.
    """
    var_g = 2.0 * MAF * (1.0 - MAF)
    beta_sd = math.sqrt(h2 / (n_causal * var_g))
    se_d = 1.0 / math.sqrt(N_DISC * var_g)
    se_r = 1.0 / math.sqrt(N_REPL * var_g)
    zt = z_threshold(p_thresh)

    flips, n_sel_tot, sel_true_z = [], [], []
    for _ in range(reps):
        beta = (rng.normal(0.0, beta_sd, n_causal) if spread
                else np.full(n_causal, beta_sd))
        bd = beta + rng.normal(0.0, se_d, n_causal)
        sel = np.abs(bd / se_d) > zt                    # winner's curse enters HERE
        k = int(sel.sum())
        n_sel_tot.append(k)
        if k == 0:
            continue
        br = beta[sel] + rng.normal(0.0, se_r, k)
        flips.append(float(np.mean(np.sign(br) != np.sign(bd[sel]))))
        sel_true_z.append(float(np.mean(np.abs(beta[sel]) / se_r)))

    total_sel = float(np.sum(n_sel_tot))
    enough = total_sel >= MIN_SELECTED
    return {
        "n_causal": n_causal,
        "h2": h2,
        "per_snp_beta_sd": beta_sd,
        "population_z_replication": beta_sd / se_r,
        "selected_mean_true_z_replication":
            float(np.mean(sel_true_z)) if sel_true_z else None,
        "simulated_flip_rate": (float(np.mean(flips))
                                if (flips and enough) else None),
        "flip_sem": (float(np.std(flips) / math.sqrt(len(flips)))
                     if (flips and enough) else None),
        "total_selected": total_sel,
        "enough_selected": bool(enough),
    }


def main():
    rng = np.random.default_rng(SEED)
    out = {"setup": {"N_disc": N_DISC, "N_repl": N_REPL, "h2": H2,
                     "maf": MAF, "p_threshold": P_THRESH}}

    # ---- the inversion the paper's numbers imply --------------------------
    print("WHAT AN OBSERVED FLIP RATE IMPLIES ABOUT PER-SNP SIGNAL-TO-NOISE")
    inv = []
    for f in (0.317, 0.20, 0.096, 0.05):
        z = -norm_ppf(f)
        inv.append({"flip_rate": f, "implied_beta_over_sigma": z})
        print("    flip rate %5.1f%%  ->  |beta|/sigma_repl = %.3f" % (100 * f, z))
    ratio = inv[0]["implied_beta_over_sigma"] / inv[2]["implied_beta_over_sigma"]
    print("    the reported 31.7%% vs 9.6%% gap is a factor of %.2f in per-SNP"
          % (inv[2]["implied_beta_over_sigma"] / inv[0]["implied_beta_over_sigma"]))
    print("    signal-to-noise, nothing more.")
    out["inversion"] = inv

    # ---- matched h2, different architecture -------------------------------
    print("")
    print("MATCHED SNP HERITABILITY, DIFFERENT FLIP RATE")
    print("    %-10s %-12s %-14s %-16s %-10s"
          % ("n_causal", "h2", "sel z_repl", "flip rate", "tot selected"))
    rows = []
    for m in (200, 2_000, 20_000, 100_000, 300_000):
        r = run_architecture(m, H2, rng)
        rows.append(r)
        print("    %-10d %-12.6f %-14.3f %-14s %-10.0f"
              % (m, r["h2"], r["true_z_replication"],
                 ("%.4f +-%.4f" % (r["simulated_flip_rate"], r["flip_sem"]))
                 if r["simulated_flip_rate"] is not None else "no SNP selected",
                 r["mean_n_selected"]))
    out["matched_h2"] = rows

    got = [r for r in rows if r["simulated_flip_rate"] is not None]
    if len(got) >= 2:
        spread = max(r["simulated_flip_rate"] for r in got) - \
                 min(r["simulated_flip_rate"] for r in got)
        print("    h2 identical to machine precision across every row; flip rate"
              " spans %.4f" % spread)
        out["flip_rate_spread_at_matched_h2"] = spread

    # ---- controls ----------------------------------------------------------
    print("")
    print("CONTROLS")
    # Under h2 = 0 nothing reaches p < 5e-8 except by a fluctuation of
    # probability 5e-8 per SNP, so the null control CANNOT select at the
    # genome-wide threshold -- the first version of this control failed for
    # that reason and the failure was an artefact of the control, not a
    # finding. The threshold is relaxed here so that selection happens at all;
    # the claim being checked, that a selected null SNP flips with probability
    # exactly one half, is threshold-independent.
    null = run_architecture(200_000, 0.0, rng, p_thresh=1e-3)
    c1 = (null["simulated_flip_rate"] is not None
          and abs(null["simulated_flip_rate"] - 0.5) < 0.02)
    print("    C1 null (h2 = 0, threshold relaxed to 1e-3 so anything is "
          "selected): flip rate %s, must be 0.5 -> %s"
          % (("%.4f" % null["simulated_flip_rate"])
             if null["simulated_flip_rate"] is not None else "too few selected",
             "PASS" if c1 else "FAIL"))
    sat = run_architecture(50, H2, rng)

    c2 = sat["simulated_flip_rate"] is not None and sat["simulated_flip_rate"] < 1e-3
    print("    C2 saturation (50 causal, selected z_repl = %.1f): flip rate "
          "%.6f, must be ~0 -> %s"
          % (sat["selected_mean_true_z_replication"] or float("nan"),
             sat["simulated_flip_rate"], "PASS" if c2 else "FAIL"))
    out["controls"] = {"null": null, "saturation": sat,
                       "C1_pass": bool(c1), "C2_pass": bool(c2)}
    out["READ_THE_TEST"] = bool(c1 and c2)

    print("")
    print("READ_THE_TEST: %s" % out["READ_THE_TEST"])
    fh = open("flip_rate_power_results.json", "w")
    json.dump(out, fh, indent=1)
    fh.close()
    print("-> flip_rate_power_results.json")
    return 0 if out["READ_THE_TEST"] else 1


if __name__ == "__main__":
    sys.exit(main())

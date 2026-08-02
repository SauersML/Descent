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


def run_architecture(n_causal, h2, rng, reps=REPS):
    """Discovery -> threshold -> replication; return the sign-flip rate.

    All causal SNPs share one MAF so that h2 is divided evenly and the only
    thing distinguishing architectures is HOW MANY loci carry it.
    """
    var_g = 2.0 * MAF * (1.0 - MAF)
    beta = math.sqrt(h2 / (n_causal * var_g))          # per-SNP true effect
    se_d = 1.0 / math.sqrt(N_DISC * var_g)
    se_r = 1.0 / math.sqrt(N_REPL * var_g)
    zt = z_threshold(P_THRESH)

    flips, n_sel_tot = [], []
    for _ in range(reps):
        bd = beta + rng.normal(0.0, se_d, n_causal)     # discovery estimates
        sel = np.abs(bd / se_d) > zt                    # winner's curse enters HERE
        k = int(sel.sum())
        n_sel_tot.append(k)
        if k == 0:
            continue
        br = beta + rng.normal(0.0, se_r, k)            # replication estimates
        flips.append(float(np.mean(np.sign(br) != np.sign(bd[sel]))))
    return {
        "n_causal": n_causal,
        "h2": h2,
        "per_snp_beta": beta,
        "true_z_discovery": beta / se_d,
        "true_z_replication": beta / se_r,
        "analytic_flip_rate": 1.0 - norm_cdf(beta / se_r),
        "simulated_flip_rate": float(np.mean(flips)) if flips else None,
        "flip_sem": float(np.std(flips) / math.sqrt(len(flips))) if flips else None,
        "mean_n_selected": float(np.mean(n_sel_tot)),
        "mean_discovery_beta_hat_if_selected": None,
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
    print("    %-10s %-12s %-14s %-14s %-10s"
          % ("n_causal", "h2", "true z_repl", "flip rate", "n selected"))
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
    null = run_architecture(20_000, 0.0, rng)
    c1 = (null["simulated_flip_rate"] is not None
          and abs(null["simulated_flip_rate"] - 0.5) < 0.02)
    print("    C1 null (h2 = 0): flip rate %s, must be 0.5 -> %s"
          % (("%.4f" % null["simulated_flip_rate"])
             if null["simulated_flip_rate"] is not None else "no SNP selected",
             "PASS" if c1 else "FAIL"))
    sat = run_architecture(50, H2, rng)
    c2 = sat["simulated_flip_rate"] is not None and sat["simulated_flip_rate"] < 1e-3
    print("    C2 saturation (50 causal, z_repl = %.1f): flip rate %.6f, must be"
          " ~0 -> %s" % (sat["true_z_replication"], sat["simulated_flip_rate"],
                         "PASS" if c2 else "FAIL"))
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

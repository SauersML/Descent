# The complete transport law, derived once, from the pipeline's generative definitions

This document replaces iterative candidate-patching with the full derivation. Every
reduction below is exact given the pipeline's own definitions (gen_real_pt.py /
stream_geno.py read directly); the single approximation is isolated in Step 5 and
carries a computable error bound. Nothing is fitted; nothing is graded before the
whole law is assembled.

## Step 0: the generative model, verbatim from the pipeline

Loci are laid on 20 independent 5 Mb chunks (cross-chunk independence is EXACT).
Per locus, deme frequencies p = (p_1..p_D) follow the neutral multi-deme diffusion
measure mu -- all of whose polynomial moments the corpus computes exactly (the
degree-4 hierarchy; higher degrees by the same closed construction). Causals: m
draws from the ascertained panel (pooled MAF >= 0.01), effects beta ~ N(0,1) iid;
liability G = sum beta_c g_c, standardized on the realized sample. GWAS: logistic
regression per SNP on the binary probit outcome in the train-deme fit split;
clumping (greedy plink, r^2 < 0.1 within 250 kb) then p-threshold selection with
the threshold chosen on the selection split. Score X = sum over index SNPs of
beta_hat_s g_s. Target: E[r2_j / r2_t] over seeds, where r2 = Corr^2(X, G) per deme
on test rows.

## Step 1: exact factorization over regions

Cross-chunk independence and clump-window locality partition every sum into clump
REGIONS. Writing A_j(s) = sum_c beta_c D_j(s, c) (the score channel's covariance
carrier in deme j) and noting that E[beta_c beta_c'] = delta_cc':

    Cov_j(X, G) = sum_regions  beta_hat_win * A_j(win)
    Var_j(X)    = sum_regions  beta_hat_win^2 * H_j(win)   + cross-region terms
                  that vanish in expectation by independence
    Var_j(G)    = sum_all-causals  beta_c^2 H_j(c)          (+ within-region LD terms)

so E[r2_j] and the ratio reduce EXACTLY to per-region integrals plus the finite-m
Jensen corrections of Section 2 of SELFTAG_DERIVATION.md (delta method with exact
moment inputs; expandable to any order with computable remainder).

## Step 2: the per-region integral, exactly

A region carries: N_c causal loci (N_c ~ Poisson with rate = m * region-length /
genome-length -- NOT the single-causal assumption: P(N_c >= 2 | region has one) is
about 0.3 at this design and MUST be carried), tag positions at the known marker
density, the local cross-deme LD field {D_t(x), D_j(x), H(x)}, GWAS noise with
exactly known per-SNP variance, and the probit attenuation factor c(K) (equal
across demes under phenoC's equalized prevalence, hence cancelling in the ratio --
derived, not assumed). The region contributes

    I_j(region) = E[ beta_hat_win * A_j(win) ; selection ]

where the expectation is over the local Gaussian statistic field GIVEN the LD
field, the effect draws, and the noise -- a finite-dimensional integral with every
density known in closed form except the LD-field law (Step 5). The winner-location
density of section 8 EMERGES here as an inner integral (it is not an ansatz), and
the v3-family laws are recovered as truncations: single-causal + point-mass winner
(v3), single-causal + independent-tag winner (v3.1), single-causal + correlated
winner (v3.2). THE FIRST A-PRIORI NEW TERM THE COMPLETE LAW ADDS: multi-causal
regions (N_c >= 2), whose winner tags a MIXTURE of causal channels and whose A_j
carries cross-causal interference -- at this design's causal density roughly a
third of occupied regions, a term of the same order as the residuals the gates
measured, and never indicted by them because every candidate so far shared the
single-causal assumption.

## Step 3: threshold selection across the panel

The chosen threshold maximizes calibration AUC on the selection split over nine
candidates -- an argmax over correlated statistics whose distribution is exactly
computable from the per-region integrals (the panel's composition at each
threshold is a deterministic function of the region statistics). This induces the
panel-level winner's curse on the anchor r2_t; it is a finite exact integral, not
noise.

## Step 4: the drift-heterogeneity envelope

Steps 1-3 condition on the frequency field; the outer expectation over mu is the
ascertained-moment layer, computed EXACTLY by the incomplete-Beta conditioning
(fourth_moment_ascertained.json) at the orders the delta expansion requires --
degree 4 today, degree 6 by the same closed hierarchy if the expansion's remainder
bound demands it.

## Step 5: the single approximation, and its bound

Everything above is exact. The one object without a closed-form law is the joint
distribution of the local LD field across demes (its moments are exact -- the DD /
Dz / pi2 tables -- but its full law is not Gaussian). The complete law closes it by
maximum entropy given the exact first and second moments (Gaussian LD field), and
the error of ANY selection functional under this closure is bounded by the field's
computable higher cumulants: the excess kurtosis of D is available from the same
moment hierarchy (pi2 block), so the closure ships WITH its bound rather than with
a hope. If the bound is too loose at the design's selection strength, the
correction term (Edgeworth in the exact third/fourth cumulants) is itself
computable from tables already in hand.

## What this changes about procedure

The gates stop being a search heuristic and return to their proper role: one
assembled law, evaluated once with its internal error budget (delta-method
remainder + Gaussian-closure cumulant bound + winner-density evaluation error),
pinned, and judged. The a-priori term list above -- multi-causal regions, panel
winner's curse on the anchor, the closure bound -- is fixed BEFORE any further
grading, so no future verdict can be absorbed into an unstated term.

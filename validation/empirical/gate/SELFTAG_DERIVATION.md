# The self-tagging transport law, and why everything now reduces to the ascertained spectrum

Working record of the gate-repair derivation, frozen 2026-08-11 after the v2 refutation.
Every numerical claim below cites its artifact; nothing is fitted.

## 1. The clump index is usually the causal variant itself

The causal panel is drawn from the genotyped common pool (`stream_geno.py`, MAF >= 0.01),
so each causal variant is among its own region's GWAS candidates with r^2 = 1 against
itself, strictly above every tag. The clump index (most significant SNP in the window)
is therefore the causal itself unless sampling noise reorders the top of the list.
Corroboration: the gate sidecars select ~8 index SNPs at p <= 1e-6 from 150 causals --
the surviving channels are the strongest causals, self-tagged. A self-tagged channel has
NO tag-causal LD decay: score channel beta_hat * g_causal correlates perfectly with its
own liability component in every deme.

Consequence: the panel law is a mixture -- self-tagged channels (no lambda decay) plus
tagged channels (lambda decay) -- and any pure-lambda panel model under-predicts
transport. This is the measured content of the first gate verdict (all residuals
positive, `gate_verdict_seeds101-108.json`) and of the v2 refutation (tighter panels
grade better; the tightest possible channel is the self-channel).

## 2. Where distance decay comes from if not LD: per-locus drift heterogeneity

For a self-tagged panel of k loci against an m-locus liability (k ~ 8, m = 150), with
per-locus target/train heterozygosity ratios h_l = H_{j,l}/H_{t,l}:

    r2_t = sum_k beta^2 H_t / sum_m beta^2 H_t        (panel share, train)
    r2_j = sum_k beta^2 H_j / sum_m beta^2 H_j        (panel share, target)
    ratio = (sum_k H_j / sum_k H_t) * (sum_m H_t / sum_m H_j)

The expectation of this ratio over the per-locus drift ensemble is 1 plus
finite-panel Jensen terms of order (CV^2_t - rho_tj)/k - (CV^2_j - rho_tj)/m, where
CV^2 and rho are the fourth-moment scatter statistics E[(pq)^2]/E[pq]^2 - 1 and
E[p_t q_t p_j q_j]/(E[p_t q_t] E[p_j q_j]) - 1. Distance enters through rho_tj
decaying with divergence: distant pairs decorrelate per-locus, inflating the Jensen
penalty asymmetrically. This is a drift-heterogeneity law, not a linkage law.

## 3. The fourth moments exist exactly, and they prove ascertainment-dominance

The one-locus degree-4 moment hierarchy over all 36 demes is closed under
drift + migration + mutation (91,389 sparse coordinates; `fourth_moments.py`,
`fourth_moment_tables.json`). Self-check: its degree-2 marginals reproduce the
validated H table up to a 0.2197% offset that is UNIFORM across demes to 2.9e-5 --
the offset is the reference's own theta-linearization (the moments.LD H law is the
O(theta) truncation; the diffusion with u = theta/2 is exact), so every ratio the
transport law consumes is unaffected.

Measured on the unascertained tables: CV^2 = 209-259, rho = 126-197 (pairs (0,1),
(0,7), (0,35)); the resulting k=8 corrections are +7.7 to +16.6 -- nonsensical for a
ratio near one. The raw spectrum is U-shaped at theta = 0.001; near-fixed loci
dominate the unconditioned moments. The causal panel, however, is ascertained at
pooled MAF >= 0.01 and then again by GWAS significance. CONCLUSION, now quantitative:
the self-panel transport law is controlled entirely by the ASCERTAINED fourth
moments, and no unconditioned moment table can grade it.

## 4. Convergence

Three independent lines now terminate at the same object:
  - the variance law's residual (AUC bar, first gate) needs ascertained SECOND moments;
  - the panel law (this note) needs ascertained FOURTH moments;
  - the cohort-size segregation law (the killed-dual-chain work) already computes
    sample-count-conditioned spectra exactly.
The single remaining mathematical object of the exact-law program is the ascertained
joint-frequency spectrum across demes -- the sample-count/Bernstein machinery already
landed in the corpus, evaluated at the pipeline's ascertainment events and taken to
fourth order. When that evaluation exists, predictor v3 is: self-tagged mixture with
ascertained-moment Jensen terms plus the tagged remainder, and it meets the gate on
seeds that have never been generated.

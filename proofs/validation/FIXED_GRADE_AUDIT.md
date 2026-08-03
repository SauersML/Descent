# Trust audit: fixed-grade incompleteness

The open declarations
`FiniteMixtureExperiment.fixedGrade_incompleteness` and
`MeanAbsoluteEffectCertificateProblem.fixedGrade_incompleteness_biology` are not yet suitable
for a trustable rate theorem.

## Why the current existential statement is underconstrained

`FiniteMixtureExperiment n observationCount` lets the witness choose all of the following after
seeing `n`, the grade, and the desired lower bound:

- the target;
- every moment probe;
- every parameter's observation law; and
- the observation-space size.

Consequently a witness can make every parameter emit the same one-point law, set one moment probe
equal to almost all of the target, and tune the remaining target residual to the reciprocal of
`fixedGradeGapScale K n`. The resulting total variation is genuinely zero and Lean can prove the
displayed ratio, but the construction contains no statistical information and encodes the desired
rate into the experiment. It is kernel-valid and statement-valid while failing mathematical
intent. It must not replace the visible `sorry`.

The symbol `n` is also a parameter-catalogue size in this interface, not a number of independent
observations. No theorem about a sample-size rate follows from increasing it.

## The biological specialization has the same gap

`MeanAbsoluteEffectCertificateProblem` derives a bounded carrier from each chosen catalogue, but
the radius is not fixed across `n`. Its observation kernel remains an arbitrary catalogue-indexed
finite PMF. Thus neither scale normalization nor a growing-data experiment connects the stated
polynomial ratio to GWAS observations.

## Required repair

A rate theorem needs a concrete sequence of experiments before the lower bound is stated:

1. a fixed normalized architecture class;
2. a specified one-observation kernel and its `n`-fold product, or another explicit growing-data
   construction;
3. target and moment probes fixed independently of the desired bound;
4. explicit moment-matched priors in that model; and
5. a proved total-variation comparison of their prior-predictive laws.

Until those objects exist, the two admissions are intentionally visible. A constant observation
kernel, a target residual chosen from the desired conclusion, a conditional crossing premise, or
an imported moment-comparison theorem would make the files green without proving the biological
claim.

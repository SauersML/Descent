# Results review: six differential families

Analyst reading of six family result files that had been produced but never read.
Nothing here was re-run; every number below is quoted from a results file, and
where a number is derived from those (a deviation in standard errors, a ratio)
the derivation is stated.

## Provenance of this review

- Results produced by job 14762161 (`run_rest.sh`) in the clone
  `/projects/standard/hsiehph/sauer354/gnomon-sweeps-20260803`, at repository
  revision **bb0d1f6a140914c6afedc6da714780aa9757526d**, on node cn1030,
  2026-08-03.
- All eight `fam_*.py` simulators relevant to this batch are **byte-identical**
  between bb0d1f6 and `origin/main` (compared by blob hash), so these results
  describe current main's simulators despite the run clone being pre-reorg.
- Files were copied to a scratch directory and verified to match the byte sizes
  on the cluster. All six parse as valid JSON; none is a stub or partial write.
- scikit-allel 1.3.13, as recorded by the cross-check file itself.

**Provenance gap, uniform across all six files.** Not one results file records
the repository revision it was produced from, or whether the tree was clean.
The revision above is known only because it was read out of the job's own log
and the clone, not because any file carries it. Two files record a seed
(`fst_allel_crosscheck`, `ibd_recurrence`); the other four record none at top
level. This should be fixed at the writer, not patched by hand afterwards.

---

## 1. fst_allel_crosscheck — VERDICT: the corpus AGREES with scikit-allel, and the four red cells are a stale premise in the simulator, not a defect in the corpus

This is the headline file, and its own summary fields are misleading. It reports
`cells_red: 4` and `c3_docstring_claim_supported: false`. Read literally that
looks like the independent implementation caught something. It did not.

**The independent comparison passes.** Across eight parameter cells at 5000
diploids per deme, `Calibrator.Conventions.hudsonFst` against scikit-allel's
`hudson_fst`, worst relative error **7.1e-3**, best 1.4e-4, zero red cells. The
relative errors are not evidence of drift between implementations: the absolute
deviations are 3.5e-5 to 5.4e-4 and are uncorrelated with the size of F_ST, so
the two largest relative errors are simply the two smallest F_ST values
(0.00685 and 0.00625). This is a fixed sampling-noise floor, not a bias.

The comparison spans F_ST from 0.00625 to 0.780, a factor of 125, so a constant
recalibration factor could not have produced this agreement.

**The conversion theorem holds numerically.** `Conventions.hudsonFst_eq_of_neiGst`
(Hudson = 2G/(1+G)) reproduces `hudsonFst` over 42 exact points with worst
relative error **5.6e-14** — floating point, with no sampling and no foreign
library in the loop.

**The positive control fired.** K2 at the point the corpus docstring names,
p1=0.2, p2=0.6: Nei G_ST 0.16667 against the docstring's 0.1667, Hudson 0.28571
against the docstring's 0.2857, gap +71.4286% against the docstring's 71.4%.
The estimators do disagree, so the agreements above are not vacuous.

**Why the four red C3 cells are not a finding against the corpus.** The
simulator's C3 tests the claim that Nei G_ST and Hudson "agree only when
p1 = p2 OR pbar = 1/2", attributing that disjunction to the docstring of
`Calibrator.Conventions.neiGst`. **The corpus does not say that, and did not say
it at bb0d1f6 either.** `Conventions.neiGst` says the opposite, in bold: they
agree when p₁ = p₂ and NOT when p̄ = 1/2, "the second is a tempting disjunct and
it is false in both readings", together with an instruction not to reintroduce
the exception.

So C3 measured the corpus's corrected claim and flagged it red because the
simulator's `ok` criterion still encodes the old, withdrawn claim. The measured
ratios confirm the corpus **exactly**:

| p1, p2 (p̄ = 1/2) | Hudson/Nei measured | corpus docstring states |
|---|---|---|
| 0.525, 0.475 | 1.9950124688278879 | 1.995 |
| 0.6, 0.4 | 1.9230769230769205 | 1.923 |
| 0.7, 0.3 | 1.7241379310344835 | 1.724 |
| 0.9, 0.1 | 1.2195121951219512 | 1.220 |

The last row is the point certified by the theorem
`Conventions.neiGst_ne_hudsonFst_at_mean_half`, which proves
`neiGst (9/10) (1/10) ≠ hudsonFst (9/10) (1/10)` and whose docstring gives the
ratio as 50/41. 50/41 = 1.2195121951219512, matching the simulated value to full
double precision. An independent implementation has now confirmed a Lean theorem
pointwise.

**Action required — in the simulator, not the corpus.** The module docstring of
`fam_fst_allel_crosscheck.py` misquotes `Conventions.neiGst`, and its C3 `ok`
criterion (`abs(f - g) <= 1e-9`) is inverted relative to the claim the corpus
actually makes. As written, this family reports RED whenever the corpus is
RIGHT. Until it is fixed, `cells_red` and `c3_docstring_claim_supported` from
this file must not be quoted as corpus status. I have not changed the file.

**Instrument weakness.** C1 compares a *sample* estimate from scikit-allel
against the corpus's *parametric* value, so the residual is sampling error of
the sample, not a difference between two implementations of the same formula.
The file carries no standard error on that residual anywhere; agreement is
adjudicated against a hard-coded 2% tolerance. Note for contrast that the two
foreign estimators agree with each other to 1e-8 on the same sample, four orders
of magnitude tighter than either agrees with the parametric value — which is the
signature of sampling noise and confirms the reading above. Adding a replicate
axis and a standard error would make C1 falsifiable rather than tolerance-bound.

The K1 controls are the strongest quantitative content in the file and pass
convincingly: at p1 = p2 the corrected estimators return essentially zero
(Hudson -6.5e-4 to +2.7e-4) while the uncorrected Nei body returns a strictly
positive number matching its predicted 1/(2·2n−1) bias to within 1.3–6.2%
(observed/predicted 0.938 to 1.013 across four cells).

---

## 2. coalescent — VERDICT: ran clean, both controls pass, and it delivers its intended finding: two corpus bodies are missing arguments, now quantified at up to 70 standard errors

`READ_THE_TEST: true`; controls `split_t0_zero` and `island_monotone_in_m` both
true. The large deviations below are **the designed result, not an unnoticed
bug** — the simulator's own method is to vary something a definition does not
take as an argument and measure whether the prediction notices.

**Split family.** `coalFst` takes a single Ne, so it predicts the same F_ST
whether the daughter populations are equal or 16-fold apart. Holding everything
else fixed and varying only that:

| t | daughters | measured | coalFst predicts | deviation |
|---|---|---|---|---|
| 500 | equal | 0.19295 | 0.20000 | 0.64 SE |
| 500 | 16x apart | 0.31177 | 0.20000 | **12.0 SE** |
| 2000 | equal | 0.48744 | 0.50000 | 0.83 SE |
| 2000 | 16x apart | 0.52247 | 0.50000 | **5.3 SE** |
| 8000 | equal | 0.79473 | 0.80000 | 1.09 SE |
| 8000 | 16x apart | 0.68564 | 0.80000 | **70.5 SE** |

Deviations in SE are computed here from the file's own `fst_sem`. Every
equal-daughter cell agrees within about 1 SE; every unequal-daughter cell
disagrees, worst 70 SE. `coalFst` is valid for symmetric splits and not
otherwise.

**Island family.** Eight definitions across five files compute 1/(1 + 4·Ne·m)
and none takes the deme count. Measured F_ST falls steeply in d at fixed (Ne, m)
— at m = 0.002, from 0.09787 at d = 2 to 0.00952 at d = 20, a factor of ten that
the prediction cannot represent. Against `islandModelFst` the deviations reach
**75 SE**; against the finite-deme theory 1/(1 + 4·Ne·m·(d/(d−1))²) they still
reach **69 SE**, so the measurements are not explained by that correction
either. Only the d = 2, m = 0.01 cell agrees with either (1.8 SE and 1.5 SE).

**Instrument weakness, and it matters here.** The two registered controls are
weak — F_ST = 0 at t = 0, and monotonicity in m — and neither can fail in a way
that would catch a wrong prediction. Consequently `READ_THE_TEST: true` is
compatible with a 70 SE disagreement sitting in the same file, and anything that
reads only the top-level flag will record this family as confirming `coalFst`.
The missing-argument finding is present only in the per-cell numbers. The
summary field should carry it.

---

## 3. ld_decay — VERDICT: FAILS its own null control, which invalidates its bottleneck arm; and its equilibrium arm contradicts a corpus body by a factor of 2.4

This family exited nonzero. That is a **measurement outcome, not a crash**:
stderr was empty, the results file was written, and stdout carries the full
report. It must be landed as a result with a failed control, not filed as a
broken family.

**The failing check.** `C3_null_bottleneck_pass: false`. In the null arm, where
no bottleneck is imposed and the ratio must be 1.0 by construction, the measured
ratios are **1.1647, 1.0458, 1.1536, 1.7428**. The instrument reports a
bottleneck signal of up to +74% when there is no bottleneck. The bottleneck arm
of this family (`C_bottleneck`, measured ratios 2.95 to 15.50 against corpus
predictions 5.10 to 8.39) therefore cannot be interpreted: its null is not
centred on the null. No conclusion about bottleneck LD should be drawn from this
run.

**Contradiction with the corpus, stated with both numbers.** In `B_sigma_d2` the
measured σ_d² is closer to Ohta–Kimura than to the corpus's
`driftLDEquilibrium` at **all four** rho values, and at low rho the corpus is
badly high:

| rho | measured | corpus driftLDEquilibrium | Ohta–Kimura | corpus/measured |
|---|---|---|---|---|
| 0.5 | 0.281146 | 0.666389 | 0.365217 | **2.37** |
| 2 | 0.227580 | 0.332221 | 0.230769 | 1.46 |
| 10 | 0.081964 | 0.088844 | 0.079365 | 1.08 |
| 40 | 0.025332 | 0.022032 | 0.023343 | 0.87 |

The corpus body is 2.4x high at rho = 0.5 and converges only as rho grows. The
file's own `closer_to` field reads "Ohta-Kimura" in all four rows. **This is
reported without error bars** — `B_sigma_d2` carries no standard error — so I
cannot state the discrepancy in standard errors, and given the failing C3
control the whole run warrants repeating before the corpus is amended. Flagging
it rather than acting on it.

**What does work.** The two analytic-limit controls pass tightly:
`C1_drift_only` 0.9974548963376884 against expected 0.9975, and `C2_recomb_only`
0.98 against expected 0.98. The Hill–Robertson retention arm agrees across six
cells with relative errors 2.5e-5 to 3.2e-3. So the simulator's core decay
machinery is sound; the defect is in the bottleneck construction and possibly in
the equilibrium arm.

---

## 4. sfs — VERDICT: clean, and the best-controlled family of the six; its positive control fires hard

`READ_THE_TEST: true`, all four registered controls pass:
`spectrum_shape_theta_over_i`, `spectrum_scale_watterson`,
`singleton_proportion`, `positive_control_growth_rejected`.

**The positive control fires, decisively.** Against a growth model the neutral
spectrum is rejected at **58.8 SE** on spectrum shape (worst bin 13, max
absolute deviation 0.401) and **56.6 SE** on singleton proportion (0.6832
measured against 0.2819 neutral, SEM 0.0071), with `rejected: true`. This family
has demonstrated it can detect a wrong demography, so its passes are
informative rather than automatic — the property the other five should be
measured against.

This is also the only family of the six whose result file records replicate
counts and standard errors throughout its cells, which is what makes the
above quotable in SE at all. No contradiction with any corpus claim found.

---

## 5. ibd_recurrence — VERDICT: zero red cells, but the headline hides the substance: the corpus body is exact under one reading of its rate parameter and wrong by up to 95% under the other, and it is missing the deme-count argument

`cells_red: 0`, seed 20260802, 300000 replicates, and this is the one file whose
`cells_red` should not be read as "nothing to see". Its top-level
`migration_reading_max_relerr` is **0.948** — a 95% relative error reported
alongside zero red cells, because the family documents the gap rather than
asserting agreement.

**Under the mutation reading, the corpus is exact.** `ibdRecurrenceFixedPoint`
matches the closed form to relative errors of **1.3e-15 to 1.2e-14** across the
rate grid, and the Monte Carlo agrees with both (e.g. at scaled rate 1.0, exact
0.49906113146981274 against MC 0.49901 with SE 0.00091, 0.06 SE). The file
records `mutation_reading_exact: true`.

**Under the migration reading, it is not.** `MIGRATION_relerr_vs_corpus_d2`
grows monotonically with the scaled rate: 0.201, 0.336, 0.505, 0.679, to a
maximum of 0.948. The same corpus body read as a migration recurrence is wrong
by nearly a factor of two at the top of the grid. The reading of the `rate`
argument is doing all the work, and only one reading is supported.

**Missing argument, same shape as the coalescent family.** Cell J4 is labelled
"MISSING ARGUMENT: F_ST depends on d, the body does not". At fixed rate the
exact F_ST is 0.6658 at d = 2, 0.7818 at d = 10, 0.7976 at d = 100 — a 20%
spread across deme counts that the corpus body, taking no d, returns a single
number for.

**Controls.** J1 (rate = 0) and J2 (Ne = 1e9, drift off) both pass and pin the
drift and flow arms separately, which is what makes the J3 gap attributable to
the reading of `rate`. These are limit controls rather than a planted-defect
positive control; nothing in this family fires on an injected error, so unlike
`sfs` it has not demonstrated detection power.

---

## 6. ascertainment — VERDICT: clean, positive control fires, and it reproduces its stored result BIT-FOR-BIT

`READ_THE_TEST: true`, all six registered controls pass: `sampling_variance`,
`ld_attenuation`, `threshold_null_two_sided`, `power`,
`positive_control_mismatch_axis`, `winners_curse_exact_matches_simulated_gwas`.

**The positive control fires.** On the frequency-mismatch axis, 3 matched cells
agree and **all 6** mismatched cells are caught at tolerance 0.1
(`mismatched_caught: 6` of `mismatched_cells: 6`). The family can detect the
defect it is built to detect.

**Comparison against the stored result — exact.** This is the only family of the
six with a prior stored result. The fresh run was compared against
`proofs/validation/empirical/differential/cluster/fam_ascertainment_results.json`
at `origin/main` by full recursive walk of the JSON:

- structural differences: **0** (no key, length, or type differences)
- worst absolute numeric difference: **0.0**
- worst relative numeric difference: **0.0**
- both files 23627 bytes, identical SHA

Bit-for-bit reproducible — stronger than the 1.8e-14 and 3.3e-13 agreements
recorded for other families, which are floating-point reduction order. Note that
the stored result at the *run clone's* revision bb0d1f6 was a different, smaller
file (15984 bytes); the fresh run reproduces `origin/main`'s current version
exactly, so the modification flag seen in that clone reflects the clone being
behind, not a changed measurement.

---

## Cross-cutting

**Two families report a missing argument in corpus bodies, independently.**
`coalescent` finds `coalFst` blind to daughter-size asymmetry (70 SE) and the
eight island bodies blind to deme count (75 SE); `ibd_recurrence` finds
`ibdRecurrenceFixedPoint` blind to deme count (20% spread). These agree on the
shape of the defect and are the most substantial corpus findings in the batch.

**Positive controls: three of six fire.** `sfs` (58.8 SE), `ascertainment` (6 of
6 caught), and `fst_allel_crosscheck` K2 have demonstrated detection power.
`coalescent`, `ld_decay` and `ibd_recurrence` carry only limit or monotonicity
controls, which cannot fire on a planted defect. Their passes are correspondingly
weaker evidence and should not be quoted as confirmations.

**One instrument is failing and one is mislabelled.** `ld_decay` fails its null
control and its bottleneck arm should not be used. `fam_fst_allel_crosscheck.py`
misquotes `Conventions.neiGst` and reports RED when the corpus is right; its
summary fields are unsafe to quote until its C3 criterion is corrected.

**Recommended re-runs**, for the team lead to schedule with cluster-owner; I ran
nothing and am not requesting cluster access:

1. `ld_decay`, after the null-bottleneck construction is repaired — the
   `driftLDEquilibrium` discrepancy cannot be adjudicated until the null is
   centred, and that arm needs standard errors added.
2. `fst_allel_crosscheck`, after its C3 premise and criterion are corrected —
   the measurements are sound and need no re-run for C1/C2/K1/K2, only the
   pass/fail logic and the module docstring need fixing.

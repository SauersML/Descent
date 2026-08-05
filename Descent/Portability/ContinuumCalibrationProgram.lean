/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ContinuumCalibration
import Descent.Spectral.EnsembleChannel
import Descent.Portability.PGSCalibrationTheory

/-!
# Resolving the drifting index: strata, gauge, unqueried populations, and decisions

`Descent.Portability.ContinuumCalibration` fixes one predictor class and answers the first question about
a family of populations whose conditional risk moves along the family: index-wise calibration
energy is aggregate energy plus an irreducible drift defect, the posterior mean attains the
defect, and the two demands are nested rather than opposed.

This module continues from there, and every result below is a finite, exactly stated face of a
step in that program.  Nothing analytic is assumed: no disintegration, no singular-value
asymptotics, no minimax rate over a smoothness class.  Where the continuum statement is a limit,
what is proved here is the identity the limit is taken of.

* **One lemma.**  Weights on a carrier, a partition into cells, a representative per cell: if the
  weighted residual sums to zero inside every cell, the residual is orthogonal to everything the
  cells can see.  Everything below is that fact instantiated -- in the index direction (ancestry
  strata) and in the covariate direction (the reported score's bins).

* **Stratified resolution.**  A recalibration allowed to depend on an ancestry stratum, an
  environment, or a study is a predictor factoring through `stratify : Index → Stratum`.  The
  cell lemma gives the whole geometry: an exact Pythagoras against every competing
  stratum-measurable predictor, the optimality of the stratum-calibrated one, and the exact
  decrement obtained by refining the stratification.  The energy the refinement removes is
  exactly the between-stratum drift it resolves.

* **Nested demands.**  A stratum-calibrated recalibration is automatically calibrated in
  aggregate: its calibration-in-the-large is exactly zero.  Ancestry-specific calibration is
  never bought at the pooled model's expense.

* **Refining the report.**  In the covariate direction the same monotonicity says that a sharper
  reported score exposes weakly more population drift, and conversely.  Sharpness and exposed
  defect are one functional evaluated on two fields.

* **Worst population versus pooled.**  In the squared posterior geometry there is nothing to
  trade.  The applied tension lives in the worst-population norm, whose optimum is the midrange:
  it disagrees with the pooled, aggregate-calibrated report exactly when representation is
  unequal, and the gap does not close with more data.

* **Complementarity, hence co-monotonicity.**  Residual and resolution sum to the drift defect
  of `ContinuumCalibration`.  So resolution cannot be bought without paying the defect down by
  the same amount, and refining strata moves both by exactly one shared quantity.  This is the
  calibration--refinement trade-off as an identity rather than a tension.

* **The gauge obstruction.**  Two conditional fields with the *same* values in the same
  multiplicities, differing only in which index carries which value, have equal drift defect and
  unequal within-stratum residual.  So no functional of the field's law can predict what a
  prescribed stratification recovers: alignment between the stratification and the drift decides
  it, and alignment is not a property of the field alone.

* **Unqueried populations.**  Two conditional fields that agree at every observed index, carry
  the same posterior mean, and have the same index-wise energy against *every* predictor, can
  differ by the full drift width at an unobserved index.  No estimator separates them, so the
  best available error at an unqueried population is the drift radius, and the posterior mean
  attains it.  Extrapolation across a family whose marginals do not move buys exactly nothing.

* **Decisions.**  A drifting risk that straddles a clinical threshold has a strictly positive
  net-benefit cost that no single ancestry-blind action avoids, and the cost is computed in
  closed form in the units of `decisionCurveNetBenefit`.  A drift that stays on one side of
  the threshold costs nothing at all: that is exactly which losses survive the drift.

* **Allocation.**  Stratifying into `k` cells and estimating each from `n_s` samples pays an
  effective stratum count that is at least `k`, with equality exactly at balanced allocation, and
  a two-term budget whose optimum sits where the two terms balance.

The biological wiring is by theorem, not by prose: `stratifiedCalibrationEnergy` is related to
`indexWiseCalibrationEnergy` and `calibrationDriftDefectSq`, the decision results are stated in
the units of `decisionCurveNetBenefit` and agree with `thresholdDecision`, and the aggregate
moment is identified with `calibrationInTheLarge`.
-/

namespace Descent.Portability

open scoped BigOperators

/-! ## The one lemma: cellwise balance is orthogonality to everything the cells can see

Every decomposition in this module is an instance of a single finite fact.  Weights on a carrier,
a partition of the carrier into cells, and a representative value per cell: if the weighted
residual sums to zero inside every cell, then the residual is orthogonal to every function
constant on cells.  Instantiated in the index direction the cells are ancestry strata; in the
covariate direction they are the level sets of the reported score.  The two readings of the
calibration--refinement trade-off below are the same theorem twice.
-/

section CellGeometry

variable {Carrier Cell : Type*} [Fintype Carrier] [Fintype Cell] [DecidableEq Cell]

/-- A per-cell representative is *cell-balanced* when the weighted residual sums to zero inside
every cell.  Stated without dividing by a cell mass, so it is meaningful at empty cells.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite linear condition on a supplied
representative. -/
def IsCellBalanced (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (representative : Cell → ℝ) : Prop :=
  ∀ c, (∑ a, if cell a = c then weight a * (value a - representative c) else 0) = 0

/-- **Cellwise balance is orthogonality.**  The residual of a cell-balanced representative is
orthogonal to every function that is constant on cells.

Assumes: `IsCellBalanced weight value cell representative`. -/
theorem cellBalanced_cross_term_eq_zero (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (representative competitor : Cell → ℝ)
    (hbalanced : IsCellBalanced weight value cell representative) :
    (∑ a, weight a * (value a - representative (cell a)) *
      (representative (cell a) - competitor (cell a))) = 0 := by
  have hfiber : ∀ a : Carrier,
      weight a * (value a - representative (cell a)) *
          (representative (cell a) - competitor (cell a)) =
        ∑ c, (if cell a = c then
          weight a * (value a - representative c) * (representative c - competitor c)
          else 0) := by
    intro a
    simp
  calc
    (∑ a, weight a * (value a - representative (cell a)) *
        (representative (cell a) - competitor (cell a))) =
        ∑ a, ∑ c, (if cell a = c then
          weight a * (value a - representative c) * (representative c - competitor c)
          else 0) := Finset.sum_congr rfl (fun a _ ↦ hfiber a)
    _ = ∑ c, ∑ a, (if cell a = c then
          weight a * (value a - representative c) * (representative c - competitor c)
          else 0) := Finset.sum_comm
    _ = ∑ c, (∑ a, if cell a = c then weight a * (value a - representative c) else 0) *
          (representative c - competitor c) := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          by_cases hcell : cell a = c <;> simp [hcell]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro c _
          rw [hbalanced c]
          ring

/-- The identity partition with unit weights is a concrete, nonempty family of balanced cells:
each representative is the value of the unique carrier in its cell. -/
theorem isCellBalanced_identity {Carrier : Type*} [Fintype Carrier] [DecidableEq Carrier]
    (value : Carrier → ℝ) :
    IsCellBalanced (fun _ ↦ 1) value id value := by
  intro c
  simp [IsCellBalanced]

/-- The weighted mean inside a cell.  At a cell of zero mass the division returns Lean's `0`;
that branch is named and used below rather than excluded, which is what makes the existence
theorem unconditional.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite ratio. -/
noncomputable def cellMean (weight value : Carrier → ℝ) (cell : Carrier → Cell) (c : Cell) : ℝ :=
  (∑ a, if cell a = c then weight a * value a else 0) /
    (∑ a, if cell a = c then weight a else 0)

/-- **The empty-cell branch, named.**  A cell carrying no weight has no mean to report and the
convention returns zero -- not a value any carrier holds.  Consumers reading `cellMean` as "the
typical value in this cell" must check the cell is inhabited; the balance theorem below does not
need to, because a cell of zero mass constrains nothing. -/
theorem cellMean_of_mass_zero (weight value : Carrier → ℝ) (cell : Carrier → Cell) (c : Cell)
    (hmass : (∑ a, if cell a = c then weight a else 0) = 0) :
    cellMean weight value cell c = 0 := by
  unfold cellMean
  rw [hmass, div_zero]

/-- **The optimum always exists.**  For nonnegative weights the cellwise mean is cell-balanced --
with no positivity, nonemptiness, or normalization hypothesis.  Every result about a balanced
representative is therefore a result about a construction that is always available, rather than a
conditional statement waiting for a witness. -/
theorem isCellBalanced_cellMean (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (hweight : ∀ a, 0 ≤ weight a) :
    IsCellBalanced weight value cell (cellMean weight value cell) := by
  intro c
  have hsplit : ∀ r : ℝ,
      (∑ a, if cell a = c then weight a * (value a - r) else 0) =
        (∑ a, if cell a = c then weight a * value a else 0) -
          r * ∑ a, if cell a = c then weight a else 0 := by
    intro r
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    by_cases hcell : cell a = c <;> simp [hcell] <;> ring
  rw [hsplit]
  by_cases hmass : (∑ a, if cell a = c then weight a else 0) = 0
  · have hterm : ∀ a : Carrier, (if cell a = c then weight a else 0) = 0 := by
      refine fun a ↦ (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hmass a (Finset.mem_univ a)
      intro b _
      by_cases hcell : cell b = c <;> simp [hcell, hweight b]
    have hnum : (∑ a, if cell a = c then weight a * value a else 0) = 0 := by
      refine Finset.sum_eq_zero (fun a _ ↦ ?_)
      by_cases hcell : cell a = c
      · have := hterm a
        rw [if_pos hcell] at this ⊢
        rw [this]
        ring
      · rw [if_neg hcell]
    rw [hnum, hmass]
    ring
  · unfold cellMean
    field_simp
    ring

/-- **Cellwise balance implies balance overall.**  Summing the per-cell conditions: a
representative calibrated inside every cell is calibrated in aggregate.  The two demands are
nested, never opposed -- the finite form of the statement that index-wise calibration implies
aggregate calibration.

Assumes: `IsCellBalanced weight value cell representative`. -/
theorem cellBalanced_sum_residual_eq_zero (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (representative : Cell → ℝ)
    (hbalanced : IsCellBalanced weight value cell representative) :
    (∑ a, weight a * (value a - representative (cell a))) = 0 := by
  calc
    (∑ a, weight a * (value a - representative (cell a))) =
        ∑ a, weight a * (value a - representative (cell a)) *
          (representative (cell a) - (representative (cell a) - 1)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = 0 :=
        cellBalanced_cross_term_eq_zero weight value cell representative
          (fun c ↦ representative c - 1) hbalanced

/-- **Pythagoras for cellwise balance.**  Every competing cell-constant representative pays the
balanced one's energy plus the energy of the gap between them.

Assumes: `IsCellBalanced weight value cell representative`. -/
theorem cellBalanced_energy_eq_add_gap (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (representative competitor : Cell → ℝ)
    (hbalanced : IsCellBalanced weight value cell representative) :
    (∑ a, weight a * (value a - competitor (cell a)) ^ 2) =
      (∑ a, weight a * (value a - representative (cell a)) ^ 2) +
        (∑ a, weight a * (representative (cell a) - competitor (cell a)) ^ 2) := by
  have hcross :=
    cellBalanced_cross_term_eq_zero weight value cell representative competitor hbalanced
  have hmiddle :
      (∑ a, 2 * (weight a * (value a - representative (cell a)) *
        (representative (cell a) - competitor (cell a)))) = 0 := by
    rw [← Finset.mul_sum, hcross]
    ring
  calc
    (∑ a, weight a * (value a - competitor (cell a)) ^ 2) =
        ∑ a, (weight a * (value a - representative (cell a)) ^ 2 +
          2 * (weight a * (value a - representative (cell a)) *
            (representative (cell a) - competitor (cell a))) +
          weight a * (representative (cell a) - competitor (cell a)) ^ 2) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = (∑ a, weight a * (value a - representative (cell a)) ^ 2) +
          (∑ a, 2 * (weight a * (value a - representative (cell a)) *
            (representative (cell a) - competitor (cell a)))) +
          (∑ a, weight a * (representative (cell a) - competitor (cell a)) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ a, weight a * (value a - representative (cell a)) ^ 2) +
          (∑ a, weight a * (representative (cell a) - competitor (cell a)) ^ 2) := by
          rw [hmiddle]
          ring

/-- **The balanced representative carries the whole projection.**  Total weighted energy splits
into the balanced residual and the energy of the representative itself.

Assumes: `IsCellBalanced weight value cell representative`. -/
theorem cellBalanced_total_energy_eq (weight value : Carrier → ℝ) (cell : Carrier → Cell)
    (representative : Cell → ℝ)
    (hbalanced : IsCellBalanced weight value cell representative) :
    (∑ a, weight a * value a ^ 2) =
      (∑ a, weight a * (value a - representative (cell a)) ^ 2) +
        (∑ a, weight a * representative (cell a) ^ 2) := by
  have hzero :=
    cellBalanced_energy_eq_add_gap weight value cell representative (fun _ ↦ 0) hbalanced
  simpa using hzero

/-- **What a refinement removes.**  If a coarse partition factors through a finer one, the coarse
representative's energy exceeds the fine one's by exactly the gap the refinement resolves.

Assumes: `IsCellBalanced weight value refine fineRep`. -/
theorem cellBalanced_energy_refine_eq_add_gap
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (weight value : Carrier → ℝ) (coarsen : Carrier → Cell) (refine : Carrier → Fine)
    (link : Fine → Cell) (coarseRep : Cell → ℝ) (fineRep : Fine → ℝ)
    (hlink : ∀ a, coarsen a = link (refine a))
    (hfine : IsCellBalanced weight value refine fineRep) :
    (∑ a, weight a * (value a - coarseRep (coarsen a)) ^ 2) =
      (∑ a, weight a * (value a - fineRep (refine a)) ^ 2) +
        (∑ a, weight a * (fineRep (refine a) - coarseRep (link (refine a))) ^ 2) := by
  have hsame :
      (∑ a, weight a * (value a - coarseRep (coarsen a)) ^ 2) =
        ∑ a, weight a * (value a - coarseRep (link (refine a))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hlink a]
  rw [hsame]
  exact cellBalanced_energy_eq_add_gap weight value refine fineRep
    (fun f ↦ coarseRep (link f)) hfine

/-- **Refinement is a submartingale on the resolved energy.**  For nonnegative weights, the
energy captured by the representative never decreases under refinement of the cells.  This is the
mechanism behind every co-monotonicity statement below: resolution and resolved drift are the
same functional evaluated on different fields, so refining cannot raise one without raising the
other. -/
theorem cellBalanced_representative_energy_le_of_refine
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (weight value : Carrier → ℝ) (coarsen : Carrier → Cell) (refine : Carrier → Fine)
    (link : Fine → Cell) (coarseRep : Cell → ℝ) (fineRep : Fine → ℝ)
    (hlink : ∀ a, coarsen a = link (refine a))
    (hcoarse : IsCellBalanced weight value coarsen coarseRep)
    (hfine : IsCellBalanced weight value refine fineRep)
    (hweight : ∀ a, 0 ≤ weight a) :
    (∑ a, weight a * coarseRep (coarsen a) ^ 2) ≤ ∑ a, weight a * fineRep (refine a) ^ 2 := by
  have hcoarseSplit := cellBalanced_total_energy_eq weight value coarsen coarseRep hcoarse
  have hfineSplit := cellBalanced_total_energy_eq weight value refine fineRep hfine
  have hrefine :=
    cellBalanced_energy_refine_eq_add_gap weight value coarsen refine link coarseRep fineRep
      hlink hfine
  have hgap : 0 ≤ ∑ a, weight a * (fineRep (refine a) - coarseRep (link (refine a))) ^ 2 :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (hweight a) (sq_nonneg _)
  linarith

end CellGeometry

/-- **Half the gap is unavoidable.**  If two candidate values cannot be told apart, then every
number a predictor might report is wrong by at least half the distance between them, against one
of the two.  This is the general form of every indistinguishability bound below: the two-point
drift radius, and the worst-population error of a straddling family. -/
theorem half_gap_le_max_abs_sub (first second report : ℝ) :
    |first - second| / 2 ≤ max |first - report| |second - report| := by
  have htriangle : |first - second| ≤ |first - report| + |report - second| :=
    abs_sub_le first report second
  have hcomm : |report - second| = |second - report| := abs_sub_comm report second
  have hleft : |first - report| ≤ max |first - report| |second - report| := le_max_left _ _
  have hright : |second - report| ≤ max |first - report| |second - report| := le_max_right _ _
  rw [hcomm] at htriangle
  linarith

section StratifiedResolution

variable {Index Covariate Stratum : Type*} [Fintype Index] [Fintype Covariate]
  [Fintype Stratum] [DecidableEq Stratum]

/-- Index-wise calibration energy of a recalibration allowed to depend on the stratum of the
index: an ancestry-specific intercept, a study-specific slope, a per-environment offset.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def stratifiedCalibrationEnergy (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (predictor : Stratum → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t * (conditional t x - predictor (stratify t) x) ^ 2

/-- A stratum-level predictor is *stratum-calibrated* when, inside every stratum and at every
covariate, the posterior-weighted residual sums to zero.  This is calibration of the recalibrated
score within each ancestry group, stated without dividing by a stratum mass -- so it is
meaningful at strata of zero posterior mass, where a stratum mean is not defined.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite linear condition on a supplied
recalibration. -/
def IsStratumCalibrated (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor : Stratum → Covariate → ℝ) : Prop :=
  ∀ x s, (∑ t, if stratify t = s then
    posterior x t * (conditional t x - predictor s x) else 0) = 0

/-- Energy of the gap between two stratum-level recalibrations, in the same posterior geometry.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def stratumGapEnergy (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (stratify : Index → Stratum)
    (predictor other : Stratum → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t * (predictor (stratify t) x - other (stratify t) x) ^ 2

/-- Resolution: how far a stratum-level recalibration moves away from the pooled posterior mean.
This is the sharpness a stratified model buys, measured in the geometry that charges the defect.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def stratumResolutionEnergy (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (predictor : Stratum → Covariate → ℝ) : ℝ :=
  ∑ x, covariateWeight x *
    ∑ t, posterior x t *
      (predictor (stratify t) x - posteriorMean posterior conditional x) ^ 2

/-- **The zero of the gap scale, pinned.**  A recalibration has no gap against itself, whatever
the posterior and the covariate weight: the gap energy measures only disagreement between two
recalibrations, and carries no offset. -/
@[simp] theorem stratumGapEnergy_self_eq_zero (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (stratify : Index → Stratum)
    (predictor : Stratum → Covariate → ℝ) :
    stratumGapEnergy covariateWeight posterior stratify predictor predictor = 0 := by
  simp [stratumGapEnergy]

/-- **The zero of the resolution scale, pinned.**  A recalibration that returns the pooled
posterior mean in every stratum has bought no sharpness -- so resolution is measured from the
pooled predictor, not from zero. -/
@[simp] theorem stratumResolutionEnergy_posteriorMean_eq_zero (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) :
    stratumResolutionEnergy covariateWeight posterior conditional stratify
      (fun _ x ↦ posteriorMean posterior conditional x) = 0 := by
  simp [stratumResolutionEnergy]

/-- **The stratified energy of a stratum-blind predictor is the index-wise energy.**  Taking the
recalibration constant across strata returns `indexWiseCalibrationEnergy` exactly, so the
stratified theory extends the pooled one rather than replacing it. -/
theorem stratifiedCalibrationEnergy_const_eq_indexWiseCalibrationEnergy
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor : Covariate → ℝ) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional stratify
        (fun _ x ↦ predictor x) =
      indexWiseCalibrationEnergy covariateWeight posterior conditional predictor := by
  unfold stratifiedCalibrationEnergy indexWiseCalibrationEnergy
  rfl

/-- **The pooled posterior mean is stratum-calibrated for the trivial stratification.**  This
witnesses `IsStratumCalibrated` on a construction the corpus already owns, and identifies the
zero-resolution end of the stratified scale with `ContinuumCalibration`'s optimum. -/
theorem isStratumCalibrated_posteriorMean_trivial
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    IsStratumCalibrated posterior conditional (fun _ ↦ (default : Unit))
      (fun _ x ↦ posteriorMean posterior conditional x) := by
  intro x s
  have hdrift :
      (∑ t, posterior x t * posteriorDrift posterior conditional t x) = 0 :=
    posteriorDrift_weighted_sum_eq_zero posterior conditional x (hposterior x)
  have hunit : ∀ t : Index, (fun _ ↦ (default : Unit)) t = s := by
    intro _
    cases s
    rfl
  calc
    (∑ t, if (fun _ ↦ (default : Unit)) t = s then
        posterior x t * (conditional t x - posteriorMean posterior conditional x)
      else 0) =
        ∑ t, posterior x t * (conditional t x - posteriorMean posterior conditional x) :=
          Finset.sum_congr rfl (fun t _ ↦ if_pos (hunit t))
    _ = 0 := by simpa [posteriorDrift] using hdrift

/-- **The cross term of a stratum-calibrated recalibration vanishes.**  Within-stratum
calibration is exactly orthogonality to every stratum-measurable direction: this single lemma
carries every decomposition below. -/
theorem stratumCalibrated_cross_term_eq_zero
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (predictor other : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor)
    (x : Covariate) :
    (∑ t, posterior x t * (conditional t x - predictor (stratify t) x) *
      (predictor (stratify t) x - other (stratify t) x)) = 0 :=
  cellBalanced_cross_term_eq_zero (posterior x) (fun t ↦ conditional t x) stratify
    (fun s ↦ predictor s x) (fun s ↦ other s x) (hcalibrated x)

/-- Pointwise stratified Pythagoras at one covariate. -/
theorem stratum_pointwise_pythagoras
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (predictor other : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor)
    (x : Covariate) :
    (∑ t, posterior x t * (conditional t x - other (stratify t) x) ^ 2) =
      (∑ t, posterior x t * (conditional t x - predictor (stratify t) x) ^ 2) +
        (∑ t, posterior x t *
          (predictor (stratify t) x - other (stratify t) x) ^ 2) :=
  cellBalanced_energy_eq_add_gap (posterior x) (fun t ↦ conditional t x) stratify
    (fun s ↦ predictor s x) (fun s ↦ other s x) (hcalibrated x)

/-- **Stratified Pythagoras.**  Against a stratum-calibrated recalibration, every competing
stratum-level recalibration pays its own energy plus the energy of the gap between them.  The
within-stratum residual is therefore irreducible inside the stratified model, exactly as the
drift defect is irreducible inside the pooled one. -/
theorem stratifiedCalibrationEnergy_eq_add_stratumGapEnergy
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor other : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional stratify other =
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify predictor +
        stratumGapEnergy covariateWeight posterior stratify predictor other := by
  unfold stratifiedCalibrationEnergy stratumGapEnergy
  simp_rw [stratum_pointwise_pythagoras posterior conditional stratify predictor other
    hcalibrated, mul_add, Finset.sum_add_distrib]

/-- The gap energy is nonnegative for nonnegative covariate weights and posteriors. -/
theorem stratumGapEnergy_nonneg (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (stratify : Index → Stratum)
    (predictor other : Stratum → Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hposterior : ∀ x t, 0 ≤ posterior x t) :
    0 ≤ stratumGapEnergy covariateWeight posterior stratify predictor other := by
  unfold stratumGapEnergy
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hweight x)
  exact Finset.sum_nonneg fun t _ ↦ mul_nonneg (hposterior x t) (sq_nonneg _)

/-- **The stratum-calibrated recalibration is optimal within its stratification.**  No other
ancestry-specific recalibration, however chosen, has lower index-wise calibration energy. -/
theorem stratifiedCalibrationEnergy_le_of_isStratumCalibrated
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor other : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor)
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hposterior : ∀ x t, 0 ≤ posterior x t) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional stratify predictor ≤
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify other := by
  rw [stratifiedCalibrationEnergy_eq_add_stratumGapEnergy covariateWeight posterior conditional
    stratify predictor other hcalibrated]
  exact le_add_of_nonneg_right
    (stratumGapEnergy_nonneg covariateWeight posterior stratify predictor other hweight hposterior)

/-- **Within-stratum calibration implies pooled calibration.**  At every covariate, the
posterior-weighted residual of a stratum-calibrated recalibration sums to zero across the whole
family.  Ancestry-specific calibration is therefore never bought at the cost of pooled
calibration: the demands are nested. -/
theorem isStratumCalibrated_residual_sum_eq_zero
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (predictor : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor)
    (x : Covariate) :
    (∑ t, posterior x t * (conditional t x - predictor (stratify t) x)) = 0 :=
  cellBalanced_sum_residual_eq_zero (posterior x) (fun t ↦ conditional t x) stratify
    (fun s ↦ predictor s x) (hcalibrated x)

/-- **A stratified recalibration has zero calibration-in-the-large.**  The pooled observed and
predicted means of a stratum-calibrated recalibration agree exactly, in the sign convention of
`PGSCalibrationTheory.calibrationInTheLarge`.  This is the reporting statistic the clinical
literature uses, and stratifying can never move it away from zero. -/
theorem calibrationInTheLarge_eq_zero_of_isStratumCalibrated
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor) :
    calibrationInTheLarge
        (∑ x, covariateWeight x * ∑ t, posterior x t * conditional t x)
        (∑ x, covariateWeight x * ∑ t, posterior x t * predictor (stratify t) x) = 0 := by
  unfold calibrationInTheLarge Descent.Core.difference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro x _
  have hresidual :=
    isStratumCalibrated_residual_sum_eq_zero posterior conditional stratify predictor
      hcalibrated x
  have hsplit :
      (∑ t, posterior x t * (conditional t x - predictor (stratify t) x)) =
        (∑ t, posterior x t * conditional t x) -
          (∑ t, posterior x t * predictor (stratify t) x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hsplit] at hresidual
  have hmeans :
      (∑ t, posterior x t * conditional t x) =
        ∑ t, posterior x t * predictor (stratify t) x := by linarith
  rw [hmeans]
  ring

/-- The posterior-weighted mean conditional risk inside a stratum, at a covariate: the
ancestry-specific recalibration a stratified model actually fits.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is `cellMean` evaluated fibrewise. -/
noncomputable def stratumMean (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum) (s : Stratum)
    (x : Covariate) : ℝ :=
  cellMean (posterior x) (fun t ↦ conditional t x) stratify s

/-- **The stratified optimum always exists.**  For a nonnegative posterior the stratum mean is
stratum-calibrated, with no positivity or normalization hypothesis: strata of zero posterior mass
constrain nothing and are absorbed by the convention.  Every optimality, complementarity and
refinement result above is therefore about a recalibration that can always be written down. -/
theorem isStratumCalibrated_stratumMean (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (hposterior : ∀ x t, 0 ≤ posterior x t) :
    IsStratumCalibrated posterior conditional stratify
      (stratumMean posterior conditional stratify) :=
  fun x ↦ isCellBalanced_cellMean (posterior x) (fun t ↦ conditional t x) stratify (hposterior x)

/-- **The stratum mean is optimal, unconditionally.**  No ancestry-specific recalibration of the
same stratification has lower index-wise calibration energy. -/
theorem stratifiedCalibrationEnergy_stratumMean_le (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum) (other : Stratum → Covariate → ℝ)
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hposterior : ∀ x t, 0 ≤ posterior x t) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional stratify
        (stratumMean posterior conditional stratify) ≤
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify other :=
  stratifiedCalibrationEnergy_le_of_isStratumCalibrated covariateWeight posterior conditional
    stratify (stratumMean posterior conditional stratify) other
    (isStratumCalibrated_stratumMean posterior conditional stratify hposterior) hweight hposterior

/-- **The gauge law in general.**  Relabelling the populations changes nothing, provided the
relabelling preserves the posterior and maps each population to one in the same stratum.  So the
stratified residual is a function of the family up to exactly those relabellings -- and no
further: the witness below permutes populations *across* strata, preserves the posterior and the
law of the conditional field, and changes the residual.  What a prescribed stratification
recovers is therefore not a functional of the drift's law. -/
theorem stratifiedCalibrationEnergy_relabel_invariant
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor : Stratum → Covariate → ℝ) (relabel : Equiv.Perm Index)
    (hposterior : ∀ x t, posterior x (relabel t) = posterior x t)
    (hstratify : ∀ t, stratify (relabel t) = stratify t) :
    stratifiedCalibrationEnergy covariateWeight posterior
        (fun t x ↦ conditional (relabel t) x) stratify predictor =
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify predictor := by
  unfold stratifiedCalibrationEnergy
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  congr 1
  calc
    (∑ t, posterior x t * (conditional (relabel t) x - predictor (stratify t) x) ^ 2) =
        ∑ t, posterior x (relabel t) *
          (conditional (relabel t) x - predictor (stratify (relabel t)) x) ^ 2 := by
          refine Finset.sum_congr rfl (fun t _ ↦ ?_)
          rw [hposterior x t, hstratify t]
    _ = ∑ t, posterior x t * (conditional t x - predictor (stratify t) x) ^ 2 :=
        Equiv.sum_comp relabel
          (fun u ↦ posterior x u * (conditional u x - predictor (stratify u) x) ^ 2)

/-- **Any two populations put a floor under the defect.**  For an arbitrary finite family, the
pooled drift defect at a covariate is at least the product of any two populations' posterior
weights times the square of their risk gap.  This is the usable numeric form of the obstruction:
two ancestries that are both plausible at a covariate and disagree about risk there force a
calibration defect no recalibration can remove, and the bound needs neither a two-group reduction
nor a balanced posterior. -/
theorem posteriorPairwiseDriftEnergy_ge_pair
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ) (x : Covariate)
    (s t : Index) (hst : s ≠ t) (hnonneg : ∀ u, 0 ≤ posterior x u) :
    posterior x s * posterior x t * (conditional s x - conditional t x) ^ 2 ≤
      posteriorPairwiseDriftEnergy posterior conditional x := by
  classical
  have hrownonneg : ∀ r : Index,
      0 ≤ posterior x r * ∑ u, posterior x u * (conditional r x - conditional u x) ^ 2 :=
    fun r ↦ mul_nonneg (hnonneg r)
      (Finset.sum_nonneg fun u _ ↦ mul_nonneg (hnonneg u) (sq_nonneg _))
  have hrow : ∀ a b : Index,
      posterior x a * (posterior x b * (conditional a x - conditional b x) ^ 2) ≤
        posterior x a * ∑ u, posterior x u * (conditional a x - conditional u x) ^ 2 := by
    intro a b
    refine mul_le_mul_of_nonneg_left ?_ (hnonneg a)
    exact Finset.single_le_sum
      (f := fun u ↦ posterior x u * (conditional a x - conditional u x) ^ 2)
      (fun u _ ↦ mul_nonneg (hnonneg u) (sq_nonneg _)) (Finset.mem_univ b)
  have hpair :
      (posterior x s * ∑ u, posterior x u * (conditional s x - conditional u x) ^ 2) +
          (posterior x t * ∑ u, posterior x u * (conditional t x - conditional u x) ^ 2) ≤
        ∑ r, posterior x r * ∑ u, posterior x u * (conditional r x - conditional u x) ^ 2 := by
    have hsum : (∑ r ∈ ({s, t} : Finset Index),
        posterior x r * ∑ u, posterior x u * (conditional r x - conditional u x) ^ 2) =
          (posterior x s * ∑ u, posterior x u * (conditional s x - conditional u x) ^ 2) +
            (posterior x t * ∑ u, posterior x u * (conditional t x - conditional u x) ^ 2) :=
      Finset.sum_pair hst
    calc
      (posterior x s * ∑ u, posterior x u * (conditional s x - conditional u x) ^ 2) +
            (posterior x t * ∑ u, posterior x u * (conditional t x - conditional u x) ^ 2) =
          ∑ r ∈ ({s, t} : Finset Index),
            posterior x r * ∑ u, posterior x u * (conditional r x - conditional u x) ^ 2 :=
        hsum.symm
      _ ≤ ∑ r, posterior x r *
            ∑ u, posterior x u * (conditional r x - conditional u x) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun r _ _ ↦ hrownonneg r)
  have hfirst := hrow s t
  have hsecond := hrow t s
  have hswap : (conditional t x - conditional s x) ^ 2 =
      (conditional s x - conditional t x) ^ 2 := by ring
  rw [hswap] at hsecond
  unfold posteriorPairwiseDriftEnergy
  nlinarith [hfirst, hsecond, hpair]

/-- **Residual and resolution are complementary.**  The drift defect of the pooled theory splits,
exactly, into the within-stratum residual a stratified recalibration cannot remove and the
resolution it buys.  Neither can move without the other moving by the same amount: this is the
calibration--refinement trade-off as an identity. -/
theorem calibrationDriftDefectSq_eq_stratified_add_resolution
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor : Stratum → Covariate → ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    calibrationDriftDefectSq covariateWeight posterior conditional =
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify predictor +
        stratumResolutionEnergy covariateWeight posterior conditional stratify predictor := by
  have hpooled :
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify
          (fun _ x ↦ posteriorMean posterior conditional x) =
        calibrationDriftDefectSq covariateWeight posterior conditional := by
    rw [stratifiedCalibrationEnergy_const_eq_indexWiseCalibrationEnergy]
    exact indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq covariateWeight posterior
      conditional hposterior
  have hsplit :=
    stratifiedCalibrationEnergy_eq_add_stratumGapEnergy covariateWeight posterior conditional
      stratify predictor (fun _ x ↦ posteriorMean posterior conditional x) hcalibrated
  rw [hpooled] at hsplit
  rw [hsplit]
  rfl

/-- **With no strata to separate the populations, the whole drift is irreducible.**  Under the
trivial stratification the best recalibration is the pooled posterior mean and its index-wise
energy is exactly the drift defect of `ContinuumCalibration`.  This is the baseline every
ancestry-specific recalibration is measured against, and the finite form of the statement that
drift invisible to the available labels cannot be removed by any amount of recalibration. -/
theorem stratifiedCalibrationEnergy_trivial_eq_calibrationDriftDefectSq
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional
        (fun _ ↦ (default : Unit)) (fun _ x ↦ posteriorMean posterior conditional x) =
      calibrationDriftDefectSq covariateWeight posterior conditional := by
  rw [stratifiedCalibrationEnergy_const_eq_indexWiseCalibrationEnergy]
  exact indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq covariateWeight posterior
    conditional hposterior

/-- **A first-order error in the recalibration costs only second order in the energy.**  Moving a
stratum-calibrated recalibration by `step` along any stratum-level direction raises the index-wise
calibration energy by exactly `step ^ 2` times that direction's energy: the first-order term is
annihilated by the calibration condition itself.  So a slightly mis-estimated stratification or a
slightly mis-estimated per-stratum offset is second-order harmless, which is why the strata may be
learned from the same data without spoiling the first-order behaviour of the calibration. -/
theorem stratifiedCalibrationEnergy_perturbed_eq
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (stratify : Index → Stratum)
    (predictor direction : Stratum → Covariate → ℝ) (step : ℝ)
    (hcalibrated : IsStratumCalibrated posterior conditional stratify predictor) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional stratify
        (fun s x ↦ predictor s x + step * direction s x) =
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify predictor +
        step ^ 2 *
          ∑ x, covariateWeight x * ∑ t, posterior x t * direction (stratify t) x ^ 2 := by
  have hgap :
      stratumGapEnergy covariateWeight posterior stratify predictor
          (fun s x ↦ predictor s x + step * direction s x) =
        step ^ 2 *
          ∑ x, covariateWeight x * ∑ t, posterior x t * direction (stratify t) x ^ 2 := by
    unfold stratumGapEnergy
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    refine Finset.sum_congr rfl (fun t _ ↦ ?_)
    ring
  rw [stratifiedCalibrationEnergy_eq_add_stratumGapEnergy covariateWeight posterior conditional
    stratify predictor (fun s x ↦ predictor s x + step * direction s x) hcalibrated, hgap]

/-- **The split is available for every family.**  The pooled drift defect equals the stratum
mean's irreducible residual plus the resolution it buys -- stated for the recalibration that
always exists, so this is a decomposition of the defect rather than a conditional identity. -/
theorem calibrationDriftDefectSq_eq_stratumMean_split (covariateWeight : Covariate → ℝ)
    (posterior : Covariate → Index → ℝ) (conditional : Index → Covariate → ℝ)
    (stratify : Index → Stratum)
    (hposterior : ∀ x t, 0 ≤ posterior x t) (hnormalized : ∀ x, ∑ t, posterior x t = 1) :
    calibrationDriftDefectSq covariateWeight posterior conditional =
      stratifiedCalibrationEnergy covariateWeight posterior conditional stratify
          (stratumMean posterior conditional stratify) +
        stratumResolutionEnergy covariateWeight posterior conditional stratify
          (stratumMean posterior conditional stratify) :=
  calibrationDriftDefectSq_eq_stratified_add_resolution covariateWeight posterior conditional
    stratify (stratumMean posterior conditional stratify)
    (isStratumCalibrated_stratumMean posterior conditional stratify hposterior) hnormalized

/-- **What refining a stratification removes is exactly the drift it resolves.**  If a coarse
stratification factors through a finer one, then the coarse optimum's energy is the fine
optimum's energy plus the energy of the gap between them.  Refining ancestry labels, adding a
study indicator, splitting an environment: the gain is a squared norm, never negative and never
larger than the between-stratum disagreement it names. -/
theorem stratifiedCalibrationEnergy_refine_eq_add_stratumGapEnergy
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (coarsen : Index → Stratum) (refine : Index → Fine) (link : Fine → Stratum)
    (coarsePredictor : Stratum → Covariate → ℝ) (finePredictor : Fine → Covariate → ℝ)
    (hlink : ∀ t, coarsen t = link (refine t))
    (hfine : IsStratumCalibrated posterior conditional refine finePredictor) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional coarsen coarsePredictor =
      stratifiedCalibrationEnergy covariateWeight posterior conditional refine finePredictor +
        stratumGapEnergy covariateWeight posterior refine finePredictor
          (fun f x ↦ coarsePredictor (link f) x) := by
  have hsame :
      stratifiedCalibrationEnergy covariateWeight posterior conditional coarsen coarsePredictor =
        stratifiedCalibrationEnergy covariateWeight posterior conditional refine
          (fun f x ↦ coarsePredictor (link f) x) := by
    unfold stratifiedCalibrationEnergy
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [hlink t]
  rw [hsame]
  exact stratifiedCalibrationEnergy_eq_add_stratumGapEnergy covariateWeight posterior conditional
    refine finePredictor (fun f x ↦ coarsePredictor (link f) x) hfine

/-- **Refinement never raises the residual.**  The stratified calibration energy of the finer
optimum is at most that of any coarser recalibration it refines. -/
theorem stratifiedCalibrationEnergy_refine_le
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (coarsen : Index → Stratum) (refine : Index → Fine) (link : Fine → Stratum)
    (coarsePredictor : Stratum → Covariate → ℝ) (finePredictor : Fine → Covariate → ℝ)
    (hlink : ∀ t, coarsen t = link (refine t))
    (hfine : IsStratumCalibrated posterior conditional refine finePredictor)
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hposterior : ∀ x t, 0 ≤ posterior x t) :
    stratifiedCalibrationEnergy covariateWeight posterior conditional refine finePredictor ≤
      stratifiedCalibrationEnergy covariateWeight posterior conditional coarsen
        coarsePredictor := by
  rw [stratifiedCalibrationEnergy_refine_eq_add_stratumGapEnergy covariateWeight posterior
    conditional coarsen refine link coarsePredictor finePredictor hlink hfine]
  exact le_add_of_nonneg_right
    (stratumGapEnergy_nonneg covariateWeight posterior refine finePredictor
      (fun f x ↦ coarsePredictor (link f) x) hweight hposterior)

/-- **Refinement raises resolution by exactly what it removes from the residual.**  The two
optima are related by one shared quantity, so a stratification that sharpens a score by some
amount has reduced its irreducible within-stratum calibration error by that same amount, and a
refinement that buys no sharpness has removed no defect. -/
theorem stratumResolutionEnergy_refine_eq_add_stratumGapEnergy
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ)
    (coarsen : Index → Stratum) (refine : Index → Fine) (link : Fine → Stratum)
    (coarsePredictor : Stratum → Covariate → ℝ) (finePredictor : Fine → Covariate → ℝ)
    (hlink : ∀ t, coarsen t = link (refine t))
    (hcoarse : IsStratumCalibrated posterior conditional coarsen coarsePredictor)
    (hfine : IsStratumCalibrated posterior conditional refine finePredictor)
    (hposterior : ∀ x, ∑ t, posterior x t = 1) :
    stratumResolutionEnergy covariateWeight posterior conditional refine finePredictor =
      stratumResolutionEnergy covariateWeight posterior conditional coarsen coarsePredictor +
        stratumGapEnergy covariateWeight posterior refine finePredictor
          (fun f x ↦ coarsePredictor (link f) x) := by
  have hcoarseSplit :=
    calibrationDriftDefectSq_eq_stratified_add_resolution covariateWeight posterior conditional
      coarsen coarsePredictor hcoarse hposterior
  have hfineSplit :=
    calibrationDriftDefectSq_eq_stratified_add_resolution covariateWeight posterior conditional
      refine finePredictor hfine hposterior
  have hrefine :=
    stratifiedCalibrationEnergy_refine_eq_add_stratumGapEnergy covariateWeight posterior
      conditional coarsen refine link coarsePredictor finePredictor hlink hfine
  linarith

end StratifiedResolution

/-! ## Refining the reported score: sharpness and exposed drift rise together

The other reading of the same lemma.  Here the cells are the level sets of the reported score --
the bins a calibration plot is drawn on -- and the carrier is the covariate.  Refining those bins
is what "reporting a sharper score" means.  Two consequences, both monotone and both instances of
`cellBalanced_representative_energy_le_of_refine`: a finer report resolves weakly more of the
pooled signal (sharpness), and weakly more of every population's drift away from the pooled
conditional (exposed defect).  A predictor cannot become sharper without exposing more of the
drift, which is the calibration--refinement trade-off in the direction the applied literature
reports it.  Nothing here is a rate: the finite statement is that the two move together.
-/

section ReportRefinement

variable {Index Covariate Bin : Type*} [Fintype Index] [Fintype Covariate] [Fintype Bin]
  [DecidableEq Bin]

/-- Sharpness of a reported score at a given bin resolution: the energy of the bin-level profile
of the centred pooled conditional.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def reportResolutionEnergy (covariateWeight : Covariate → ℝ)
    (report : Covariate → Bin) (profile : Bin → ℝ) : ℝ :=
  ∑ x, covariateWeight x * profile (report x) ^ 2

/-- The population drift a reported score exposes: the index-averaged energy of the bin-level
profiles of each population's deviation from the pooled conditional.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def visibleDriftEnergy (indexWeight : Index → ℝ) (covariateWeight : Covariate → ℝ)
    (report : Covariate → Bin) (profile : Index → Bin → ℝ) : ℝ :=
  ∑ t, indexWeight t * ∑ x, covariateWeight x * profile t (report x) ^ 2

/-- **The zero of the sharpness scale, pinned.**  A report whose profile is flat at zero has no
sharpness, whatever the bins and the covariate weights. -/
@[simp] theorem reportResolutionEnergy_zero (covariateWeight : Covariate → ℝ)
    (report : Covariate → Bin) :
    reportResolutionEnergy covariateWeight report (fun _ ↦ 0) = 0 := by
  simp [reportResolutionEnergy]

/-- **The zero of the exposed-drift scale, pinned.**  A report that sees no deviation in any
population exposes no drift. -/
@[simp] theorem visibleDriftEnergy_zero (indexWeight : Index → ℝ)
    (covariateWeight : Covariate → ℝ) (report : Covariate → Bin) :
    visibleDriftEnergy indexWeight covariateWeight report (fun _ _ ↦ 0) = 0 := by
  simp [visibleDriftEnergy]

/-- **A finer report is weakly sharper.** -/
theorem reportResolutionEnergy_refine_le
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (covariateWeight value : Covariate → ℝ)
    (report : Covariate → Bin) (refine : Covariate → Fine) (link : Fine → Bin)
    (coarseProfile : Bin → ℝ) (fineProfile : Fine → ℝ)
    (hlink : ∀ x, report x = link (refine x))
    (hcoarse : IsCellBalanced covariateWeight value report coarseProfile)
    (hfine : IsCellBalanced covariateWeight value refine fineProfile)
    (hweight : ∀ x, 0 ≤ covariateWeight x) :
    reportResolutionEnergy covariateWeight report coarseProfile ≤
      reportResolutionEnergy covariateWeight refine fineProfile :=
  cellBalanced_representative_energy_le_of_refine covariateWeight value report refine link
    coarseProfile fineProfile hlink hcoarse hfine hweight

/-- **A finer report exposes weakly more drift.**  Every population's resolved deviation grows,
so their index-average does. -/
theorem visibleDriftEnergy_refine_le
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (indexWeight : Index → ℝ) (covariateWeight : Covariate → ℝ) (drift : Index → Covariate → ℝ)
    (report : Covariate → Bin) (refine : Covariate → Fine) (link : Fine → Bin)
    (coarseProfile : Index → Bin → ℝ) (fineProfile : Index → Fine → ℝ)
    (hlink : ∀ x, report x = link (refine x))
    (hcoarse : ∀ t, IsCellBalanced covariateWeight (drift t) report (coarseProfile t))
    (hfine : ∀ t, IsCellBalanced covariateWeight (drift t) refine (fineProfile t))
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hindex : ∀ t, 0 ≤ indexWeight t) :
    visibleDriftEnergy indexWeight covariateWeight report coarseProfile ≤
      visibleDriftEnergy indexWeight covariateWeight refine fineProfile := by
  unfold visibleDriftEnergy
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left
    (cellBalanced_representative_energy_le_of_refine covariateWeight (drift t) report refine link
      (coarseProfile t) (fineProfile t) hlink (hcoarse t) (hfine t) hweight) (hindex t)

/-- **Sharpness and exposed drift are co-monotone.**  Refining the bins of a reported score
weakly increases both.  There is no refinement that buys sharpness while leaving the population
drift as invisible as it was, and none that exposes drift without having bought sharpness
somewhere -- the two are the same functional on two different fields. -/
theorem report_refinement_co_monotone
    {Fine : Type*} [Fintype Fine] [DecidableEq Fine]
    (indexWeight : Index → ℝ) (covariateWeight : Covariate → ℝ)
    (pooled : Covariate → ℝ) (drift : Index → Covariate → ℝ)
    (report : Covariate → Bin) (refine : Covariate → Fine) (link : Fine → Bin)
    (coarsePooledProfile : Bin → ℝ) (finePooledProfile : Fine → ℝ)
    (coarseProfile : Index → Bin → ℝ) (fineProfile : Index → Fine → ℝ)
    (hlink : ∀ x, report x = link (refine x))
    (hcoarsePooled : IsCellBalanced covariateWeight pooled report coarsePooledProfile)
    (hfinePooled : IsCellBalanced covariateWeight pooled refine finePooledProfile)
    (hcoarse : ∀ t, IsCellBalanced covariateWeight (drift t) report (coarseProfile t))
    (hfine : ∀ t, IsCellBalanced covariateWeight (drift t) refine (fineProfile t))
    (hweight : ∀ x, 0 ≤ covariateWeight x) (hindex : ∀ t, 0 ≤ indexWeight t) :
    reportResolutionEnergy covariateWeight report coarsePooledProfile ≤
        reportResolutionEnergy covariateWeight refine finePooledProfile ∧
      visibleDriftEnergy indexWeight covariateWeight report coarseProfile ≤
        visibleDriftEnergy indexWeight covariateWeight refine fineProfile :=
  ⟨reportResolutionEnergy_refine_le covariateWeight pooled report refine link
      coarsePooledProfile finePooledProfile hlink hcoarsePooled hfinePooled hweight,
    visibleDriftEnergy_refine_le indexWeight covariateWeight drift report refine link
      coarseProfile fineProfile hlink hcoarse hfine hweight hindex⟩

end ReportRefinement

/-! ## Worst population versus pooled: the tension is in the norm, not in the demands

In the squared, posterior-weighted geometry there is nothing to trade -- that is the content of
the complementarity above.  The tension the applied literature reports, between a pooled model
and its worst group, lives in a different norm: the worst-population error.  Its minimiser is the
midrange of the population risks, while pooled calibration forces the posterior mean, and those
two agree only under equal representation.  So the pooled-versus-worst-group gap is a statement
about the choice of norm across populations, not about calibration being in conflict with itself.
-/

section WorstIndex

/-- Worst-population calibration error of a single reported risk, across two populations.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite maximum. -/
noncomputable def worstIndexError (upper lower report : ℝ) : ℝ :=
  max |upper - report| |lower - report|

/-- **Every report pays at least half the width.** -/
theorem worstIndexError_ge_half_width (upper lower report : ℝ) :
    (upper - lower) / 2 ≤ worstIndexError upper lower report := by
  have hleft : |upper - report| ≤ worstIndexError upper lower report := le_max_left _ _
  have hright : |lower - report| ≤ worstIndexError upper lower report := le_max_right _ _
  have h1 : upper - report ≤ |upper - report| := le_abs_self _
  have h2 : -(lower - report) ≤ |lower - report| := by
    rcases abs_cases (lower - report) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> linarith
  linarith

/-- **And the midrange pays exactly half the width.**  The worst-population optimum is the
midpoint of the two population risks, whatever their posterior masses. -/
theorem worstIndexError_midrange (upper lower : ℝ) (hwidth : lower ≤ upper) :
    worstIndexError upper lower ((upper + lower) / 2) = (upper - lower) / 2 := by
  have hhalf : (0 : ℝ) ≤ (upper - lower) / 2 := by linarith
  unfold worstIndexError
  rw [show upper - (upper + lower) / 2 = (upper - lower) / 2 by ring,
    show lower - (upper + lower) / 2 = -((upper - lower) / 2) by ring, abs_neg,
    abs_of_nonneg hhalf, max_self]

/-- **Unequal representation splits the two objectives.**  The pooled, aggregate-calibrated report
-- the posterior mean of the two population risks -- is strictly worse than the midrange in
worst-population error whenever the two populations are not equally represented and their risks
differ.  The pooled-versus-worst-group gap is therefore exactly a representation asymmetry, and it
does not vanish with more data. -/
theorem worstIndexError_posteriorMean_gt_half_width (q upper lower : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hbalance : q ≠ 1 / 2) (hwidth : lower < upper) :
    (upper - lower) / 2 <
      worstIndexError upper lower (q * upper + (1 - q) * lower) := by
  have hpos : 0 < upper - lower := by linarith
  have hupper : upper - (q * upper + (1 - q) * lower) = (1 - q) * (upper - lower) := by ring
  have hlower : lower - (q * upper + (1 - q) * lower) = -(q * (upper - lower)) := by ring
  unfold worstIndexError
  rw [hupper, hlower, abs_neg, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ (1 - q) * (upper - lower)),
    abs_of_nonneg (by nlinarith : (0:ℝ) ≤ q * (upper - lower))]
  rcases lt_or_gt_of_ne hbalance with hlt | hgt
  · have hbig : (upper - lower) / 2 < (1 - q) * (upper - lower) := by nlinarith
    exact lt_of_lt_of_le hbig (le_max_left _ _)
  · have hbig : (upper - lower) / 2 < q * (upper - lower) := by nlinarith
    exact lt_of_lt_of_le hbig (le_max_right _ _)

end WorstIndex

/-! ## The gauge obstruction: the law of the drift does not decide what strata recover

The index labels are not observable; only the family is.  So a quantity that changes when the
labels are permuted, holding the family fixed, is not a property of the biology.  The witness
below is the smallest one: four populations, two strata, and two conditional fields taking the
same two values in the same multiplicities.  They have equal pooled drift defect and unequal
within-stratum residual, which settles the question negatively -- what a prescribed
stratification recovers is decided by its alignment with the drift, and alignment is not a
functional of the drift's law.
-/

section GaugeWitness

/-- Four populations indexed by a stratum bit and a within-stratum bit. -/
abbrev GaugeIndex : Type := Bool × Bool

/-- The stratification: the first bit.  Two strata of two populations each. -/
def gaugeStratify (t : GaugeIndex) : Bool := t.1

/-- Uniform posterior over the four populations at every covariate.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite weight. -/
noncomputable def gaugePosterior (_x : Unit) (_t : GaugeIndex) : ℝ := 1 / 4

/-- Conditional risk that varies *between* strata: constant inside each stratum.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite field. -/
noncomputable def gaugeAlignedConditional (t : GaugeIndex) (_x : Unit) : ℝ :=
  if t.1 then 1 else 0

/-- Conditional risk that varies *within* strata: the same four values, relabelled.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite field. -/
noncomputable def gaugeCrossedConditional (t : GaugeIndex) (_x : Unit) : ℝ :=
  if t.2 then 1 else 0

/-- The uniform posterior is normalized. -/
theorem gaugePosterior_sum_eq_one (x : Unit) : ∑ t, gaugePosterior x t = 1 := by
  norm_num [gaugePosterior, Fintype.sum_prod_type]

/-- The aligned field's posterior mean is one half. -/
theorem posteriorMean_gaugeAligned :
    posteriorMean gaugePosterior gaugeAlignedConditional () = 1 / 2 := by
  norm_num [posteriorMean, gaugePosterior, gaugeAlignedConditional, Fintype.sum_prod_type]

/-- The relabelled field has the same posterior mean. -/
theorem posteriorMean_gaugeCrossed :
    posteriorMean gaugePosterior gaugeCrossedConditional () = 1 / 2 := by
  norm_num [posteriorMean, gaugePosterior, gaugeCrossedConditional, Fintype.sum_prod_type]

/-- The two fields have the same pooled drift defect: one quarter. -/
theorem calibrationDriftDefectSq_gaugeAligned :
    calibrationDriftDefectSq (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
      gaugeAlignedConditional = 1 / 4 := by
  norm_num [calibrationDriftDefectSq, posteriorDrift, posteriorMean, gaugePosterior,
    gaugeAlignedConditional, Fintype.sum_prod_type]

/-- The relabelled field has the identical pooled drift defect. -/
theorem calibrationDriftDefectSq_gaugeCrossed :
    calibrationDriftDefectSq (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
      gaugeCrossedConditional = 1 / 4 := by
  norm_num [calibrationDriftDefectSq, posteriorDrift, posteriorMean, gaugePosterior,
    gaugeCrossedConditional, Fintype.sum_prod_type]

/-- The stratum-level recalibration that reads off the aligned field's stratum value.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite recalibration. -/
noncomputable def gaugeAlignedPredictor (s : Bool) (_x : Unit) : ℝ :=
  Spectral.binarySecondAnnotation s

/-- The stratum-level recalibration for the relabelled field: both strata get one half.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite recalibration. -/
noncomputable def gaugeCrossedPredictor (_s : Bool) (x : Unit) : ℝ :=
  balancedBinaryWeight x

/-- The aligned predictor is exactly the indicator of the persistent stratum. -/
@[simp] theorem gaugeAlignedPredictor_apply (s : Bool) (x : Unit) :
    gaugeAlignedPredictor s x = if s then 1 else 0 := by
  cases s <;> norm_num [gaugeAlignedPredictor, Spectral.binarySecondAnnotation]

/-- The crossed predictor is the pooled one-half report in every stratum. -/
@[simp] theorem gaugeCrossedPredictor_apply (s : Bool) (x : Unit) :
    gaugeCrossedPredictor s x = 1 / 2 := by
  norm_num [gaugeCrossedPredictor, balancedBinaryWeight]

/-- The aligned recalibration is stratum-calibrated for the aligned field. -/
theorem isStratumCalibrated_gaugeAligned :
    IsStratumCalibrated gaugePosterior gaugeAlignedConditional gaugeStratify
      gaugeAlignedPredictor := by
  intro x s
  cases s <;>
    norm_num [gaugePosterior, gaugeAlignedConditional, gaugeStratify, gaugeAlignedPredictor,
      Spectral.binarySecondAnnotation, Fintype.sum_prod_type]

/-- The one-half recalibration is stratum-calibrated for the relabelled field. -/
theorem isStratumCalibrated_gaugeCrossed :
    IsStratumCalibrated gaugePosterior gaugeCrossedConditional gaugeStratify
      gaugeCrossedPredictor := by
  intro x s
  cases s <;>
    norm_num [gaugePosterior, gaugeCrossedConditional, gaugeStratify, gaugeCrossedPredictor,
      balancedBinaryWeight, Fintype.sum_prod_type]

/-- Stratifying the aligned field removes its entire drift defect. -/
theorem stratifiedCalibrationEnergy_gaugeAligned_eq_zero :
    stratifiedCalibrationEnergy (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
      gaugeAlignedConditional gaugeStratify gaugeAlignedPredictor = 0 := by
  norm_num [stratifiedCalibrationEnergy, gaugePosterior, gaugeAlignedConditional, gaugeStratify,
    gaugeAlignedPredictor, Spectral.binarySecondAnnotation, Fintype.sum_prod_type]

/-- Stratifying the relabelled field removes none of it. -/
theorem stratifiedCalibrationEnergy_gaugeCrossed_eq_quarter :
    stratifiedCalibrationEnergy (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
      gaugeCrossedConditional gaugeStratify gaugeCrossedPredictor = 1 / 4 := by
  norm_num [stratifiedCalibrationEnergy, gaugePosterior, gaugeCrossedConditional, gaugeStratify,
    gaugeCrossedPredictor, balancedBinaryWeight, Fintype.sum_prod_type]

/-- **The gauge obstruction.**  Two conditional fields with the same posterior, the same posterior
mean, and the same pooled drift defect leave *different* residuals under the same stratification:
one is fully resolved, the other not at all.  Therefore no functional of the drift's law predicts
what a prescribed stratification recovers.  The consequence for practice is that reporting the
size of a portability gap says nothing about whether stratifying by ancestry will close it; only
the alignment between the strata and the drift decides that, and it must be measured. -/
theorem gauge_residual_not_determined_by_defect :
    calibrationDriftDefectSq (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior gaugeAlignedConditional =
        calibrationDriftDefectSq (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
          gaugeCrossedConditional ∧
      stratifiedCalibrationEnergy (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
          gaugeAlignedConditional gaugeStratify gaugeAlignedPredictor ≠
        stratifiedCalibrationEnergy (fun _ : Unit ↦ (1 : ℝ)) gaugePosterior
          gaugeCrossedConditional gaugeStratify gaugeCrossedPredictor := by
  constructor
  · rw [calibrationDriftDefectSq_gaugeAligned, calibrationDriftDefectSq_gaugeCrossed]
  · rw [stratifiedCalibrationEnergy_gaugeAligned_eq_zero,
      stratifiedCalibrationEnergy_gaugeCrossed_eq_quarter]
    norm_num

end GaugeWitness

/-! ## Unqueried populations: the drift radius is the whole answer

The construction is the two-point one.  Two populations carry the same covariate distribution --
this is the pure posterior-drift regime, where the index has no observable signature -- and two
candidate conditional fields assign the same pair of risks to them in opposite orders.  Every
posterior-weighted functional of the two is identical, so no amount of data from elsewhere
separates them; yet at either population they differ by the full drift width.
-/

section UnqueriedIndex

/-- One of two conditional risks that differ from a common centre by the drift radius.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a two-point field with a named centre and
radius. -/
noncomputable def swappedConditional (centre radius : ℝ) (t : Bool) (_x : Unit) : ℝ :=
  if t then centre + radius else centre - radius

/-- The same two risks, assigned to the two populations in the opposite order.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the relabelling of `swappedConditional`. -/
noncomputable def swappedConditionalMirror (centre radius : ℝ) (t : Bool) (_x : Unit) : ℝ :=
  if t then centre - radius else centre + radius

/-- Balanced posterior over the two populations.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite weight. -/
noncomputable def balancedPosterior (x : Unit) (t : Bool) : ℝ := gaugeCrossedPredictor t x

/-- The balanced posterior is normalized. -/
theorem balancedPosterior_sum_eq_one (x : Unit) : ∑ t, balancedPosterior x t = 1 := by
  norm_num [balancedPosterior, gaugeCrossedPredictor, balancedBinaryWeight]

/-- Both candidate fields have the same posterior mean, namely the centre. -/
theorem posteriorMean_swappedConditional (centre radius : ℝ) :
    posteriorMean balancedPosterior (swappedConditional centre radius) () = centre ∧
      posteriorMean balancedPosterior (swappedConditionalMirror centre radius) () = centre := by
  constructor <;>
    · norm_num [posteriorMean, balancedPosterior, gaugeCrossedPredictor, balancedBinaryWeight,
        swappedConditional, swappedConditionalMirror] <;> ring

/-- **The two candidate fields are indistinguishable by any calibration measurement.**  For every
predictor whatsoever, they have identical index-wise calibration energy -- so no calibration
statistic, at any covariate, against any weight, can tell them apart. -/
theorem indexWiseCalibrationEnergy_swappedConditional_eq (centre radius : ℝ)
    (covariateWeight : Unit → ℝ) (predictor : Unit → ℝ) :
    indexWiseCalibrationEnergy covariateWeight balancedPosterior
        (swappedConditional centre radius) predictor =
      indexWiseCalibrationEnergy covariateWeight balancedPosterior
        (swappedConditionalMirror centre radius) predictor := by
  unfold indexWiseCalibrationEnergy
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  congr 1
  simp [balancedPosterior, gaugeCrossedPredictor, balancedBinaryWeight, swappedConditional,
    swappedConditionalMirror] <;> ring

/-- **No predictor beats the drift radius at an unqueried population.**  At either population, and
for every value a predictor might report there, one of the two indistinguishable fields is wrong
by at least the drift radius.  Since the fields agree on every observable, this is a bound no
design and no sample size improves. -/
theorem unqueried_error_ge_radius (centre radius v : ℝ) (hradius : 0 ≤ radius) (t : Bool) :
    radius ≤ max |swappedConditional centre radius t () - v|
      |swappedConditionalMirror centre radius t () - v| := by
  have hkey : ∀ A B : ℝ, |A - B| = 2 * radius → radius ≤ max |A - v| |B - v| := by
    intro A B hgap
    have hhalf := half_gap_le_max_abs_sub A B v
    rw [hgap] at hhalf
    linarith
  have hgap : (0 : ℝ) ≤ 2 * radius := by linarith
  cases t
  · refine hkey _ _ ?_
    have hdiff : swappedConditional centre radius false () -
        swappedConditionalMirror centre radius false () = -(2 * radius) := by
      norm_num [swappedConditional, swappedConditionalMirror] <;> ring
    rw [hdiff, abs_neg, abs_of_nonneg hgap]
  · refine hkey _ _ ?_
    have hdiff : swappedConditional centre radius true () -
        swappedConditionalMirror centre radius true () = 2 * radius := by
      norm_num [swappedConditional, swappedConditionalMirror] <;> ring
    rw [hdiff, abs_of_nonneg hgap]

/-- **And the pooled mean attains it.**  Reporting the posterior mean at an unqueried population
is wrong by exactly the drift radius against both candidates, which with the previous theorem
makes the drift radius the exact price of an unobserved population under pure posterior drift.
Extrapolating along an index whose marginals do not move returns nothing beyond the pooled
answer. -/
theorem unqueried_error_posteriorMean_eq_radius (centre radius : ℝ) (hradius : 0 ≤ radius)
    (t : Bool) :
    max |swappedConditional centre radius t () - centre|
      |swappedConditionalMirror centre radius t () - centre| = radius := by
  have hplus : centre + radius - centre = radius := by ring
  have hminus : centre - radius - centre = -radius := by ring
  cases t
  · show max |centre - radius - centre| |centre + radius - centre| = radius
    rw [hplus, hminus, abs_neg, abs_of_nonneg hradius, max_self]
  · show max |centre + radius - centre| |centre - radius - centre| = radius
    rw [hplus, hminus, abs_neg, abs_of_nonneg hradius, max_self]

end UnqueriedIndex

/-! ## Decisions: which losses survive the drift, in net-benefit units

`ContinuumCalibration` shows that a threshold crossing leaves no single correct action.  What is
proved here is the price, in the units the clinical literature already uses: the net benefit of
`decisionCurveNetBenefit`.  A drift that crosses the threshold costs a strictly positive,
closed-form amount whatever single action is taken; a drift that stays on one side costs zero.
That dichotomy is the survival criterion for decision losses: a loss survives a drifting
conditional exactly when its threshold is outside the drift's range.
-/

section DecisionSurvival

/-- Net benefit, per person, of treating someone whose true risk is `risk`, at threshold
`cutoff` -- the decision-curve quantity with one person, `risk` expected true positives and
`1 - risk` expected false positives.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is `decisionCurveNetBenefit` at a one-person
count vector. -/
noncomputable def treatNetBenefit (cutoff risk : ℝ) : ℝ :=
  decisionCurveNetBenefit risk (1 - risk) 1 cutoff

/-- **Net benefit of treating is the threshold excess, rescaled.**  It is positive exactly when
the risk exceeds the threshold, which is why the threshold rule is the optimal decision. -/
theorem treatNetBenefit_eq (cutoff risk : ℝ) (hcutoff : cutoff ≠ 1) :
    treatNetBenefit cutoff risk = (risk - cutoff) / (1 - cutoff) := by
  unfold treatNetBenefit
  rw [decisionCurveNetBenefit_eq_formula]
  have hne : (1 : ℝ) - cutoff ≠ 0 := sub_ne_zero.mpr (Ne.symm hcutoff)
  field_simp
  ring

/-- **The unit threshold is a junk branch, named.**  At `cutoff = 1` the odds weight `t / (1 - t)`
divides by zero, Lean returns `0` for it, and `treatNetBenefit` reports the raw risk as the
benefit of treating -- so a threshold of certainty comes out looking maximally favourable to
treatment rather than maximally hostile to it.  Every consumer must require `cutoff ≠ 1`. -/
theorem treatNetBenefit_at_unit_cutoff_is_junk (risk : ℝ) :
    treatNetBenefit 1 risk = risk := by
  unfold treatNetBenefit
  rw [decisionCurveNetBenefit_eq_formula]
  norm_num

/-- Regret, in net-benefit units, of taking action `treat` at a known risk: the benefit forgone
against the better of the two available actions.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite difference. -/
noncomputable def decisionRegret (cutoff risk : ℝ) (treat : Bool) : ℝ :=
  max (treatNetBenefit cutoff risk) 0 - (if treat then treatNetBenefit cutoff risk else 0)

/-- **The threshold rule is the regret-free decision.**  Acting on `thresholdDecision` at a known
risk gives zero regret, at every threshold below certainty.  This ties the qualitative rule of
`ContinuumCalibration` to the net-benefit scale of `PGSCalibrationTheory`. -/
theorem decisionRegret_thresholdDecision_eq_zero (cutoff risk : ℝ) (hcutoff : cutoff < 1) :
    decisionRegret cutoff risk (thresholdDecision cutoff risk) = 0 := by
  have hne : cutoff ≠ 1 := ne_of_lt hcutoff
  have hpos : (0 : ℝ) < 1 - cutoff := by linarith
  unfold decisionRegret thresholdDecision
  by_cases hcross : cutoff ≤ risk
  · have hbenefit : 0 ≤ treatNetBenefit cutoff risk := by
      rw [treatNetBenefit_eq cutoff risk hne]
      exact div_nonneg (by linarith) (le_of_lt hpos)
    simp [hcross, max_eq_left hbenefit]
  · have hbenefit : treatNetBenefit cutoff risk ≤ 0 := by
      rw [treatNetBenefit_eq cutoff risk hne]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp hcross]) (le_of_lt hpos)
    simp [hcross, max_eq_right hbenefit]

/-- Posterior-average decision regret across a drifting family of populations at one covariate.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite weighted sum. -/
noncomputable def driftDecisionRegret {Index : Type*} [Fintype Index]
    (posterior : Index → ℝ) (conditional : Index → ℝ) (cutoff : ℝ) (treat : Bool) : ℝ :=
  ∑ t, posterior t * decisionRegret cutoff (conditional t) treat

/-- **A drift that stays on one side of the threshold costs nothing.**  If every population's
risk is at or above the cutoff, treating everyone is regret-free across the whole family: the
decision loss at that threshold survives the drift intact. -/
theorem driftDecisionRegret_eq_zero_of_no_crossing {Index : Type*} [Fintype Index]
    (posterior : Index → ℝ) (conditional : Index → ℝ) (cutoff : ℝ) (hcutoff : cutoff < 1)
    (hside : ∀ t, cutoff ≤ conditional t) :
    driftDecisionRegret posterior conditional cutoff true = 0 := by
  unfold driftDecisionRegret
  apply Finset.sum_eq_zero
  intro t _
  have hdecision : thresholdDecision cutoff (conditional t) = true := by
    simp [thresholdDecision, hside t]
  have := decisionRegret_thresholdDecision_eq_zero cutoff (conditional t) hcutoff
  rw [hdecision] at this
  rw [this]
  ring

/-- **A drift that crosses the threshold costs a strictly positive amount, whatever is done.**
With two populations straddling the cutoff and both posteriorly plausible, treating everyone pays
the low-risk population's excess and treating nobody pays the high-risk population's, each in
closed form and each strictly positive.  No ancestry-blind action escapes: this is the exact
price, in net benefit, of a conditional that drifts across a clinical decision boundary, and the
criterion for which decision losses survive such a drift. -/
theorem driftDecisionRegret_pos_of_crossing (q lower upper cutoff : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hcutoff : cutoff < 1)
    (hlower : lower < cutoff) (hupper : cutoff < upper) :
    0 < driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
        (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ()) cutoff
        true ∧
      0 < driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
        (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ()) cutoff
        false := by
  have hne : cutoff ≠ 1 := ne_of_lt hcutoff
  have hpos : (0 : ℝ) < 1 - cutoff := by linarith
  have hupperBenefit : treatNetBenefit cutoff upper = (upper - cutoff) / (1 - cutoff) :=
    treatNetBenefit_eq cutoff upper hne
  have hlowerBenefit : treatNetBenefit cutoff lower = (lower - cutoff) / (1 - cutoff) :=
    treatNetBenefit_eq cutoff lower hne
  have hupperPos : 0 < treatNetBenefit cutoff upper := by
    rw [hupperBenefit]
    exact div_pos (by linarith) hpos
  have hlowerNeg : treatNetBenefit cutoff lower < 0 := by
    rw [hlowerBenefit]
    exact div_neg_of_neg_of_pos (by linarith) hpos
  constructor
  · have hvalue :
        driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
            (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ())
            cutoff true =
          (1 - q) * (0 - treatNetBenefit cutoff lower) := by
      simp [driftDecisionRegret, decisionRegret, twoIndexPosterior, twoIndexConditional,
        max_eq_left (le_of_lt hupperPos), max_eq_right (le_of_lt hlowerNeg)]
    rw [hvalue]
    exact mul_pos (by linarith) (by linarith)
  · have hvalue :
        driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
            (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ())
            cutoff false =
          q * treatNetBenefit cutoff upper := by
      simp [driftDecisionRegret, decisionRegret, twoIndexPosterior, twoIndexConditional,
        max_eq_left (le_of_lt hupperPos), max_eq_right (le_of_lt hlowerNeg)]
    rw [hvalue]
    exact mul_pos hq₀ hupperPos

/-- The per-population regret of treating: zero above the threshold, the shortfall below it. -/
theorem decisionRegret_true_eq (cutoff risk : ℝ) (hcutoff : cutoff < 1) :
    decisionRegret cutoff risk true = max 0 ((cutoff - risk) / (1 - cutoff)) := by
  have hne : cutoff ≠ 1 := ne_of_lt hcutoff
  have hpos : (0 : ℝ) < 1 - cutoff := by linarith
  have hunfold : decisionRegret cutoff risk true =
      max (treatNetBenefit cutoff risk) 0 - treatNetBenefit cutoff risk := by
    unfold decisionRegret
    norm_num
  rw [hunfold, treatNetBenefit_eq cutoff risk hne]
  rcases le_total risk cutoff with hside | hside
  · have hneg : (risk - cutoff) / (1 - cutoff) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
    have hnonneg : 0 ≤ (cutoff - risk) / (1 - cutoff) :=
      div_nonneg (by linarith) (le_of_lt hpos)
    rw [max_eq_right hneg, max_eq_right hnonneg]
    ring
  · have hnonneg : 0 ≤ (risk - cutoff) / (1 - cutoff) :=
      div_nonneg (by linarith) (le_of_lt hpos)
    have hneg : (cutoff - risk) / (1 - cutoff) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hpos)
    rw [max_eq_left hnonneg, max_eq_left hneg]
    ring

/-- The per-population regret of not treating: zero below the threshold, the excess above it. -/
theorem decisionRegret_false_eq (cutoff risk : ℝ) (hcutoff : cutoff < 1) :
    decisionRegret cutoff risk false = max 0 ((risk - cutoff) / (1 - cutoff)) := by
  have hne : cutoff ≠ 1 := ne_of_lt hcutoff
  have hunfold : decisionRegret cutoff risk false = max (treatNetBenefit cutoff risk) 0 := by
    unfold decisionRegret
    norm_num
  rw [hunfold, treatNetBenefit_eq cutoff risk hne, max_comm]

/-- Regret is never negative: no action beats the better of the two available ones. -/
theorem decisionRegret_nonneg (cutoff risk : ℝ) (hcutoff : cutoff < 1) (treat : Bool) :
    0 ≤ decisionRegret cutoff risk treat := by
  cases treat
  · rw [decisionRegret_false_eq cutoff risk hcutoff]
    exact le_max_left _ _
  · rw [decisionRegret_true_eq cutoff risk hcutoff]
    exact le_max_left _ _

/-- **Any family straddling the threshold pays, whatever is done.**  For an arbitrary finite
family of populations -- no two-population reduction, no balanced posterior, no bound on the
number of ancestries -- if one positively weighted population sits strictly below the clinical
cutoff and another sits strictly above it, then every ancestry-blind action carries strictly
positive expected net-benefit regret.  What decides the price is the drift range against the
threshold, never the number of groups. -/
theorem driftDecisionRegret_pos_of_straddling {Index : Type*} [Fintype Index]
    (posterior : Index → ℝ) (conditional : Index → ℝ) (cutoff : ℝ) (hcutoff : cutoff < 1)
    (hposterior : ∀ t, 0 ≤ posterior t)
    (low high : Index) (hlowWeight : 0 < posterior low) (hhighWeight : 0 < posterior high)
    (hlow : conditional low < cutoff) (hhigh : cutoff < conditional high) (treat : Bool) :
    0 < driftDecisionRegret posterior conditional cutoff treat := by
  have hpos : (0 : ℝ) < 1 - cutoff := by linarith
  unfold driftDecisionRegret
  refine Finset.sum_pos' (fun t _ ↦ mul_nonneg (hposterior t)
    (decisionRegret_nonneg cutoff (conditional t) hcutoff treat)) ?_
  cases treat
  · refine ⟨high, Finset.mem_univ high, ?_⟩
    rw [decisionRegret_false_eq cutoff (conditional high) hcutoff,
      max_eq_right (div_nonneg (by linarith) (le_of_lt hpos))]
    exact mul_pos hhighWeight (div_pos (by linarith) hpos)
  · refine ⟨low, Finset.mem_univ low, ?_⟩
    rw [decisionRegret_true_eq cutoff (conditional low) hcutoff,
      max_eq_right (div_nonneg (by linarith) (le_of_lt hpos))]
    exact mul_pos hlowWeight (div_pos (by linarith) hpos)

/-- **A drift that stays below the threshold costs nothing either.**  If every population's risk
is at or below the cutoff, treating nobody is regret-free across the whole family. -/
theorem driftDecisionRegret_eq_zero_of_below {Index : Type*} [Fintype Index]
    (posterior : Index → ℝ) (conditional : Index → ℝ) (cutoff : ℝ) (hcutoff : cutoff < 1)
    (hside : ∀ t, conditional t ≤ cutoff) :
    driftDecisionRegret posterior conditional cutoff false = 0 := by
  have hne : cutoff ≠ 1 := ne_of_lt hcutoff
  have hpos : (0 : ℝ) < 1 - cutoff := by linarith
  unfold driftDecisionRegret
  apply Finset.sum_eq_zero
  intro t _
  have hbenefit : treatNetBenefit cutoff (conditional t) ≤ 0 := by
    rw [treatNetBenefit_eq cutoff (conditional t) hne]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hside t]) (le_of_lt hpos)
  have hregret : decisionRegret cutoff (conditional t) false = 0 := by
    unfold decisionRegret
    simp [max_eq_right hbenefit]
  rw [hregret]
  ring

/-- **The survival criterion, positive half.**  A decision loss whose threshold the drift never
crosses is survived by a single ancestry-blind action, at zero cost: treat everyone if the family
sits above the cutoff, nobody if it sits below. -/
theorem exists_regretFree_action_of_no_crossing {Index : Type*} [Fintype Index]
    (posterior : Index → ℝ) (conditional : Index → ℝ) (cutoff : ℝ) (hcutoff : cutoff < 1)
    (hside : (∀ t, cutoff ≤ conditional t) ∨ (∀ t, conditional t ≤ cutoff)) :
    ∃ action, driftDecisionRegret posterior conditional cutoff action = 0 := by
  rcases hside with habove | hbelow
  · exact ⟨true,
      driftDecisionRegret_eq_zero_of_no_crossing posterior conditional cutoff hcutoff habove⟩
  · exact ⟨false,
      driftDecisionRegret_eq_zero_of_below posterior conditional cutoff hcutoff hbelow⟩

/-- **The survival criterion, negative half.**  Once the drift straddles the threshold, *no*
action is regret-free -- the two closed forms of the crossing theorem, read as a statement about
every available decision.  Together with the previous theorem this is the exact dichotomy: a
decision loss survives a drifting conditional if and only if its threshold lies outside the
drift's range. -/
theorem no_regretFree_action_of_crossing (q lower upper cutoff : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hcutoff : cutoff < 1)
    (hlower : lower < cutoff) (hupper : cutoff < upper) (action : Bool) :
    0 < driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
      (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ()) cutoff
      action := by
  have hboth :=
    driftDecisionRegret_pos_of_crossing q lower upper cutoff hq₀ hq₁ hcutoff hlower hupper
  cases action
  · exact hboth.2
  · exact hboth.1

/-- **The estimation obstruction and the decision obstruction are one event.**  A drift that
straddles a clinical threshold has, at the same time, a strictly positive pooled calibration
defect in the sense of `ContinuumCalibration` and a strictly positive net-benefit regret for
every available action.  The probability-estimation obstruction and the decision-theoretic one
are not two findings about a drifting conditional; they are one crossing, counted in two
currencies. -/
theorem crossing_forces_defect_and_regret (q lower upper cutoff : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hcutoff : cutoff < 1)
    (hlower : lower < cutoff) (hupper : cutoff < upper) :
    0 < (∑ t, twoIndexPosterior (fun _ : Unit ↦ q) () t *
        posteriorDrift (twoIndexPosterior (fun _ : Unit ↦ q))
          (twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower)) t () ^ 2) ∧
      ∀ action : Bool,
        0 < driftDecisionRegret (twoIndexPosterior (fun _ : Unit ↦ q) ())
          (fun t ↦ twoIndexConditional (fun _ : Unit ↦ upper) (fun _ : Unit ↦ lower) t ())
          cutoff action := by
  have hmarginPos : 0 < min (cutoff - lower) (upper - cutoff) :=
    lt_min (by linarith) (by linarith)
  have hlow : (fun _ : Unit ↦ lower) () ≤ cutoff - min (cutoff - lower) (upper - cutoff) := by
    have hmin := min_le_left (cutoff - lower) (upper - cutoff)
    simp only
    linarith
  have hup : cutoff + min (cutoff - lower) (upper - cutoff) ≤ (fun _ : Unit ↦ upper) () := by
    have hmin := min_le_right (cutoff - lower) (upper - cutoff)
    simp only
    linarith
  exact ⟨twoIndex_posteriorDriftEnergy_pos_of_thresholdMargin (fun _ ↦ q) (fun _ ↦ upper)
      (fun _ ↦ lower) () cutoff (min (cutoff - lower) (upper - cutoff)) hq₀ hq₁ hmarginPos
      hlow hup,
    fun action ↦
      no_regretFree_action_of_crossing q lower upper cutoff hq₀ hq₁ hcutoff hlower hupper action⟩

end DecisionSurvival

/-! ## Aggregate calibration is calibration-in-the-large

One line of wiring, because it is the identification that lets the whole module be read in the
vocabulary the clinical calibration literature already uses.
-/

section AggregateIsCITL

variable {Index Covariate : Type*} [Fintype Index] [Fintype Covariate]

/-- **The aggregate calibration moment against the constant weight is calibration-in-the-large.**
The pooled observed mean is the posterior-weighted conditional, so `ContinuumCalibration`'s
aggregate moment at kernel `1` is `PGSCalibrationTheory`'s CITL, with the same sign convention. -/
theorem aggregateCalibrationMoment_one_eq_calibrationInTheLarge
    (covariateWeight : Covariate → ℝ) (posterior : Covariate → Index → ℝ)
    (conditional : Index → Covariate → ℝ) (predictor : Covariate → ℝ) :
    aggregateCalibrationMoment covariateWeight posterior conditional predictor (fun _ ↦ 1) =
      calibrationInTheLarge
        (∑ x, covariateWeight x * posteriorMean posterior conditional x)
        (∑ x, covariateWeight x * predictor x) := by
  unfold aggregateCalibrationMoment calibrationInTheLarge Descent.Core.difference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

end AggregateIsCITL

/-! ## Allocation: what stratifying costs, and where the budget balances

Two elementary facts, stated where the stratified theory needs them.  Refining into `k` strata
buys the between-stratum drift of the first section and pays an estimation cost per stratum; the
first fact says that unequal sampling inflates the number of strata one is effectively paying
for, and the second locates the optimum of the resulting two-term budget.
-/

section Allocation

variable {Stratum : Type*} [Fintype Stratum]

/-- The effective number of strata paid for under an allocation `n`: the stratum count inflated
by the harmonic penalty of unequal sampling.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite ratio. -/
noncomputable def effectiveStratumCount (n : Stratum → ℝ) : ℝ :=
  (∑ s, n s) * (∑ s, 1 / n s) / (Fintype.card Stratum : ℝ)

/-- **An empty stratification is a junk branch, named.**  With no strata the divisor is zero, and
Lean's convention returns `0` -- an allocation over nothing reports the most favourable possible
effective count rather than an undefined one.  Consumers must require a nonempty stratification. -/
theorem effectiveStratumCount_empty_is_junk (n : Empty → ℝ) :
    effectiveStratumCount n = 0 := by
  simp [effectiveStratumCount]

/-- **An unsampled stratum is a junk branch, named.**  At `n s = 0` the reciprocal is `0` by
Lean's convention, so a stratum with no data contributes nothing to the effective count instead of
making it infinite: the penalty for abandoning a stratum entirely is silently waived.  Read with `effectiveStratumCount_ge_card`, which is why that theorem requires a positive allocation. -/
theorem effectiveStratumCount_unsampled_stratum_contributes_zero :
    (1 : ℝ) / (0 : ℝ) = 0 := by
  norm_num

/-- Cauchy--Schwarz in the form needed below, proved by expanding a single square: the harmonic
inequality between an allocation and its reciprocals. -/
theorem card_sq_le_sum_mul_sum_inv (n : Stratum → ℝ) (hpos : ∀ s, 0 < n s) :
    ((Fintype.card Stratum : ℝ)) ^ 2 ≤ (∑ s, n s) * (∑ s, 1 / n s) := by
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset Stratum) with hempty | hne
  · have hcard : Fintype.card Stratum = 0 := by
      rw [← Finset.card_univ, hempty, Finset.card_empty]
    rw [hcard]
    simp [hempty]
  -- Cauchy-Schwarz at `f s = sqrt (n s)`, `g s = 1 / sqrt (n s)`: the cross term is
  -- identically one, so the left side is the cardinality.  Mathlib proves the
  -- inequality (`Finset.sum_mul_sq_le_sq_mul_sq`); the discriminant argument this
  -- replaced was a second proof of it in disguise.
  have hkey := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Stratum)
    (fun s ↦ Real.sqrt (n s)) (fun s ↦ 1 / Real.sqrt (n s))
  have hsqrt : ∀ s : Stratum, Real.sqrt (n s) ≠ 0 :=
    fun s ↦ ne_of_gt (Real.sqrt_pos.mpr (hpos s))
  -- stated in `⁻¹` form, which is what `simp` normalises `1 / _` to
  have hcross : ∀ s : Stratum, Real.sqrt (n s) * (Real.sqrt (n s))⁻¹ = 1 :=
    fun s ↦ mul_inv_cancel₀ (hsqrt s)
  have hf : ∀ s : Stratum, Real.sqrt (n s) ^ 2 = n s :=
    fun s ↦ Real.sq_sqrt (hpos s).le
  have hg : ∀ s : Stratum, ((Real.sqrt (n s))⁻¹) ^ 2 = (n s)⁻¹ := by
    intro s
    rw [inv_pow, Real.sq_sqrt (hpos s).le]
  simpa [one_div, hcross, hf, hg, Finset.card_univ] using hkey

/-- **Unequal sampling inflates the effective stratum count.**  Whatever the allocation, one pays
for at least as many strata as one has declared. -/
theorem effectiveStratumCount_ge_card (n : Stratum → ℝ) (hpos : ∀ s, 0 < n s)
    (hcard : 0 < Fintype.card Stratum) :
    (Fintype.card Stratum : ℝ) ≤ effectiveStratumCount n := by
  have hcardpos : (0 : ℝ) < (Fintype.card Stratum : ℝ) := by exact_mod_cast hcard
  have hne : (Fintype.card Stratum : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hgap : 0 ≤ ((∑ s, n s) * ∑ s, 1 / n s) - (Fintype.card Stratum : ℝ) ^ 2 := by
    linarith [card_sq_le_sum_mul_sum_inv n hpos]
  have hsplit :
      ((∑ s, n s) * ∑ s, 1 / n s) / (Fintype.card Stratum : ℝ) -
          (Fintype.card Stratum : ℝ) =
        (((∑ s, n s) * ∑ s, 1 / n s) - (Fintype.card Stratum : ℝ) ^ 2) /
          (Fintype.card Stratum : ℝ) := by
    field_simp [hne]
  have hnonneg :
      0 ≤ ((∑ s, n s) * ∑ s, 1 / n s) / (Fintype.card Stratum : ℝ) -
        (Fintype.card Stratum : ℝ) := by
    rw [hsplit]
    exact div_nonneg hgap (le_of_lt hcardpos)
  rw [effectiveStratumCount]
  linarith

/-- **Proportional allocation attains it.**  Sampling every stratum equally makes the effective
count exactly the declared count, so the inflation above is entirely a penalty for imbalance and
the optimal design is the balanced one. -/
theorem effectiveStratumCount_balanced_eq_card (c : ℝ) (hc : 0 < c)
    (hcard : 0 < Fintype.card Stratum) :
    effectiveStratumCount (fun _ : Stratum ↦ c) = (Fintype.card Stratum : ℝ) := by
  have hcardpos : (0 : ℝ) < (Fintype.card Stratum : ℝ) := by exact_mod_cast hcard
  have hcne : c ≠ 0 := ne_of_gt hc
  have hne : (Fintype.card Stratum : ℝ) ≠ 0 := ne_of_gt hcardpos
  rw [effectiveStratumCount]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **A worked imbalance.**  Two strata sampled one to three pay for two and two thirds, not two:
a quarter of the second stratum's information is bought and thrown away. -/
theorem effectiveStratumCount_one_three :
    effectiveStratumCount (fun b : Bool ↦ if b then 1 else 3) = 8 / 3 := by
  norm_num [effectiveStratumCount]

/-- **The two-term budget is bounded below by its balance point.**  With unresolved drift falling
as `a / k` in the resolution `k` and estimation cost rising as `b * k`, no resolution does better
than twice the geometric mean of the two coefficients. -/
theorem resolution_budget_ge (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    2 * Real.sqrt (a * b) ≤ a / k + b * k := by
  have hkne : k ≠ 0 := ne_of_gt hk
  have hsqrt : Real.sqrt (a * b) ^ 2 = a * b :=
    Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hprod : b * k * (a / k) = a * b := by
    field_simp
  have hkey : b * k * (a / k + b * k - 2 * Real.sqrt (a * b)) =
      (Real.sqrt (a * b) - b * k) ^ 2 := by
    calc
      b * k * (a / k + b * k - 2 * Real.sqrt (a * b)) =
          b * k * (a / k) + (b * k) ^ 2 - 2 * Real.sqrt (a * b) * (b * k) := by ring
      _ = a * b + (b * k) ^ 2 - 2 * Real.sqrt (a * b) * (b * k) := by rw [hprod]
      _ = Real.sqrt (a * b) ^ 2 + (b * k) ^ 2 - 2 * Real.sqrt (a * b) * (b * k) := by rw [hsqrt]
      _ = (Real.sqrt (a * b) - b * k) ^ 2 := by ring
  have hbk : 0 < b * k := mul_pos hb hk
  nlinarith [hkey, sq_nonneg (Real.sqrt (a * b) - b * k), hbk]

/-- **And the balance point attains it.**  The optimal resolution is where the drift the
stratification still fails to resolve equals the estimation cost of resolving it -- the finite
face of the `k*` the continuum theory quotes, with no smoothness class required to state it. -/
theorem resolution_budget_eq_of_balanced (a b k : ℝ) (hb : 0 < b) (hk : 0 < k)
    (hbalanced : b * k ^ 2 = a) :
    a / k + b * k = 2 * Real.sqrt (a * b) := by
  have hsq : a * b = (b * k) ^ 2 := by
    rw [← hbalanced]
    ring
  have hroot : Real.sqrt (a * b) = b * k := by
    rw [hsq]
    exact Real.sqrt_sq (le_of_lt (mul_pos hb hk))
  have hkne : k ≠ 0 := ne_of_gt hk
  have hdiv : a / k = b * k := by
    rw [← hbalanced]
    field_simp
  rw [hroot, hdiv]
  ring

end Allocation

end Descent.Portability

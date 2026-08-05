/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.PCCorrectability.Threshold

namespace Descent

/-!
# Johnstone--Paul overlap curve

Writing `c = n/M` and `s = λ - 1` for the population spike above the noise
eigenvalue, the asymptotic squared overlap is
`(1 - c/s²) / (1 + c/s)` above `s = √c`, and zero below it.
-/

/-- Squared sample/population eigenvector overlap in the rank-one
spiked-covariance model. -/
noncomputable def samplePCOverlapSq (n M spike : ℝ) : ℝ :=
  if bbpProxyThreshold n M < spike then
    (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike)
  else 0

/-- Below the BBP edge, the modeled eigenvector overlap is exactly zero. -/
theorem samplePCOverlapSq_eq_zero_of_subthreshold
    (n M spike : ℝ) (h : spike ≤ bbpProxyThreshold n M) :
    samplePCOverlapSq n M spike = 0 := by
  simp [samplePCOverlapSq, not_lt.mpr h]

/-- Above the BBP edge, the implementation uses the Johnstone--Paul overlap
formula exactly. -/
theorem samplePCOverlapSq_eq_of_superthreshold
    (n M spike : ℝ) (h : bbpProxyThreshold n M < spike) :
    samplePCOverlapSq n M spike =
      (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike) := by
  simp [samplePCOverlapSq, h]

/-- Above the edge, the Johnstone--Paul squared overlap is strictly between
zero and one for positive sample and marker counts. -/
theorem samplePCOverlapSq_pos_and_lt_one
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    0 < samplePCOverlapSq n M spike ∧ samplePCOverlapSq n M spike < 1 := by
  rw [samplePCOverlapSq_eq_of_superthreshold n M spike h]
  have hc : 0 < n / M := div_pos hn hM
  have ht : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hc
  have hspike : 0 < spike := ht.trans h
  have ht_sq : bbpProxyThreshold n M ^ 2 = n / M := by
    unfold bbpProxyThreshold
    exact Real.sq_sqrt (le_of_lt hc)
  have hc_lt_spike_sq : n / M < spike ^ 2 := by
    rw [← ht_sq]
    exact (sq_lt_sq₀ (le_of_lt ht) (le_of_lt hspike)).2 h
  have hspike_sq : 0 < spike ^ 2 := sq_pos_of_pos hspike
  have hratio_pos : 0 < (n / M) / spike ^ 2 := div_pos hc hspike_sq
  have hratio_lt_one : (n / M) / spike ^ 2 < 1 :=
    (div_lt_one hspike_sq).2 hc_lt_spike_sq
  have hnum : 0 < 1 - (n / M) / spike ^ 2 := sub_pos.mpr hratio_lt_one
  have hlinear_ratio : 0 < (n / M) / spike := div_pos hc hspike
  have hdenom : 0 < 1 + (n / M) / spike := by linarith
  constructor
  · exact div_pos hnum hdenom
  · rw [div_lt_one hdenom]
    linarith

/-- Fraction of the target ancestry axis left after projection onto the modeled
sample PC.

**This models an analyst who residualizes on the relevant sample PC.**  It does not model
the analyst's choice of *how many* PCs to fit.  The shipped calculator
(`map/correctability.rs`, `removed_axis_fraction`) removes the axis only when the class's
`theoretical_pc_rank` is within the requested `fitted_pcs`, and otherwise removes nothing.
Use `fittedResidualAxisFraction` below for the shipped quantity; this definition is the
`pcRank ≤ fittedPCs` special case of it. -/
noncomputable def samplePCResidualAxisFraction (n M spike : ℝ) : ℝ :=
  1 - samplePCOverlapSq n M spike

/-- A sub-threshold sample PC leaves the entire target axis unresolved.  Thus,
in the rank-one model, increasing the requested PC count cannot recover an axis
whose empirical eigenvector has zero overlap with its population direction. -/
theorem subthreshold_sample_pc_leaves_full_axis
    (n M spike : ℝ) (h : spike ≤ bbpProxyThreshold n M) :
    samplePCResidualAxisFraction n M spike = 1 := by
  rw [samplePCResidualAxisFraction, samplePCOverlapSq_eq_zero_of_subthreshold n M spike h]
  ring

/-- Above the edge, the residual fraction is exactly one minus the
Johnstone--Paul overlap used by the executable calculator. -/
theorem superthreshold_sample_pc_residual_fraction
    (n M spike : ℝ) (h : bbpProxyThreshold n M < spike) :
    samplePCResidualAxisFraction n M spike =
      1 - (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike) := by
  rw [samplePCResidualAxisFraction, samplePCOverlapSq_eq_of_superthreshold n M spike h]

/-- A detectable finite spike is only partially recovered: its modeled residual
axis fraction is also strictly between zero and one. -/
theorem samplePCResidualAxisFraction_pos_and_lt_one
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    0 < samplePCResidualAxisFraction n M spike ∧
      samplePCResidualAxisFraction n M spike < 1 := by
  have hoverlap := samplePCOverlapSq_pos_and_lt_one n M spike hn hM h
  unfold samplePCResidualAxisFraction
  constructor <;> linarith

/-- Above the phase transition, the residual fraction has a closed rational
form.  This is algebraically equivalent to one minus the Johnstone--Paul
overlap but is better suited to design calculations and monotonicity proofs. -/
theorem samplePCResidualAxisFraction_eq_rational
    (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h : bbpProxyThreshold n M < spike) :
    samplePCResidualAxisFraction n M spike =
      (n / M) * (spike + 1) / (spike * (spike + n / M)) := by
  rw [superthreshold_sample_pc_residual_fraction n M spike h]
  have hratio : 0 < n / M := div_pos hn hM
  have hedge : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hratio
  have hspike : 0 < spike := hedge.trans h
  field_simp [ne_of_gt hspike]
  ring

/-- Once the spike is detectable, increasing its strength strictly decreases
the fraction of the target axis left after projecting out the sample PC. -/
theorem samplePCResidualAxisFraction_strictAntiOn_superthreshold
    (n M spike₁ spike₂ : ℝ) (hn : 0 < n) (hM : 0 < M)
    (h₁ : bbpProxyThreshold n M < spike₁) (h₂ : spike₁ < spike₂) :
    samplePCResidualAxisFraction n M spike₂ <
      samplePCResidualAxisFraction n M spike₁ := by
  have hratio : 0 < n / M := div_pos hn hM
  have hedge : 0 < bbpProxyThreshold n M := Real.sqrt_pos.2 hratio
  have hspike₁ : 0 < spike₁ := hedge.trans h₁
  have hspike₂ : 0 < spike₂ := hspike₁.trans h₂
  have h₂super : bbpProxyThreshold n M < spike₂ := h₁.trans h₂
  rw [samplePCResidualAxisFraction_eq_rational n M spike₁ hn hM h₁,
    samplePCResidualAxisFraction_eq_rational n M spike₂ hn hM h₂super]
  have hdenominator₁ : 0 < spike₁ * (spike₁ + n / M) :=
    mul_pos hspike₁ (add_pos hspike₁ hratio)
  have hdenominator₂ : 0 < spike₂ * (spike₂ + n / M) :=
    mul_pos hspike₂ (add_pos hspike₂ hratio)
  rw [div_lt_div_iff₀ hdenominator₂ hdenominator₁]
  have hfactor :
      0 < (spike₂ - spike₁) *
        (spike₁ * spike₂ + spike₁ + spike₂ + n / M) := by
    apply mul_pos (sub_pos.mpr h₂)
    positivity
  have hcore :
      (spike₂ + 1) * (spike₁ * (spike₁ + n / M)) <
        (spike₁ + 1) * (spike₂ * (spike₂ + n / M)) := by
    nlinarith
  simpa only [mul_assoc] using mul_lt_mul_of_pos_left hcore hratio

/-!
### The fitted-PC-count gate

Detectability is not the only gate the shipped calculator applies.  A marker class whose
ancestry axis is the `r`-th population PC is only residualized away if the analyst actually
fitted at least `r` PCs.  Detecting an axis at rank 30 and then fitting 10 PCs removes none
of it.

The definitions above model only the spectral gate, and differential testing against
`map/correctability.rs` found the gap: on the shipped calculator's own unit-test fixture
(`n = 1000`, `M = 4000`, `F = 0.01`, `m = 500`, `theoretical_pc_rank = 3`, `fitted_pcs = 2`)
the calculator reports `residual_axis_fraction = 1` — nothing removed — while
`samplePCResidualAxisFraction` gives `0.0268`.  Over a 1010-design sweep the two disagree on
160 of 1971 marker-class instances, always in the optimistic direction.  The definitions
below close the gap.
-/

/-- Fraction of the target ancestry axis actually removed by a requested PC set, as computed
by the shipped calculator.  `pcRank` is the one-based population-PC index carrying the axis,
`fittedPCs` the number of PCs the analyst requested. -/
noncomputable def removedAxisFraction (n M spike : ℝ) (pcRank fittedPCs : ℕ) : ℝ :=
  if pcRank ≤ fittedPCs then samplePCOverlapSq n M spike else 0

/-- Fraction of the target ancestry axis left after a requested PC set is projected out. -/
noncomputable def fittedResidualAxisFraction (n M spike : ℝ) (pcRank fittedPCs : ℕ) : ℝ :=
  1 - removedAxisFraction n M spike pcRank fittedPCs

/-- **The shipped conjunction is the same function.**  `map/correctability.rs` gates removal
on `detectable_by_sample_pca && theoretical_pc_rank <= fitted_pcs`, whereas
`removedAxisFraction` gates on the rank alone.  The two agree because `samplePCOverlapSq` is
already zero below the edge, so the detectability conjunct is redundant.  Stating this is what
makes the single-gate definition a faithful model rather than a simplification. -/
theorem removedAxisFraction_eq_detectability_gated
    (n M spike : ℝ) (pcRank fittedPCs : ℕ) :
    removedAxisFraction n M spike pcRank fittedPCs =
      (if bbpProxyThreshold n M < spike ∧ pcRank ≤ fittedPCs then
        samplePCOverlapSq n M spike else 0) := by
  unfold removedAxisFraction
  by_cases hrank : pcRank ≤ fittedPCs
  · by_cases hdetect : bbpProxyThreshold n M < spike
    · simp [hrank, hdetect]
    · simp [hrank, hdetect, samplePCOverlapSq]
  · simp [hrank]

/-- Within the fitted PC budget, the shipped residual fraction is exactly the
Johnstone--Paul one. -/
theorem fittedResidualAxisFraction_eq_samplePC
    (n M spike : ℝ) (pcRank fittedPCs : ℕ) (hrank : pcRank ≤ fittedPCs) :
    fittedResidualAxisFraction n M spike pcRank fittedPCs =
      samplePCResidualAxisFraction n M spike := by
  unfold fittedResidualAxisFraction removedAxisFraction samplePCResidualAxisFraction
  simp [hrank]

/-- **An axis outside the fitted PC budget is untouched, however detectable it is.**  This is
the content the spectral model alone does not carry: no amount of separation rescues an axis
the analyst did not fit a PC for.  It is also the exact sense in which
`samplePCResidualAxisFraction` is optimistic about the shipped calculator. -/
theorem fittedResidualAxisFraction_eq_one_of_rank_exceeds_budget
    (n M spike : ℝ) (pcRank fittedPCs : ℕ) (hrank : ¬ pcRank ≤ fittedPCs) :
    fittedResidualAxisFraction n M spike pcRank fittedPCs = 1 := by
  unfold fittedResidualAxisFraction removedAxisFraction
  simp [hrank]

/-- The modeled squared overlap is never negative, on either side of the edge. -/
theorem samplePCOverlapSq_nonneg (n M spike : ℝ) (hn : 0 < n) (hM : 0 < M) :
    0 ≤ samplePCOverlapSq n M spike := by
  by_cases hdetect : bbpProxyThreshold n M < spike
  · exact le_of_lt (samplePCOverlapSq_pos_and_lt_one n M spike hn hM hdetect).1
  · rw [samplePCOverlapSq_eq_zero_of_subthreshold n M spike (not_lt.mp hdetect)]

/-- The shipped residual fraction is never below the spectral one: modelling the PC budget can
only make the reported residual confounding larger.  The corpus's end-to-end risk chain
(`modeledPCResidualSusceptibility`) is therefore a lower bound on the shipped calculator's
residual susceptibility, not an equal. -/
theorem samplePCResidualAxisFraction_le_fitted
    (n M spike : ℝ) (pcRank fittedPCs : ℕ) (hn : 0 < n) (hM : 0 < M) :
    samplePCResidualAxisFraction n M spike ≤
      fittedResidualAxisFraction n M spike pcRank fittedPCs := by
  have hoverlap := samplePCOverlapSq_nonneg n M spike hn hM
  unfold fittedResidualAxisFraction removedAxisFraction samplePCResidualAxisFraction
  by_cases hrank : pcRank ≤ fittedPCs
  · simp [hrank]
  · simp only [hrank, if_false, sub_zero]
    linarith

end Descent

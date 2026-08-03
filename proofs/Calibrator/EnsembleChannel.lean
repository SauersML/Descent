import Mathlib

namespace Calibrator

/-!
# The ensemble channel for order-erased target panels

An order-erased target panel is not the same experiment as a one-locus marginal.  Even
after genomic positions are discarded, fluctuations of its empirical measure depend on
linkage.  The variance of the sample mean exposes a Fejér-weighted autocovariance sum.

The first two theorems record that useful channel exactly for three loci.  The next witness
is the guardrail: the Fejér number is not sufficient for the unordered sample law.  Two
positive trigonometric symbols can have the same sample-mean channel while a symmetric
fourth-order Gaussian statistic differs.  Thus ensemble PGS deployment may learn some LD
from order-erased target panels, but it must not compress all target dependence to one
"long-run variance" without an additional model.

The next section proves the exact symmetry that survives this correction.  Every statistic
of an unordered panel is invariant under time reversal, whereas one ordered adjacent pair
supports an antisymmetric arrow statistic.  This is a finite theorem, not a claim that a
chosen list of Gaussian diagram moments completely determines every stationary process.
Biologically, unordered genotype panels may retain rich symmetric LD fingerprints while
still losing the direction of haplotype or ancestry-tract transitions.

The final theorem is the exact finite-sample geometry behind compound deployment.  Moving
from the source score to the ensemble centroid improves squared spectral loss by precisely
the between-target predictable component; residual within-fibre variation is the price of
blindness.  Statistical identification of that centroid is a separate experiment, not an
algebraic consequence of the decomposition.
-/

open scoped BigOperators

/-- For a stationary three-locus covariance profile `(γ₀, γ₁, γ₂)`, this is
`3 * Var(mean)`: the zero-frequency Fejér evaluation. -/
noncomputable def fejerChannel3 (γ₀ γ₁ γ₂ : ℝ) : ℝ :=
  γ₀ + (4 / 3 : ℝ) * γ₁ + (2 / 3 : ℝ) * γ₂

/-- Direct covariance counting: three diagonal terms, four ordered lag-one terms, and two
ordered lag-two terms. -/
theorem three_mul_sampleMeanVariance3 (γ₀ γ₁ γ₂ : ℝ) :
    3 * ((3 * γ₀ + 4 * γ₁ + 2 * γ₂) / 9) = fejerChannel3 γ₀ γ₁ γ₂ := by
  unfold fejerChannel3
  ring

/-- A symmetric Gaussian fourth-order channel. By Isserlis' identity,
`E[∑_{i<j} Xᵢ²Xⱼ²] = 3γ₀² + 4γ₁² + 2γ₂²`; unlike the sample-mean channel it sees squared
lag covariances. -/
noncomputable def gaussianPairSquareChannel3 (γ₀ γ₁ γ₂ : ℝ) : ℝ :=
  3 * γ₀ ^ 2 + 4 * γ₁ ^ 2 + 2 * γ₂ ^ 2

/-- The flat covariance profile and a dependent profile have exactly the same Fejér
sample-mean channel. -/
theorem equal_fejer_channel_witness :
    fejerChannel3 1 0 0 = fejerChannel3 1 (1 / 10) (-1 / 5) := by
  norm_num [fejerChannel3]

/-- The same two profiles are separated by a symmetric fourth-order statistic. Therefore
the Fejér/sample-mean channel is not sufficient for the unordered Gaussian sample law. -/
theorem unequal_symmetric_fourth_channel_witness :
    gaussianPairSquareChannel3 1 0 0 ≠
      gaussianPairSquareChannel3 1 (1 / 10) (-1 / 5) := by
  norm_num [gaussianPairSquareChannel3]

/-- The dependent witness has a strictly positive trigonometric spectral polynomial on
`[-1,1]`, where `x = cos s`. This is the positivity check needed before interpreting its
first two Fourier coefficients as a stationary covariance profile. -/
theorem dependent_channel_symbol_positive {x : ℝ} (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    (2 / 5 : ℝ) ≤ 7 / 5 + x / 5 - (4 / 5) * x ^ 2 := by
  have hsq : x ^ 2 ≤ 1 := by
    have hxplus : 0 ≤ 1 + x := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hx₁) hxplus]
  nlinarith

/-! ## The finite arrow-of-time quotient

The fourth-order witness above refutes the old one-number description of an unordered
panel, but it does not refute the elementary symmetry that remains: an order-free
observation is invariant under every permutation and therefore under time reversal.
The next results isolate that exact wall without claiming that a particular collection of
moments is a complete invariant of an arbitrary process.

For genetics, the distinction is operational.  An unordered bag of genotypes can retain
rich LD information through its empirical-measure fluctuations, but it cannot decide
which haplotype transition came first.  One ordered adjacent pair is the smallest carrier
of a reversal-odd, direction-of-transition probe.
-/

/-- A statistic on finite panels is order-free when it is constant on list-permutation
classes.  This is the exact deterministic symmetry imposed by discarding genomic order. -/
def IsOrderFreeStatistic {α β : Type*} (statistic : List α → β) : Prop :=
  ∀ xs ys : List α, xs.Perm ys → statistic xs = statistic ys

/-- **Finite reversal wall.** Every order-free statistic is invariant under reversing the
entire panel.  Thus no downstream use of an unordered panel can recover the arrow of time
without adding an order-sensitive observation. -/
theorem orderFreeStatistic_reverse {α β : Type*} {statistic : List α → β}
    (hstatistic : IsOrderFreeStatistic statistic) (xs : List α) :
    statistic xs.reverse = statistic xs :=
  hstatistic xs.reverse xs xs.reverse_perm

/-- The antisymmetric statistic carried by one ordered pair.  Choices of `f` and `g` can
represent two allele, haplotype, ancestry, or functional annotations; the determinant
measures their directional transition imbalance. -/
noncomputable def twoUnitArrow {α : Type*} (f g : α → ℝ) (x₀ x₁ : α) : ℝ :=
  f x₀ * g x₁ - g x₀ * f x₁

/-- Reversing an ordered pair negates its arrow statistic. -/
theorem twoUnitArrow_swap {α : Type*} (f g : α → ℝ) (x₀ x₁ : α) :
    twoUnitArrow f g x₁ x₀ = -twoUnitArrow f g x₀ x₁ := by
  unfold twoUnitArrow
  ring

/-- A single repeated unit carries no arrow.  This is the algebraic core of the
`n' = 1` versus `n' = 2` design threshold: the second ordered unit is the minimal carrier
for this reversal-odd channel. -/
theorem twoUnitArrow_diagonal {α : Type*} (f g : α → ℝ) (x : α) :
    twoUnitArrow f g x x = 0 := by
  unfold twoUnitArrow
  ring

/-- An order-free statistic gives the same answer on the two orientations of a pair. -/
theorem orderFreeStatistic_pair_swap {α β : Type*} {statistic : List α → β}
    (hstatistic : IsOrderFreeStatistic statistic) (x₀ x₁ : α) :
    statistic [x₀, x₁] = statistic [x₁, x₀] := by
  apply hstatistic
  exact (List.Perm.swap x₀ x₁ []).symm

/-- If an ordered pair has a nonzero arrow, the two orientations are distinguished by
that one scalar probe.  The theorem asserts only orientation recovery for the named
pair—not completeness of all Gaussian spectral diagrams. -/
theorem twoUnitArrow_distinguishes_orientation {α : Type*} (f g : α → ℝ)
    (x₀ x₁ : α) (harrow : twoUnitArrow f g x₀ x₁ ≠ 0) :
    twoUnitArrow f g x₀ x₁ ≠ twoUnitArrow f g x₁ x₀ := by
  intro h
  have hswap := twoUnitArrow_swap f g x₀ x₁
  apply harrow
  linarith

/-- Total squared deployment loss for a scalar spectral coordinate across a finite target
ensemble. The vector-valued/bandwise identity follows by summing this theorem by band. -/
noncomputable def ensembleSquaredLoss {ι : Type*} [Fintype ι]
    (target : ι → ℝ) (deployment : ℝ) : ℝ :=
  ∑ i, (target i - deployment) ^ 2

/-- Squared loss of a target-specific predictor across a finite ensemble. -/
noncomputable def ensemblePredictorSquaredLoss {ι : Type*} [Fintype ι]
    (target predictor : ι → ℝ) : ℝ :=
  ∑ i, (target i - predictor i) ^ 2

/-- **Conditional-predictor Pythagorean identity.** If the prediction residual is
orthogonal to the displacement from the source deployment, then source deployment loss is
residual loss plus the squared recoverable displacement. For a conditional expectation,
the orthogonality premise is the defining projection property.

The recoverable term is `∑ᵢ (predictor i - source)²`. It is not generally the variance of
the predictor: it also contains the squared displacement between the source and the target
ensemble mean. This distinction matters when a PGS is transported into cohorts whose
average genetic architecture has shifted from the training population. -/
theorem ensemblePredictorSquaredLoss_decomposition {ι : Type*} [Fintype ι]
    (target predictor : ι → ℝ) (source : ℝ)
    (horthogonal : ∑ i, (target i - predictor i) * (predictor i - source) = 0) :
    ensembleSquaredLoss target source =
      ensemblePredictorSquaredLoss target predictor + ∑ i, (predictor i - source) ^ 2 := by
  unfold ensembleSquaredLoss ensemblePredictorSquaredLoss
  calc
    ∑ i, (target i - source) ^ 2 =
        ∑ i, ((target i - predictor i) ^ 2 + (predictor i - source) ^ 2 +
          2 * ((target i - predictor i) * (predictor i - source))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (target i - predictor i) ^ 2) +
        (∑ i, (predictor i - source) ^ 2) +
          2 * ∑ i, (target i - predictor i) * (predictor i - source) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, (target i - predictor i) ^ 2) +
        ∑ i, (predictor i - source) ^ 2 := by
      rw [horthogonal]
      ring

/-- **Compound deployment Pythagorean identity.** If `center` is an ensemble centroid,
loss from deploying the source decomposes into irreducible within-ensemble loss plus the
recoverable displacement of the centroid from the source. -/
theorem ensembleSquaredLoss_decomposition {ι : Type*} [Fintype ι]
    (target : ι → ℝ) (source center : ℝ)
    (hcenter : ∑ i, (target i - center) = 0) :
    ensembleSquaredLoss target source =
      ensembleSquaredLoss target center + Fintype.card ι * (center - source) ^ 2 := by
  unfold ensembleSquaredLoss
  calc
    ∑ i, (target i - source) ^ 2 =
        ∑ i, ((target i - center) ^ 2 +
          2 * (center - source) * (target i - center) + (center - source) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (target i - center) ^ 2) +
        2 * (center - source) * (∑ i, (target i - center)) +
          ∑ _i : ι, (center - source) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i, (target i - center) ^ 2) +
        Fintype.card ι * (center - source) ^ 2 := by
      rw [hcenter]
      simp

/-! ## Exact multi-band compound geometry -/

/-- Evaluation-weighted squared deployment loss across target populations and genomic
frequency bands.  The weight may vary by target and band; in the spectral portability
model it is the target feature spectrum, optionally multiplied by a task weight. -/
noncomputable def weightedBandEnsembleLoss
    {ι Band : Type*} [Fintype ι] [Fintype Band]
    (weight : ι → Band → ℝ) (target : ι → Band → ℝ)
    (deployment : Band → ℝ) : ℝ :=
  ∑ i, ∑ b, weight i b * (target i b - deployment b) ^ 2

/-- Evaluation-weighted loss of a target-specific predictor. -/
noncomputable def weightedBandPredictorLoss
    {ι Band : Type*} [Fintype ι] [Fintype Band]
    (weight : ι → Band → ℝ) (target predictor : ι → Band → ℝ) : ℝ :=
  ∑ i, ∑ b, weight i b * (target i b - predictor i b) ^ 2

/-- **Exact spectral compound-deployment identity.** If the prediction residual is
orthogonal to displacement from the source in the evaluation-weighted inner product,
then source deployment loss is irreducible residual loss plus the complete recoverable
term

`∑ target ∑ band weight · (predictor - source)²`.

Allowing weights to vary across targets is essential in genetics: LD spectra, genotype
variance, imputation quality, and task emphasis can all differ between deployment
populations.  The recoverable term is not generally the variance of the predictor; it
also retains systematic displacement of the ensemble from the source population. -/
theorem weightedBandEnsembleLoss_decomposition
    {ι Band : Type*} [Fintype ι] [Fintype Band]
    (weight : ι → Band → ℝ) (target predictor : ι → Band → ℝ)
    (source : Band → ℝ)
    (horthogonal :
      ∑ i, ∑ b, weight i b *
        (target i b - predictor i b) * (predictor i b - source b) = 0) :
    weightedBandEnsembleLoss weight target source =
      weightedBandPredictorLoss weight target predictor +
        ∑ i, ∑ b, weight i b * (predictor i b - source b) ^ 2 := by
  unfold weightedBandEnsembleLoss weightedBandPredictorLoss
  have hpoint : ∀ i b,
      weight i b * (target i b - source b) ^ 2 =
        weight i b * (target i b - predictor i b) ^ 2 +
          weight i b * (predictor i b - source b) ^ 2 +
            2 * (weight i b * (target i b - predictor i b) *
              (predictor i b - source b)) := by
    intro i b
    ring
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [horthogonal]
  ring

/-- With nonnegative evaluation weights, an orthogonal conditional predictor can only
improve aggregate deployment risk; its exact improvement is the recoverable term in
`weightedBandEnsembleLoss_decomposition`. -/
theorem weightedBandPredictorLoss_le_source
    {ι Band : Type*} [Fintype ι] [Fintype Band]
    (weight : ι → Band → ℝ) (target predictor : ι → Band → ℝ)
    (source : Band → ℝ) (hweight : ∀ i b, 0 ≤ weight i b)
    (horthogonal :
      ∑ i, ∑ b, weight i b *
        (target i b - predictor i b) * (predictor i b - source b) = 0) :
    weightedBandPredictorLoss weight target predictor ≤
      weightedBandEnsembleLoss weight target source := by
  rw [weightedBandEnsembleLoss_decomposition weight target predictor source horthogonal]
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hweight i b) (sq_nonneg _)

end Calibrator

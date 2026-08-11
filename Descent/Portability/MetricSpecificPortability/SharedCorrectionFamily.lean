/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricSpecificPortability.R2Decomposition
import Descent.PopGen.DGP
import Descent.Spectral.ProjectionShiftBounds
import Descent.Spectral.SpectralDegradation

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory

/-!
# `MetricSpecificPortability.SharedCorrectionFamily`

Part of the split of `Descent/Portability/MetricSpecificPortability.lean`, which was 3,946 lines.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

/-!
## One correction, several deployment targets: the spread law

`ProjectionShiftBounds.sharedCorrectionOptimum` gives the recalibration each
target would choose on its own.  A score deployed to several populations gets
*one* correction.  This section prices that constraint, and the price has a
closed form: it is the curvature-weighted variance of the per-target optimal
corrections, zero exactly when they agree.

The curvature weight is not a free parameter — it is
`weight i * Spectral.coefficientEnergy (B i) beta`, the deployment weight times the
transported direction's energy in that target's own second-moment matrix.  So a
target with little signal energy in the score's direction pulls the shared
correction weakly, which is the right behaviour and is forced rather than
stipulated.

Why this is worth having: multi-population incompatibility becomes a number
computable from quantities already in the corpus — compute `a_i*` per target,
take the weighted variance — instead of a program to be solved or a qualitative
warning to be repeated.
-/

section SharedCorrectionFamily

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq J]

/-- **Curvature of a target's recalibration objective**: how hard target `i`
pulls on the shared correction.  Deployment weight times the energy of the
transported direction in that target's own second-moment matrix.

**DO NOT DELETE AS UNUSED.**  Nothing applies this, and that is the point of it.
`sharedCorrectionConsensus` and `sharedCorrectionSpread` below take `curvature`
and `optimum` as arbitrary functions `ι → ℝ`; this definition and
`targetCorrectionOptimum` are what say which functions the section is about.  The
section's claim that the curvature weight is FORCED rather than stipulated depends
on them: without them the weight is a free parameter, the spread law holds for any
weights whatsoever, and that claim is false.  Deleting them does not break
elaboration, because the arguments are already abstract — it hollows the claim and
leaves the file green, which is why an identifier grep is not enough to justify
removing them.

Empirical status: UNTESTED. -/
noncomputable def targetCorrectionCurvature (weight : ι → ℝ) (B : ι → Matrix J J ℝ)
    (beta : J → ℝ) : ι → ℝ :=
  fun i ↦ weight i * Spectral.coefficientEnergy (B i) beta

/-- **The curvature is the energy scaled by the target's weight**, evaluated where the
family is not degenerate.

Written because the docstring above says an identifier grep is not enough to justify
removing this definition: what makes it load-bearing is a statement that USES it, and a
statement that only quantified over abstract arguments would be satisfied by the constant
zero. At weight one the curvature IS the coefficient energy of that target's operator,
which is the claim the name makes. -/
theorem targetCorrectionCurvature_at_unit_weight (B : ι → Matrix J J ℝ) (beta : J → ℝ)
    (i : ι) :
    targetCorrectionCurvature (fun _ ↦ 1) B beta i = Spectral.coefficientEnergy (B i) beta := by
  unfold targetCorrectionCurvature
  ring

/-- **The correction each target would choose alone**, as a family indexed by
deployment target.

**DO NOT DELETE AS UNUSED** -- see `targetCorrectionCurvature` above.  This is
the `optimum` that `sharedCorrectionConsensus` and `sharedCorrectionSpread`
average and take the variance of; without it the "per-target optimal
corrections" their docstrings name have no referent in the corpus.

`noncomputable` because `Spectral.sharedCorrectionOptimum` is: it divides by
`Spectral.coefficientEnergy`, and it sits inside a `noncomputable section` in
`ProjectionShiftBounds`, so it carries no executable code. That section marker does not
travel with the name, so this definition -- outside such a section -- has to say so
itself, or the compiler IR check fails here rather than at the real-division site.

Empirical status: UNTESTED. -/
noncomputable def targetCorrectionOptimum (B : ι → Matrix J J ℝ) (beta theta : J → ℝ) :
    ι → ℝ :=
  fun i ↦ Spectral.sharedCorrectionOptimum (B i) beta theta

/-- **Each target's own optimum is the shared optimum for that target's operator.**
The definition unfolded, stated so the indexed family is tied to the scalar it indexes
rather than merely resembling it. -/
theorem targetCorrectionOptimum_apply (B : ι → Matrix J J ℝ) (beta theta : J → ℝ)
    (i : ι) :
    targetCorrectionOptimum B beta theta i = Spectral.sharedCorrectionOptimum (B i) beta theta :=
  rfl

/-- The curvature-weighted mean of the per-target optimal corrections: the
shared correction that a weighted-least-squares compromise selects.

Empirical status: NOT AN EMPIRICAL CLAIM -- a weighted mean of two ARBITRARY functions
`ι → ℝ`. No population enters: given the numbers, this is their curvature-weighted average
by definition. The empirical content sits in `targetCorrectionCurvature` and
`targetCorrectionOptimum`, which say WHICH functions the section is about, and those keep
their UNTESTED heads because identifying the abstract slots with specific spectral
quantities is a claim a simulation can refuse. -/
noncomputable def sharedCorrectionConsensus (curvature optimum : ι → ℝ) : ℝ :=
  (∑ i, curvature i * optimum i) / ∑ i, curvature i

/-- **sharedCorrectionConsensus over an empty index, named.** The consensus is a
curvature-weighted mean of the per-task optima, and with no tasks both sums vanish. Lean returns
`0`, which is a perfectly ordinary correction value -- so a consensus over an empty set of tasks
is reported as a definite recommendation rather than as absent. Consumers must require a nonempty
index. -/
theorem sharedCorrectionConsensus_no_curvature_is_junk (curvature optimum : Fin 0 → ℝ) :
    sharedCorrectionConsensus curvature optimum = 0 := by
  unfold sharedCorrectionConsensus
  simp

/-- **The spread law's right-hand side**: the curvature-weighted variance of the
per-target optimal corrections.

Empirical status: NOT AN EMPIRICAL CLAIM -- a weighted variance of arbitrary functions,
with the same standing as `sharedCorrectionConsensus` it is written around. The spread LAW
relating this to the cost is the bias-variance decomposition, which is algebra and could not
have come out otherwise; what could be wrong is the identification of the weights, and that
lives in `targetCorrectionCurvature`. -/
noncomputable def sharedCorrectionSpread (curvature optimum : ι → ℝ) : ℝ :=
  ∑ i, curvature i *
    (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2

/-- Total excess risk incurred across the family by applying the single
correction `correction` instead of each target's own optimum.

Empirical status: NOT AN EMPIRICAL CLAIM -- a weighted squared loss over arbitrary
functions. Calling it "excess risk" is a reading of the weights, not a measurement: whether
this sum IS the excess risk a family of targets pays depends on `targetCorrectionCurvature`
being the right curvature, which is the claim that carries the section and the head. -/
def sharedCorrectionCost (curvature optimum : ι → ℝ) (correction : ℝ) : ℝ :=
  ∑ i, curvature i * (correction - optimum i) ^ 2

/-- The consensus correction is the curvature-weighted centroid: deviations from
it cancel under the curvature weights.  This is the one computation the spread
law rests on. -/
theorem sharedCorrection_centered (curvature optimum : ι → ℝ)
    (hC : ∑ i, curvature i ≠ 0) :
    ∑ i, curvature i *
        (sharedCorrectionConsensus curvature optimum - optimum i) = 0 := by
  have hsplit : ∑ i, curvature i *
        (sharedCorrectionConsensus curvature optimum - optimum i) =
      sharedCorrectionConsensus curvature optimum * (∑ i, curvature i) -
        ∑ i, curvature i * optimum i := by
    calc ∑ i, curvature i *
          (sharedCorrectionConsensus curvature optimum - optimum i)
        = ∑ i, (sharedCorrectionConsensus curvature optimum * curvature i -
            curvature i * optimum i) :=
          Finset.sum_congr rfl (fun i _ ↦ by ring)
      _ = (∑ i, sharedCorrectionConsensus curvature optimum * curvature i) -
            ∑ i, curvature i * optimum i := by
          rw [Finset.sum_sub_distrib]
      _ = sharedCorrectionConsensus curvature optimum * (∑ i, curvature i) -
            ∑ i, curvature i * optimum i := by
          rw [← Finset.mul_sum]
  rw [hsplit]
  unfold sharedCorrectionConsensus
  rw [div_mul_cancel₀ _ hC, sub_self]

/-- **The spread law.**  The cost of any single shared correction splits into a
consensus term, which the best shared correction drives to zero, and the
curvature-weighted variance of the per-target optima, which nothing drives to
zero.  The second term is the price of sharing. -/
theorem sharedCorrectionCost_eq_consensus_add_spread
    (curvature optimum : ι → ℝ) (correction : ℝ) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionCost curvature optimum correction =
      (∑ i, curvature i) *
          (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
        sharedCorrectionSpread curvature optimum := by
  have hcentered := sharedCorrection_centered curvature optimum hC
  unfold sharedCorrectionCost sharedCorrectionSpread
  calc ∑ i, curvature i * (correction - optimum i) ^ 2
      = ∑ i, (curvature i *
              (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
            2 * (correction - sharedCorrectionConsensus curvature optimum) *
              (curvature i *
                (sharedCorrectionConsensus curvature optimum - optimum i)) +
            curvature i *
              (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2) :=
        Finset.sum_congr rfl (fun i _ ↦ by ring)
    _ = (∑ i, curvature i *
            (correction - sharedCorrectionConsensus curvature optimum) ^ 2) +
          (∑ i, 2 * (correction - sharedCorrectionConsensus curvature optimum) *
            (curvature i *
              (sharedCorrectionConsensus curvature optimum - optimum i))) +
          ∑ i, curvature i *
            (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = (∑ i, curvature i) *
            (correction - sharedCorrectionConsensus curvature optimum) ^ 2 +
          ∑ i, curvature i *
            (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hcentered, mul_zero, add_zero]

/-- No shared correction beats the spread. -/
theorem sharedCorrectionSpread_le_cost (curvature optimum : ι → ℝ)
    (correction : ℝ) (hCpos : 0 < ∑ i, curvature i) :
    sharedCorrectionSpread curvature optimum ≤
      sharedCorrectionCost curvature optimum correction := by
  rw [sharedCorrectionCost_eq_consensus_add_spread curvature optimum correction
    (ne_of_gt hCpos)]
  nlinarith [mul_nonneg (le_of_lt hCpos)
    (sq_nonneg (correction - sharedCorrectionConsensus curvature optimum))]

/-- And the consensus correction attains it, so the spread is the value of the
shared-correction problem rather than a lower bound for it. -/
theorem sharedCorrectionCost_at_consensus (curvature optimum : ι → ℝ)
    (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionCost curvature optimum
        (sharedCorrectionConsensus curvature optimum) =
      sharedCorrectionSpread curvature optimum := by
  rw [sharedCorrectionCost_eq_consensus_add_spread curvature optimum _ hC,
    sub_self]
  norm_num

theorem sharedCorrectionSpread_nonneg (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 ≤ curvature i) :
    0 ≤ sharedCorrectionSpread curvature optimum := by
  unfold sharedCorrectionSpread
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hc i) (sq_nonneg _))

/-- **The price of sharing vanishes exactly on agreement.** -/
theorem sharedCorrectionSpread_eq_zero_iff (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 < curvature i) :
    sharedCorrectionSpread curvature optimum = 0 ↔
      ∀ i, optimum i = sharedCorrectionConsensus curvature optimum := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ curvature j *
      (optimum j - sharedCorrectionConsensus curvature optimum) ^ 2 :=
    fun j _ ↦ mul_nonneg (le_of_lt (hc j)) (sq_nonneg _)
  constructor
  · intro h i
    have hle : curvature i *
        (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 ≤
        sharedCorrectionSpread curvature optimum :=
      Finset.single_le_sum hnn (Finset.mem_univ i)
    have hterm : curvature i *
        (optimum i - sharedCorrectionConsensus curvature optimum) ^ 2 = 0 := by
      linarith [hnn i (Finset.mem_univ i), hle, h]
    have hsq : (optimum i -
        sharedCorrectionConsensus curvature optimum) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with hcase | hcase
      · exact absurd hcase (ne_of_gt (hc i))
      · exact hcase
    have hdiff := sq_eq_zero_iff.mp hsq
    linarith
  · intro h
    unfold sharedCorrectionSpread
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [h i, sub_self]
    ring

/-- **The obstruction restated on the per-target optima.**  The shared
correction is free exactly when every target wants the same correction — which
is the vanishing of the pairwise differences `a_i* - a_j*`. -/
theorem sharedCorrectionSpread_eq_zero_iff_agree (curvature optimum : ι → ℝ)
    (hc : ∀ i, 0 < curvature i) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionSpread curvature optimum = 0 ↔
      ∀ i j, optimum i = optimum j := by
  rw [sharedCorrectionSpread_eq_zero_iff curvature optimum hc]
  constructor
  · intro h i j
    rw [h i, h j]
  · intro h i
    have hsum : ∑ j, curvature j * optimum j =
        optimum i * ∑ j, curvature j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ by rw [h j i]; ring)
    unfold sharedCorrectionConsensus
    rw [hsum, mul_div_assoc, div_self hC, mul_one]

/-- **The degenerate control, pinned by proof rather than by a run.**  A family
of targets that all want the same correction pays nothing for sharing one.  Any
simulation of the spread law must return exactly zero here. -/
theorem sharedCorrectionSpread_of_identical_optima (curvature : ι → ℝ)
    (a : ℝ) (hc : ∀ i, 0 < curvature i) (hC : ∑ i, curvature i ≠ 0) :
    sharedCorrectionSpread curvature (fun _ ↦ a) = 0 := by
  rw [sharedCorrectionSpread_eq_zero_iff_agree curvature (fun _ ↦ a) hc hC]
  intro i j
  rfl

end SharedCorrectionFamily

/-!
## No task-independent scalar ordering of spectral portability

The low/high-frequency witness from `SpectralDegradation` is now a dependency of the
metric-specific biological theory, not a leaf result.  Low-frequency shifts model
long-horizon ancestry or population-structure mismatch; high-frequency shifts model local
haplotype, imputation, or short-window mismatch.  A single pair of populations can reverse
order when the deployment task changes bands.
-/

-- `HasTaskIndependentSpectralPortabilityScalar` is defined in
-- `Descent.Spectral.SpectralDegradation`,
-- beside the two-band witness it quantifies over.  It was written out again here, `let`
-- bindings and all, which is how the biological consumer and the spectral witness came to
-- carry two copies of one predicate.

/-- **Metric-specific portability has no universal scalar degradation order.**  At every
nonzero shift the low-band and high-band tasks rank the same two population shifts in
opposite orders. -/
theorem not_hasTaskIndependentSpectralPortabilityScalar (a : ℝ) (ha : a ≠ 0) :
    ¬ Spectral.HasTaskIndependentSpectralPortabilityScalar a := by
  unfold Spectral.HasTaskIndependentSpectralPortabilityScalar
  exact Spectral.twoBand_no_common_monotone_scalar a ha

end Descent.Portability

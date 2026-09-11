/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.VectorAuditConfidence
import Descent.Portability.AuditCovarianceSpectrum

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 10 with the variance and range computed
from the actual audit design. The variance constant is the largest eigenvalue
of the sharp covariance envelope. Normalization and whitening are included
in the fixed row vectors, so this theorem applies in any equivalent Hilbert
representation of the proposed correction span.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SpectralAuditConfidence

open MeasureTheory ProbabilityTheory AuditVarianceGeometry AugmentedAuditLaw BoundedAuditCompletion
open SharedAuditCompletion FiniteAuditConfidence BernsteinTailBound
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Exact marginal variance envelopes for the chosen proxies and honest mean bands. -/
noncomputable def marginal (L U p q lo hi : ι → ℝ) (i : ι) : ℝ :=
  envelope (L i) (U i) (p i) (q i) (clip (lo i) (hi i) (vertex (L i) (U i) (p i) (q i)))

/-- The spectral variance constant of the shared audit. -/
noncomputable def variance (L U p q lo hi : ι → ℝ) (u : ι → E) : ℝ :=
  AuditCovarianceSpectrum.largest (marginal L U p q lo hi) u

/-- The maximum norm-based bounded-increment constant for the nonempty target frame. -/
noncomputable def range [Nonempty ι] (L U p : ι → ℝ) (u : ι → E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖u i‖ * (U i - L i) / p i)

/-- The reported vector radius, including the net factor and exact dimension exponent. -/
noncomputable def confidenceRadius [Nonempty ι] (L U p q lo hi : ι → ℝ)
    (u : ι → E) (δ : ℝ) : ℝ :=
  2 * radius (range L U p u) (variance L U p q lo hi u)
    (Real.log (2 * (5 ^ Module.finrank ℝ E : ℕ) / δ))

/-- Every marginal envelope is nonnegative because it bounds an actual audit variance. -/
theorem marginal_nonneg (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) (i : ι) :
    0 ≤ marginal L U p q lo hi i := by
  exact (variance_nonneg (fun y : ℝ ↦ y) (auditLaw (μ i) (p i) (q i))).trans
    (worst_case_upper (μ i) (L i) (U i) (p i) (q i) (lo i) (hi i) (hp i) (hs i) (hband i))

/-- The largest covariance eigenvalue bounds every unit-ball directional audit variance. -/
theorem directional_variance (L U p q lo hi : ι → ℝ) (u : ι → E)
    (hw : ∀ i, 0 ≤ marginal L U p q lo hi i) (a : E) (ha : ‖a‖ ≤ 1) :
    varianceBound L U p q lo hi (fun i ↦ inner ℝ a (u i)) ≤ variance L U p q lo hi u := by
  have he : varianceBound L U p q lo hi (fun i ↦ inner ℝ a (u i)) =
      ∑ i, marginal L U p q lo hi i * (inner ℝ a (u i)) ^ 2 := by
    unfold varianceBound marginal
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hh := AuditCovarianceSpectrum.quadratic_le (marginal L U p q lo hi) u a
  have hv := AuditCovarianceSpectrum.largest_nonneg (marginal L U p q lo hi) u hw
  have hn : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hv)

/-- Each norm-based row range is bounded by the computed maximum. -/
theorem le_range [Nonempty ι] (L U p : ι → ℝ) (u : ι → E) (i : ι) :
    ‖u i‖ * (U i - L i) / p i ≤ range L U p u :=
  Finset.le_sup' (f := fun i ↦ ‖u i‖ * (U i - L i) / p i) (Finset.mem_univ i)

/-- The computed maximum range is nonnegative on a valid nonempty audit frame. -/
theorem range_nonneg [Nonempty ι] (L U p : ι → ℝ) (u : ι → E)
    (hLU : ∀ i, L i ≤ U i) (hp : ∀ i, 0 < p i) : 0 ≤ range L U p u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : 0 ≤ ‖u i‖ * (U i - L i) / p i :=
    div_nonneg (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (hLU i))) (hp i).le
  exact hi.trans (le_range L U p u i)

/-- The complete vector confidence statement with both constants derived from the audit inputs. -/
theorem confidence [Nonempty ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p q lo hi : ι → ℝ) (u : ι → E) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (hq : ∀ i, q i ∈ Set.Icc (L i) (U i))
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hband : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p q).real {z | confidenceRadius L U p q lo hi u δ <
      ‖VectorAuditConfidence.error μ u z‖} ≤ δ := by
  exact VectorAuditConfidence.vector_confidence μ L U p q lo hi u
    (range L U p u) (variance L U p q lo hi u) δ hδ hp hq hs hband
    (range_nonneg L U p u (fun i ↦ (hq i).1.trans (hq i).2) (fun i ↦ (hp i).1))
    (le_range L U p u)
    (directional_variance L U p q lo hi u (marginal_nonneg μ L U p q lo hi hp hs hband))

end Descent.Portability.SpectralAuditConfidence

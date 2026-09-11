/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RangeAwareAuditSearch
import Descent.Portability.FiniteAuditConfidence

assert_below Descent.Decision Descent.Program

/-!
The statistical connection for Decision-Directed Portability's audit design.
The reciprocal coefficients and common range contributions are computed from
the registered contrasts, outcome support and honest mean bands. The exact
minimax proxy envelope equals those coefficients divided by the actual
request probabilities. The optimized common radius consequently certifies
the actual joint audit, not an unrelated abstract allocation objective.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MinimaxAuditDesignLaw

open MeasureTheory AuditVarianceGeometry FiniteAuditDesign AuditRangeCaps
open FiniteAuditConfidence SharedAuditCompletion IndependentContrastLaw BernsteinTailBound
open scoped BigOperators

/-- The exact envelope maximum at the minimax proxy equals the fixed coefficient divided by p. -/
theorem proxy_envelope_value (L U p lo hi : ℝ) (hp : 0 < p) (hb : lo ≤ hi) :
    envelope L U p (proxy L U lo hi)
      (clip lo hi (vertex L U p (proxy L U lo hi))) =
      (U - proxy L U lo hi) * (proxy L U lo hi - L) / p := by
  apply le_antisymm
  · exact proxy_upper L U p lo hi _ hp (clip_mem lo hi _ hb)
  · have hh := maximizing_mean L U p (proxy L U lo hi) lo hi (proxy L U lo hi) hp.ne'
      (clip_mem lo hi ((L + U) / 2) hb)
    simpa only [envelope, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] using hh

variable {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]

/-- The fixed nonnegative variance coefficient of one unit under the minimax proxy. -/
noncomputable def kappa (L U lo hi : ι → ℝ) (i : ι) : ℝ :=
  (U i - proxy (L i) (U i) (lo i) (hi i)) * (proxy (L i) (U i) (lo i) (hi i) - L i)

/-- Fixed reciprocal-allocation coefficients for the registered contrasts. -/
noncomputable def coefficients (L U lo hi : ι → ℝ) (w : J → ι → ℝ) (j : J) (i : ι) : ℝ :=
  kappa L U lo hi i * w j i ^ 2

/-- Common range contributions, computed before outcomes are requested. -/
noncomputable def ranges (L U : ι → ℝ) (w : J → ι → ℝ) (i : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j ↦ |w j i| * (U i - L i))

/-- The allocation coefficients are nonnegative for valid honest mean bands. -/
theorem coefficients_nonneg (L U lo hi : ι → ℝ) (w : J → ι → ℝ)
    (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i) (j : J) (i : ι) :
    0 ≤ coefficients L U lo hi w j i := by
  have hq := clip_mem (lo i) (hi i) ((L i + U i) / 2) (hb i).2.1
  have hl : L i ≤ proxy (L i) (U i) (lo i) (hi i) := (hb i).1.trans hq.1
  have hu : proxy (L i) (U i) (lo i) (hi i) ≤ U i := hq.2.trans (hb i).2.2
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)) (sq_nonneg _)

/-- The computed abstract row objective equals the actual sharp audit variance envelope. -/
theorem variance_identity (L U p lo hi : ι → ℝ) (w : J → ι → ℝ)
    (hp : ∀ i, 0 < p i) (hb : ∀ i, lo i ≤ hi i) (j : J) :
    varianceBound L U p (fun i ↦ proxy (L i) (U i) (lo i) (hi i)) lo hi (w j) =
      rowVariance (coefficients L U lo hi w) p j := by
  unfold varianceBound rowVariance
  apply Finset.sum_congr rfl
  intro i _
  rw [proxy_envelope_value _ _ _ _ _ (hp i) (hb i)]
  unfold coefficients kappa
  ring

/-- Each registered contrast has range no greater than the common computed row contribution. -/
theorem le_ranges (L U : ι → ℝ) (w : J → ι → ℝ) (j : J) (i : ι) :
    |w j i| * (U i - L i) ≤ ranges L U w i :=
  Finset.le_sup' (f := fun j ↦ |w j i| * (U i - L i)) (Finset.mem_univ j)

/-- A common range contribution is nonnegative under valid support bounds. -/
theorem ranges_nonneg (L U : ι → ℝ) (w : J → ι → ℝ)
    (hLU : ∀ i, L i ≤ U i) (i : ι) : 0 ≤ ranges L U w i := by
  obtain ⟨j⟩ := ‹Nonempty J›
  exact (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (hLU i))).trans (le_ranges L U w j i)

/-- The design's common maximum range is nonnegative under valid probabilities. -/
theorem common_range_nonneg [Nonempty ι] (L U p : ι → ℝ) (w : J → ι → ℝ)
    (hLU : ∀ i, L i ≤ U i) (hp : ∀ i, 0 < p i) : 0 ≤ maxRange (ranges L U w) p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (div_nonneg (ranges_nonneg L U w hLU i) (hp i).le).trans (le_maxRange _ p i)

/-- The optimized common radius bounds the actual finite-library audit failure probability. -/
theorem common_confidence [Nonempty ι] (K : ℕ) [NeZero K]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (L U p lo hi : ι → ℝ) (w : Fin K → ι → ℝ) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1)
    (hb : ∀ i, L i ≤ lo i ∧ lo i ≤ hi i ∧ hi i ≤ U i)
    (hs : ∀ i, ∀ᵐ y ∂μ i, y ∈ Set.Icc (L i) (U i))
    (hm : ∀ i, lo i ≤ (∫ y, y ∂μ i) ∧ (∫ y, y ∂μ i) ≤ hi i) :
    (frameLaw μ p (fun i ↦ proxy (L i) (U i) (lo i) (hi i))).real
      {z | ∃ j, fullRadius (coefficients L U lo hi w) (ranges L U w) p
        (Real.log (2 * K / δ)) < |contrast (w j) z - ∑ i, w j i * ∫ y, y ∂μ i|} ≤ δ := by
  let q (i : ι) := proxy (L i) (U i) (lo i) (hi i)
  let M := maxRange (ranges L U w) p
  let x := Real.log (2 * K / δ)
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hq (i : ι) : q i ∈ Set.Icc (L i) (U i) := by
    have hh := clip_mem (lo i) (hi i) ((L i + U i) / 2) (hb i).2.1
    exact ⟨(hb i).1.trans hh.1, hh.2.trans (hb i).2.2⟩
  have hM : 0 ≤ M := common_range_nonneg L U p w
    (fun i ↦ (hb i).1.trans ((hb i).2.1.trans (hb i).2.2)) (fun i ↦ (hp i).1)
  have hcap (j : Fin K) (i : ι) : |w j i| * (U i - L i) / p i ≤ M :=
    (div_le_div_of_nonneg_right (le_ranges L U w j i) (hp i).1.le).trans (le_maxRange _ p i)
  have ht := finite_library μ L U p q lo hi K hK w (fun _ ↦ M) δ hδ hp hq hs hm
    (fun _ ↦ hM) hcap
  letI := frameLaw_probability μ p q (fun i ↦ ⟨(hp i).1.le, (hp i).2⟩)
  apply le_trans (measureReal_mono (show _ ⊆
    {z | ∃ j, radius M (varianceBound L U p q lo hi (w j)) x <
      |contrast (w j) z - ∑ i, w j i * ∫ y, y ∂μ i|} from ?_)) ht
  rintro z ⟨j, hj⟩
  refine ⟨j, lt_of_le_of_lt ?_ hj⟩
  apply AuditRangeCaps.radius_mono _ _ _ _ x (le_refl _) _
    (confidence_exponent_pos K hK δ hδ).le
  rw [variance_identity L U p lo hi w (fun i ↦ (hp i).1) (fun i ↦ (hb i).2.1)]
  exact row_le_worst _ p j

end Descent.Portability.MinimaxAuditDesignLaw

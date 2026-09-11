/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditCellAveraging
import Descent.Portability.SpectralAuditDesign

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Proposition 17, for the actual audit programs.
Exact averaging within a cell preserves feasibility and expected cost,
reduces every finite contrast and the actual largest covariance eigenvalue,
and cannot increase the maximum observation range. Consequently an actual
spectral optimizer exists that is constant on each specified identical cell,
including the problem with an additional range cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IdenticalAuditCells

open AuditCellAveraging FiniteAuditDesign AuditRangeCaps
open scoped BigOperators

variable {ι J E : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging preserves positive request probabilities. -/
theorem average_positive (s : Finset ι) (p : ι → ℝ) (hs : s.Nonempty)
    (hp : ∀ i, 0 < p i) (i : ι) : 0 < averageCell s p i := by
  by_cases hi : i ∈ s
  · simpa only [averageCell, if_pos hi] using cellMean_pos s p hs (fun j _ ↦ hp j)
  · simpa only [averageCell, if_neg hi] using hp i

/-- Identical floors and costs make exact cell averaging preserve the actual design constraints. -/
theorem feasible_average (s : Finset ι) (p floor c : ι → ℝ) (B f₀ c₀ : ℝ)
    (hs : s.Nonempty) (hf : ∀ i ∈ s, floor i = f₀) (hc : ∀ i ∈ s, c i = c₀)
    (hp : Feasible floor c B p) : Feasible floor c B (averageCell s p) := by
  constructor
  · intro i
    by_cases hi : i ∈ s
    · rw [averageCell, if_pos hi, hf i hi]
      constructor
      · exact le_cellMean s p hs f₀ (fun j hj ↦ by simpa only [hf j hj] using (hp.1 j).1)
      · exact cellMean_le s p hs 1 (fun j _ ↦ (hp.1 j).2)
    · simpa only [averageCell, if_neg hi] using hp.1 i
  · change (∑ i, c i * averageCell s p i) ≤ B
    rw [weighted_sum_eq s p c hs c₀ hc]
    exact hp.2

/-- Every nonnegative identical contrast row has no larger actual audit variance after averaging. -/
theorem finite_variance_le [Fintype J] [Nonempty J]
    (s : Finset ι) (p : ι → ℝ) (a : J → ι → ℝ) (a₀ : J → ℝ)
    (hs : s.Nonempty) (hp : ∀ i, 0 < p i) (ha₀ : ∀ j, 0 ≤ a₀ j)
    (ha : ∀ j i, i ∈ s → a j i = a₀ j) :
    worstVariance a (averageCell s p) ≤ worstVariance a p := by
  apply Finset.sup'_le
  intro j _
  have hh := weighted_reciprocal_le s p (a j) hs (fun i _ ↦ hp i) (a₀ j) (ha₀ j) (ha j)
  exact hh.trans (row_le_worst a p j)

/-- The actual maximum range cannot increase for identical nonnegative cell widths and leverage. -/
theorem range_le [Nonempty ι] (s : Finset ι) (p h : ι → ℝ) (h₀ : ℝ)
    (hs : s.Nonempty) (hp : ∀ i, 0 < p i) (hh₀ : 0 ≤ h₀)
    (hh : ∀ i ∈ s, h i = h₀) : maxRange h (averageCell s p) ≤ maxRange h p := by
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image p hs
  have hmean := le_cellMean s p hs (p j) hmin
  apply (maxRange_le_iff _ _ _).mpr
  intro i
  by_cases hi : i ∈ s
  · rw [averageCell, if_pos hi, hh i hi]
    have hd := div_le_div_of_nonneg_left hh₀ (hp j) hmean
    have hjbound := le_maxRange h p j
    rw [hh j hj] at hjbound
    exact hd.trans hjbound
  · simpa only [averageCell, if_neg hi] using le_maxRange h p i

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Identical uncertainty and repair vectors give a smaller actual spectral covariance objective. -/
theorem spectral_variance_le (s : Finset ι) (p κ : ι → ℝ) (u : ι → E) (κ₀ : ℝ) (u₀ : E)
    (hs : s.Nonempty) (hp : ∀ i, 0 < p i) (hκ : ∀ i, 0 ≤ κ i)
    (hk : ∀ i ∈ s, κ i = κ₀) (hu : ∀ i ∈ s, u i = u₀) :
    SpectralAuditDesign.objective κ u (averageCell s p) ≤ SpectralAuditDesign.objective κ u p := by
  obtain ⟨j, hj⟩ := hs
  have hk₀ : 0 ≤ κ₀ := by simpa only [hk j hj] using hκ j
  unfold SpectralAuditDesign.objective
  apply (AuditRayleighGeometry.largest_le_iff _ u
    (fun i ↦ div_nonneg (hκ i) (average_positive s p hs hp i).le) _).mpr
  intro v hv
  have hh := weighted_reciprocal_le s p (fun i ↦ κ i * (inner ℝ v (u i)) ^ 2) hs
    (fun i _ ↦ hp i) (κ₀ * (inner ℝ v u₀) ^ 2) (mul_nonneg hk₀ (sq_nonneg _))
    (fun i hi ↦ by rw [hk i hi, hu i hi])
  have he (q : ι → ℝ) : (∑ i, κ i / q i * (inner ℝ v (u i)) ^ 2) =
      ∑ i, (κ i * (inner ℝ v (u i)) ^ 2) / q i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← he, ← he] at hh
  exact hh.trans (SpectralAuditDesign.direction_le κ u p hκ hp v hv)

/-- A genuine attained spectral optimum can be chosen constant throughout an identical cell. -/
theorem spectral_optimum_constant (s : Finset ι) (κ floor c : ι → ℝ) (u : ι → E)
    (B κ₀ f₀ c₀ : ℝ) (u₀ : E) (hs : s.Nonempty)
    (hκ : ∀ i, 0 ≤ κ i) (hfloor : ∀ i, 0 < floor i)
    (hk : ∀ i ∈ s, κ i = κ₀) (hu : ∀ i ∈ s, u i = u₀)
    (hf : ∀ i ∈ s, floor i = f₀) (hc : ∀ i ∈ s, c i = c₀)
    (hne : {p | Feasible floor c B p}.Nonempty) :
    ∃ p, Feasible floor c B p ∧
      IsMinOn (SpectralAuditDesign.objective κ u) {q | Feasible floor c B q} p ∧
      ∀ i ∈ s, ∀ j ∈ s, p i = p j := by
  obtain ⟨p, hp, hmin⟩ := SpectralAuditDesign.optimum_exists κ floor c u B hκ hfloor hne
  have hpos (i : ι) := (hfloor i).trans_le (hp.1 i).1
  have hvar := spectral_variance_le s p κ u κ₀ u₀ hs hpos hκ hk hu
  refine ⟨averageCell s p, feasible_average s p floor c B f₀ c₀ hs hf hc hp, ?_, ?_⟩
  · intro q hq
    exact hvar.trans (hmin hq)
  · intro i hi j hj
    simp only [averageCell, if_pos hi, if_pos hj]

/-- An actual range-capped spectral optimum also admits exact identical-cell aggregation. -/
theorem capped_spectral_optimum_constant [Nonempty ι]
    (s : Finset ι) (κ floor c h : ι → ℝ) (u : ι → E)
    (B m κ₀ f₀ c₀ h₀ : ℝ) (u₀ : E) (hs : s.Nonempty) (hm : 0 < m)
    (hκ : ∀ i, 0 ≤ κ i) (hfloor : ∀ i, 0 < floor i)
    (hk : ∀ i ∈ s, κ i = κ₀) (hu : ∀ i ∈ s, u i = u₀)
    (hf : ∀ i ∈ s, floor i = f₀) (hc : ∀ i ∈ s, c i = c₀)
    (hh : ∀ i ∈ s, h i = h₀)
    (hne : {p | Feasible floor c B p ∧ maxRange h p ≤ m}.Nonempty) :
    ∃ p, (Feasible floor c B p ∧ maxRange h p ≤ m) ∧
      IsMinOn (SpectralAuditDesign.objective κ u)
        {q | Feasible floor c B q ∧ maxRange h q ≤ m} p ∧
      ∀ i ∈ s, ∀ j ∈ s, p i = p j := by
  have hcf (i : ι) : 0 < cappedFloor floor h m i := (hfloor i).trans_le (le_max_left _ _)
  have he (p : ι → ℝ) := capped_feasible_iff floor c h p B m hfloor hm
  have hne' : {p | Feasible (cappedFloor floor h m) c B p}.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, (he p).mpr hp⟩
  obtain ⟨p, hp, hmin, hconst⟩ := spectral_optimum_constant s κ (cappedFloor floor h m) c u
    B κ₀ (max f₀ (h₀ / m)) c₀ u₀ hs hκ hcf hk hu
    (fun i hi ↦ by simp only [cappedFloor, hf i hi, hh i hi]) hc hne'
  exact ⟨p, (he p).mp hp, fun q hq ↦ hmin ((he q).mpr hq), hconst⟩

end Descent.Portability.IdenticalAuditCells

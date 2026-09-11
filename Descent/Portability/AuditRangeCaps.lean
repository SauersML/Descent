/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteAuditDesignConvexity
import Descent.Portability.BernsteinTailBound

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16. A bound on the actual maximum
observation range is exactly an increased probability floor. Each feasible
capped variance problem therefore remains a compact convex audit design,
including boundary budgets. The full Bernstein radius has an attained
minimum and can be optimized through these capped problems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditRangeCaps

open FiniteAuditDesign FiniteAuditDesignConvexity BernsteinTailBound
open scoped BigOperators

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- The common maximum observation range for a finite decision library. -/
noncomputable def maxRange (h p : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ h i / p i)

/-- The probability floors imposed by a positive range cap. -/
noncomputable def cappedFloor (floor h : ι → ℝ) (m : ℝ) (i : ι) : ℝ := max (floor i) (h i / m)

/-- The full finite-library Bernstein objective, including both variance and range. -/
noncomputable def fullRadius (a : J → ι → ℝ) (h p : ι → ℝ) (x : ℝ) : ℝ :=
  radius (maxRange h p) (worstVariance a p) x

/-- A coordinate range is bounded by the actual maximum. -/
theorem le_maxRange (h p : ι → ℝ) (i : ι) : h i / p i ≤ maxRange h p :=
  Finset.le_sup' (f := fun i ↦ h i / p i) (Finset.mem_univ i)

/-- The maximum range bound is equivalent to all coordinate range bounds. -/
theorem maxRange_le_iff (h p : ι → ℝ) (m : ℝ) :
    maxRange h p ≤ m ↔ ∀ i, h i / p i ≤ m := by
  constructor
  · intro hh i
    exact (le_maxRange h p i).trans hh
  · intro hh
    exact Finset.sup'_le _ _ (fun i _ ↦ hh i)

/-- A positive range cap is exactly a reciprocal lower bound on each request probability. -/
theorem coordinate_cap_iff (h p m : ℝ) (hp : 0 < p) (hm : 0 < m) :
    h / p ≤ m ↔ h / m ≤ p := by
  rw [div_le_iff₀ hp, div_le_iff₀ hm, mul_comm m p]

/-- The capped design is exactly the original feasible design with its range bounded. -/
theorem capped_feasible_iff (floor c h p : ι → ℝ) (B m : ℝ)
    (hf : ∀ i, 0 < floor i) (hm : 0 < m) :
    Feasible (cappedFloor floor h m) c B p ↔ Feasible floor c B p ∧ maxRange h p ≤ m := by
  constructor
  · intro hp
    have hb (i : ι) : floor i ≤ p i := (le_max_left _ _).trans (hp.1 i).1
    refine ⟨⟨fun i ↦ ⟨hb i, (hp.1 i).2⟩, hp.2⟩, ?_⟩
    apply (maxRange_le_iff h p m).mpr
    intro i
    apply (coordinate_cap_iff (h i) (p i) m ((hf i).trans_le (hb i)) hm).mpr
    exact (le_max_right _ _).trans (hp.1 i).1
  · rintro ⟨hp, hr⟩
    refine ⟨?_, hp.2⟩
    intro i
    refine ⟨max_le (hp.1 i).1 ?_, (hp.1 i).2⟩
    exact (coordinate_cap_iff (h i) (p i) m ((hf i).trans_le (hp.1 i).1) hm).mp
      ((maxRange_le_iff h p m).mp hr i)

/-- Positive range contributions and request probabilities give a strictly positive range. -/
theorem maxRange_pos (h p : ι → ℝ) (hh : ∀ i, 0 < h i) (hp : ∀ i, 0 < p i) :
    0 < maxRange h p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (div_pos (hh i) (hp i)).trans_le (le_maxRange h p i)

/-- Increasing either variance or range can only increase the full confidence radius. -/
theorem radius_mono (M₁ M₂ v₁ v₂ x : ℝ) (hM : M₁ ≤ M₂) (hv : v₁ ≤ v₂) (hx : 0 ≤ x) :
    radius M₁ v₁ x ≤ radius M₂ v₂ x := by
  unfold radius
  have hs : Real.sqrt (2 * v₁ * x) ≤ Real.sqrt (2 * v₂ * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hm : 2 * M₁ * x / 3 ≤ 2 * M₂ * x / 3 := by nlinarith
  exact add_le_add hs hm

/-- The actual full confidence radius is continuous on the positive-probability feasible set. -/
theorem fullRadius_continuous (a : J → ι → ℝ) (floor c h : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) : ContinuousOn (fullRadius a h · x) {p | Feasible floor c B p} := by
  have hr : ContinuousOn (maxRange h) {p | Feasible floor c B p} := by
    apply ContinuousOn.finset_sup'_apply
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun p hp ↦ ne_of_gt ((hf i).trans_le (hp.1 i).1))
  have hv := objective_continuous a floor c B hf
  exact ((continuousOn_const.mul hv).mul continuousOn_const).sqrt.add
    (((continuousOn_const.mul hr).mul continuousOn_const).div_const 3)

/-- The full variance-and-range objective has a genuine minimizing audit design. -/
theorem full_optimum_exists (a : J → ι → ℝ) (floor c h : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) (hne : {p | Feasible floor c B p}.Nonempty) :
    ∃ p, Feasible floor c B p ∧ IsMinOn (fullRadius a h · x) {q | Feasible floor c B q} p :=
  (feasible_compact floor c B).exists_isMinOn hne (fullRadius_continuous a floor c h B x hf)

/-- Every feasible capped variance problem has an attained optimum. -/
theorem capped_optimum_exists (a : J → ι → ℝ) (floor c h : ι → ℝ) (B m : ℝ)
    (hf : ∀ i, 0 < floor i)
    (hne : {p | Feasible (cappedFloor floor h m) c B p}.Nonempty) :
    ∃ p, Feasible (cappedFloor floor h m) c B p ∧
      IsMinOn (worstVariance a) {q | Feasible (cappedFloor floor h m) c B q} p :=
  optimum_exists a (cappedFloor floor h m) c B
    (fun i ↦ (hf i).trans_le (le_max_left _ _)) hne

/-- At the optimum's own range cap, minimizing variance preserves global radius optimality. -/
theorem exact_cap_reduction (a : J → ι → ℝ) (floor c h p : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i) (hx : 0 ≤ x)
    (hp : Feasible floor c B p)
    (hopt : IsMinOn (fullRadius a h · x) {q | Feasible floor c B q} p) :
    ∃ q, Feasible (cappedFloor floor h (maxRange h p)) c B q ∧
      IsMinOn (worstVariance a) {r | Feasible (cappedFloor floor h (maxRange h p)) c B r} q ∧
      radius (maxRange h p) (worstVariance a q) x = fullRadius a h p x ∧
      fullRadius a h q x = fullRadius a h p x := by
  have hm := maxRange_pos h p hh (fun i ↦ (hf i).trans_le (hp.1 i).1)
  have hpc := (capped_feasible_iff floor c h p B (maxRange h p) hf hm).mpr ⟨hp, le_refl _⟩
  obtain ⟨q, hq, hqopt⟩ := capped_optimum_exists a floor c h B (maxRange h p) hf ⟨p, hpc⟩
  have hqu := (capped_feasible_iff floor c h q B (maxRange h p) hf hm).mp hq
  have hv := hqopt hpc
  have hlow := hopt hqu.1
  have hmid : fullRadius a h q x ≤ radius (maxRange h p) (worstVariance a q) x :=
    radius_mono _ _ _ _ x hqu.2 (le_refl _) hx
  have hupp : radius (maxRange h p) (worstVariance a q) x ≤ fullRadius a h p x :=
    radius_mono _ _ _ _ x (le_refl _) hv hx
  exact ⟨q, hq, hqopt, le_antisymm hupp (hlow.trans hmid),
    le_antisymm (hmid.trans hupp) hlow⟩

end Descent.Portability.AuditRangeCaps

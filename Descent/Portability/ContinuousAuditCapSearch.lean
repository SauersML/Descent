/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RangeAwareAuditSearch

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16 for a general continuous audit
variance criterion. The actual positive-floor budget set is compact; every
feasible capped subproblem therefore has an attained minimizer. Selecting
the smallest full radius among finitely many exact capped solves has the
proved geometric-grid factor guarantee against every feasible design.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousAuditCapSearch

open FiniteAuditDesign FiniteAuditDesignConvexity AuditRangeCaps BernsteinTailBound
open GeometricAuditCaps RangeAwareAuditSearch

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The full variance-and-range criterion for any continuous audit variance functional. -/
noncomputable def designRadius (F : (ι → ℝ) → ℝ) (h p : ι → ℝ) (x : ℝ) : ℝ :=
  radius (maxRange h p) (F p) x

/-- A capped design is always in the original probability and expected-budget domain. -/
theorem capped_subset (floor c h : ι → ℝ) (B m : ℝ) :
    {p | Feasible (cappedFloor floor h m) c B p} ⊆ {p | Feasible floor c B p} := by
  intro p hp
  exact ⟨fun i ↦ ⟨(le_max_left _ _).trans (hp.1 i).1, (hp.1 i).2⟩, hp.2⟩

/-- Every feasible capped continuous-variance subproblem has an actual minimizer. -/
theorem capped_minimum (F : (ι → ℝ) → ℝ) (floor c h : ι → ℝ) (B m : ℝ)
    (hF : ContinuousOn F {p | Feasible floor c B p})
    (hne : {p | Feasible (cappedFloor floor h m) c B p}.Nonempty) :
    ∃ p, Feasible (cappedFloor floor h m) c B p ∧
      IsMinOn F {q | Feasible (cappedFloor floor h m) c B q} p :=
  (feasible_compact (cappedFloor floor h m) c B).exists_isMinOn hne
    (hF.mono (capped_subset floor c h B m))

/-- The complete range-aware objective is continuous on the actual positive-floor design set. -/
theorem radius_continuous (F : (ι → ℝ) → ℝ) (floor c h : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) (hF : ContinuousOn F {p | Feasible floor c B p}) :
    ContinuousOn (fun p ↦ designRadius F h p x) {p | Feasible floor c B p} := by
  have hr : ContinuousOn (maxRange h) {p | Feasible floor c B p} := by
    apply ContinuousOn.finset_sup'_apply
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun p hp ↦ ((hf i).trans_le (hp.1 i).1).ne')
  exact ((continuousOn_const.mul hF).mul continuousOn_const).sqrt.add
    (((continuousOn_const.mul hr).mul continuousOn_const).div_const 3)

/-- The globally best complete confidence-radius criterion is attained. -/
theorem radius_minimum (F : (ι → ℝ) → ℝ) (floor c h : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) (hF : ContinuousOn F {p | Feasible floor c B p})
    (hne : {p | Feasible floor c B p}.Nonempty) :
    ∃ p, Feasible floor c B p ∧
      IsMinOn (fun q ↦ designRadius F h q x) {q | Feasible floor c B q} p :=
  (feasible_compact floor c B).exists_isMinOn hne (radius_continuous F floor c h B x hf hF)

/-- Optimizing variance at a global optimum's exact range cap preserves the best full radius. -/
theorem exact_cap_reduction (F : (ι → ℝ) → ℝ) (floor c h p : ι → ℝ) (B x : ℝ)
    (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i) (hx : 0 ≤ x)
    (hF : ContinuousOn F {p | Feasible floor c B p}) (hp : Feasible floor c B p)
    (hopt : IsMinOn (fun q ↦ designRadius F h q x) {q | Feasible floor c B q} p) :
    ∃ q, Feasible (cappedFloor floor h (maxRange h p)) c B q ∧
      IsMinOn F {r | Feasible (cappedFloor floor h (maxRange h p)) c B r} q ∧
      radius (maxRange h p) (F q) x = designRadius F h p x ∧
      designRadius F h q x = designRadius F h p x := by
  have hm := maxRange_pos h p hh (fun i ↦ (hf i).trans_le (hp.1 i).1)
  have hpc := (capped_feasible_iff floor c h p B (maxRange h p) hf hm).mpr ⟨hp, le_refl _⟩
  obtain ⟨q, hq, hqopt⟩ := capped_minimum F floor c h B (maxRange h p) hF ⟨p, hpc⟩
  have hqu := (capped_feasible_iff floor c h q B (maxRange h p) hf hm).mp hq
  have hv := hqopt hpc
  have hlow := hopt hqu.1
  have hmid : designRadius F h q x ≤ radius (maxRange h p) (F q) x :=
    radius_mono _ _ _ _ x hqu.2 (le_refl _) hx
  have hupp : radius (maxRange h p) (F q) x ≤ designRadius F h p x :=
    radius_mono _ _ _ _ x (le_refl _) hv hx
  exact ⟨q, hq, hqopt, le_antisymm hupp (hlow.trans hmid),
    le_antisymm (hmid.trans hupp) hlow⟩

/-- Any exact solutions of all feasible grid subproblems support the full-radius guarantee. -/
theorem exact_solvers_guarantee (F : (ι → ℝ) → ℝ) (floor c h : ι → ℝ)
    (B x low high rate : ℝ) (N : ℕ) (hf : ∀ i, 0 < floor i) (hx : 0 ≤ x)
    (hlow : 0 < low) (hrate : 1 < rate) (hN : high ≤ low * rate ^ N)
    (hranges : ∀ p, Feasible floor c B p → maxRange h p ∈ Set.Icc low high)
    (hne : ∃ p, Feasible floor c B p)
    (solve : ValidCap floor c h B low high rate N → ι → ℝ)
    (hsolve : ∀ j, Feasible (cappedFloor floor h j.val.val) c B (solve j) ∧
      IsMinOn F {p | Feasible (cappedFloor floor h j.val.val) c B p} (solve j)) :
    ∃ j : ValidCap floor c h B low high rate N,
      (∀ k, designRadius F h (solve j) x ≤ designRadius F h (solve k) x) ∧
      ∀ p, Feasible floor c B p → designRadius F h (solve j) x ≤ rate * designRadius F h p x := by
  classical
  have hvalid : Nonempty (ValidCap floor c h B low high rate N) := by
    obtain ⟨p, hp⟩ := hne
    obtain ⟨cap, hc, hmc, _⟩ := grid_covers low high rate (maxRange h p) N
      hlow hrate hN (hranges p hp)
    have hcap : 0 < cap := (hlow.trans_le (hranges p hp).1).trans_le hmc
    exact ⟨⟨⟨cap, hc⟩, p, (capped_feasible_iff floor c h p B cap hf hcap).mpr ⟨hp, hmc⟩⟩⟩
  letI := hvalid
  letI : Finite (ValidCap floor c h B low high rate N) := by
    unfold ValidCap
    infer_instance
  obtain ⟨j, hj⟩ := Finite.exists_min (fun k ↦ designRadius F h (solve k) x)
  refine ⟨j, hj, ?_⟩
  intro p hp
  obtain ⟨cap, hc, hmc, hcm⟩ := grid_covers low high rate (maxRange h p) N
    hlow hrate hN (hranges p hp)
  have hcap : 0 < cap := (hlow.trans_le (hranges p hp).1).trans_le hmc
  have hpc := (capped_feasible_iff floor c h p B cap hf hcap).mpr ⟨hp, hmc⟩
  let k : ValidCap floor c h B low high rate N := ⟨⟨cap, hc⟩, p, hpc⟩
  have hq := hsolve k
  have hqr := (capped_feasible_iff floor c h (solve k) B cap hf hcap).mp hq.1
  have hrad : designRadius F h (solve k) x ≤ rate * designRadius F h p x :=
    (radius_mono _ cap _ _ x hqr.2 (le_refl _) hx).trans
      (radius_factor (maxRange h p) cap (F p) (F (solve k)) x rate
        hx hrate.le hcm (hq.2 hpc))
  exact (hj k).trans hrad

/-- The finite cap search has its factor guarantee from the actual design inputs. -/
theorem finite_search_exists (F : (ι → ℝ) → ℝ) (floor c h : ι → ℝ) (B x rate : ℝ)
    (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i) (hx : 0 ≤ x) (hrate : 1 < rate)
    (hF : ContinuousOn F {p | Feasible floor c B p})
    (hne : ∃ p, Feasible floor c B p) :
    ∃ N : ℕ, ∃ cap ∈ grid (lowerCap h) (upperCap floor h) rate N, ∃ q,
      Feasible (cappedFloor floor h cap) c B q ∧
      IsMinOn F {p | Feasible (cappedFloor floor h cap) c B p} q ∧
      ∀ p, Feasible floor c B p → designRadius F h q x ≤ rate * designRadius F h p x := by
  classical
  have hl : 0 < lowerCap h := maxRange_pos h (fun _ ↦ 1) hh (fun _ ↦ by norm_num)
  have hr : ∀ p, Feasible floor c B p →
      maxRange h p ∈ Set.Icc (lowerCap h) (upperCap floor h) :=
    fun p hp ↦ range_interval floor c h p B hf (fun i ↦ (hh i).le) hp
  have hinterval : lowerCap h ≤ upperCap floor h := by
    obtain ⟨p, hp⟩ := hne
    exact (hr p hp).1.trans (hr p hp).2
  obtain ⟨N, hN, _⟩ := finite_grid_exists (lowerCap h) (upperCap floor h) rate hl hinterval hrate
  let V := ValidCap floor c h B (lowerCap h) (upperCap floor h) rate N
  have hex (j : V) : ∃ q, Feasible (cappedFloor floor h j.val.val) c B q ∧
      IsMinOn F {p | Feasible (cappedFloor floor h j.val.val) c B p} q :=
    capped_minimum F floor c h B j.val.val hF j.property
  let solve (j : V) := Classical.choose (hex j)
  have hsolve (j : V) := Classical.choose_spec (hex j)
  obtain ⟨j, _, hj⟩ := exact_solvers_guarantee F floor c h B x (lowerCap h) (upperCap floor h)
    rate N hf hx hl hrate hN hr hne solve hsolve
  exact ⟨N, j.val.val, j.val.property, solve j, (hsolve j).1, (hsolve j).2, hj⟩

end Descent.Portability.ContinuousAuditCapSearch

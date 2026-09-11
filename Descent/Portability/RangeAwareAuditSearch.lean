/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GeometricAuditCaps
import Mathlib.Data.Fintype.Lattice

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16, finite-library search theorem.
The interval of possible range constants is derived from the actual floors
and caps. All feasible geometric-grid subproblems have exact variance
minimizers; selecting the least-radius returned candidate gives the stated
multiplicative guarantee against every feasible audit design.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RangeAwareAuditSearch

open FiniteAuditDesign AuditRangeCaps GeometricAuditCaps

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- The smallest possible range cap with all request probabilities at most one. -/
noncomputable def lowerCap (h : ι → ℝ) : ℝ := maxRange h (fun _ ↦ 1)

/-- The largest possible range cap with all request probabilities above their registered floors. -/
noncomputable def upperCap (floor h : ι → ℝ) : ℝ := maxRange h floor

/-- Every feasible audit range lies in the computable cap interval. -/
theorem range_interval (floor c h p : ι → ℝ) (B : ℝ)
    (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 ≤ h i) (hp : Feasible floor c B p) :
    maxRange h p ∈ Set.Icc (lowerCap h) (upperCap floor h) := by
  constructor
  · apply (maxRange_le_iff h (fun _ ↦ 1) (maxRange h p)).mpr
    intro i
    exact (div_le_div_of_nonneg_left (hh i) ((hf i).trans_le (hp.1 i).1)
      (hp.1 i).2).trans (le_maxRange h p i)
  · apply (maxRange_le_iff h p (upperCap floor h)).mpr
    intro i
    exact (div_le_div_of_nonneg_left (hh i) (hf i) (hp.1 i).1).trans (le_maxRange h floor i)

/-- Feasible grid caps are a finite index set; infeasible caps have no solver output. -/
def ValidCap (floor c h : ι → ℝ) (B low high rate : ℝ) (N : ℕ) :=
  {cap : {m : ℝ // m ∈ grid low high rate N} //
    ∃ p, Feasible (cappedFloor floor h cap.val) c B p}

/-- Any exact solutions of all feasible grid subproblems support the full-radius guarantee. -/
theorem exact_solvers_guarantee (a : J → ι → ℝ) (floor c h : ι → ℝ)
    (B x low high rate : ℝ) (N : ℕ) (hf : ∀ i, 0 < floor i) (hx : 0 ≤ x)
    (hlow : 0 < low) (hrate : 1 < rate) (hN : high ≤ low * rate ^ N)
    (hranges : ∀ p, Feasible floor c B p → maxRange h p ∈ Set.Icc low high)
    (hne : ∃ p, Feasible floor c B p)
    (solve : ValidCap floor c h B low high rate N → ι → ℝ)
    (hsolve : ∀ j, Feasible (cappedFloor floor h j.val.val) c B (solve j) ∧
      IsMinOn (worstVariance a) {p | Feasible (cappedFloor floor h j.val.val) c B p} (solve j)) :
    ∃ j : ValidCap floor c h B low high rate N,
      (∀ k, fullRadius a h (solve j) x ≤ fullRadius a h (solve k) x) ∧
      ∀ p, Feasible floor c B p → fullRadius a h (solve j) x ≤ rate * fullRadius a h p x := by
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
  obtain ⟨j, hj⟩ := Finite.exists_min (fun k ↦ fullRadius a h (solve k) x)
  refine ⟨j, hj, ?_⟩
  intro p hp
  obtain ⟨cap, hc, hmc, hcm⟩ := grid_covers low high rate (maxRange h p) N
    hlow hrate hN (hranges p hp)
  have hcap : 0 < cap := (hlow.trans_le (hranges p hp).1).trans_le hmc
  have hpc := (capped_feasible_iff floor c h p B cap hf hcap).mpr ⟨hp, hmc⟩
  let k : ValidCap floor c h B low high rate N := ⟨⟨cap, hc⟩, p, hpc⟩
  have hq := hsolve k
  have hqr := (capped_feasible_iff floor c h (solve k) B cap hf hcap).mp hq.1
  have hrad : fullRadius a h (solve k) x ≤ rate * fullRadius a h p x :=
    (radius_mono _ cap _ _ x hqr.2 (le_refl _) hx).trans
      (radius_factor (maxRange h p) cap (worstVariance a p) (worstVariance a (solve k)) x rate
        hx hrate.le hcm (hq.2 hpc))
  exact (hj k).trans hrad

/-- The finite cap search has its factor guarantee from the actual design inputs. -/
theorem finite_search_exists (a : J → ι → ℝ) (floor c h : ι → ℝ) (B x rate : ℝ)
    (hf : ∀ i, 0 < floor i) (hh : ∀ i, 0 < h i) (hx : 0 ≤ x) (hrate : 1 < rate)
    (hne : ∃ p, Feasible floor c B p) :
    ∃ N : ℕ, ∃ cap ∈ grid (lowerCap h) (upperCap floor h) rate N, ∃ q,
      Feasible (cappedFloor floor h cap) c B q ∧
      IsMinOn (worstVariance a) {p | Feasible (cappedFloor floor h cap) c B p} q ∧
      ∀ p, Feasible floor c B p → fullRadius a h q x ≤ rate * fullRadius a h p x := by
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
      IsMinOn (worstVariance a) {p | Feasible (cappedFloor floor h j.val.val) c B p} q :=
    capped_optimum_exists a floor c h B j.val.val hf j.property
  let solve (j : V) := Classical.choose (hex j)
  have hsolve (j : V) := Classical.choose_spec (hex j)
  obtain ⟨j, _, hj⟩ := exact_solvers_guarantee a floor c h B x (lowerCap h) (upperCap floor h)
    rate N hf hx hl hrate hN hr hne solve hsolve
  exact ⟨N, j.val.val, j.val.property, solve j, (hsolve j).1, (hsolve j).2, hj⟩

end Descent.Portability.RangeAwareAuditSearch

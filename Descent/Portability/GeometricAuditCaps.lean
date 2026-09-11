/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AuditRangeCaps
import Mathlib.Algebra.Order.Archimedean.Basic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 16: construction of a finite geometric
cap grid and the full-radius approximation guarantee. The next grid cap is
proved to exist; its coverage is not an assumed oracle. Every feasible inner
variance problem has a minimizer by the preceding compactness theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GeometricAuditCaps

open FiniteAuditDesign AuditRangeCaps BernsteinTailBound

/-- A finite geometric grid clipped at the upper endpoint and including that endpoint. -/
noncomputable def grid (low high rate : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact insert high ((Finset.range (N + 1)).image (fun n ↦ min high (low * rate ^ n)))

/-- Every point in the cap interval has a grid cap above it within the specified factor. -/
theorem grid_covers (low high rate m : ℝ) (N : ℕ) (hlow : 0 < low)
    (hrate : 1 < rate) (hN : high ≤ low * rate ^ N) (hm : m ∈ Set.Icc low high) :
    ∃ cap ∈ grid low high rate N, m ≤ cap ∧ cap ≤ rate * m := by
  classical
  by_cases hend : m = high
  · refine ⟨high, Finset.mem_insert_self _ _, ?_, ?_⟩
    · exact hend.le
    · have hmpos : 0 < m := hlow.trans_le hm.1
      rw [← hend]
      nlinarith
  · have hmh : m < high := lt_of_le_of_ne hm.2 hend
    obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near
      ((le_div_iff₀ hlow).mpr (by simpa using hm.1)) hrate
    have hn : n < N := by
      by_contra hh
      have hpow : rate ^ N ≤ rate ^ n := pow_le_pow_right₀ hrate.le (Nat.le_of_not_gt hh)
      have hmul := mul_le_mul_of_nonneg_left hpow hlow.le
      have hsmall : low * rate ^ n ≤ m := by
        have hh := (le_div_iff₀ hlow).mp hnlow
        nlinarith
      linarith
    have hmcap : m < low * rate ^ (n + 1) := by
      have hh := (div_lt_iff₀ hlow).mp hnhigh
      nlinarith
    have hcap : low * rate ^ (n + 1) ≤ rate * m := by
      have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hlow).mp hnlow) (by linarith : 0 ≤ rate)
      rw [pow_succ]
      nlinarith
    refine ⟨min high (low * rate ^ (n + 1)), ?_, le_min hm.2 hmcap.le,
      (min_le_right _ _).trans hcap⟩
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨n + 1, Finset.mem_range.mpr (by omega), rfl⟩

/-- A finite grid with the proved coverage exists for every nonempty positive cap interval. -/
theorem finite_grid_exists (low high rate : ℝ) (hlow : 0 < low) (hh : low ≤ high)
    (hrate : 1 < rate) :
    ∃ N : ℕ, high ≤ low * rate ^ N ∧
      ∀ m ∈ Set.Icc low high, ∃ cap ∈ grid low high rate N, m ≤ cap ∧ cap ≤ rate * m := by
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near ((le_div_iff₀ hlow).mpr (by simpa using hh)) hrate
  have hN : high ≤ low * rate ^ (n + 1) := by
    have hm := (div_lt_iff₀ hlow).mp hn
    nlinarith
  exact ⟨n + 1, hN, fun m hm ↦ grid_covers low high rate m (n + 1) hlow hrate hN hm⟩

/-- Every grid cap remains inside the prescribed finite interval. -/
theorem grid_mem_interval (low high rate : ℝ) (N : ℕ) (hlow : 0 ≤ low)
    (hh : low ≤ high) (hrate : 1 ≤ rate) (cap : ℝ) (hc : cap ∈ grid low high rate N) :
    cap ∈ Set.Icc low high := by
  classical
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact ⟨hh, le_refl _⟩
  · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hc
    have hn : 1 ≤ rate ^ n := one_le_pow₀ hrate
    have hl : low ≤ low * rate ^ n := by nlinarith
    exact ⟨le_min hh hl, min_le_left _ _⟩

/-- Increasing only the range cap by a factor loses at most that factor in the full radius. -/
theorem radius_factor (M cap v v' x rate : ℝ) (hx : 0 ≤ x) (hrate : 1 ≤ rate)
    (hcap : cap ≤ rate * M) (hv : v' ≤ v) :
    radius cap v' x ≤ rate * radius M v x := by
  have hs : Real.sqrt (2 * v' * x) ≤ Real.sqrt (2 * v * x) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hscale := mul_le_mul_of_nonneg_right hrate (Real.sqrt_nonneg (2 * v * x))
  have hr := mul_le_mul_of_nonneg_right hcap hx
  unfold radius
  nlinarith

variable {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J] [Nonempty J]

/-- A grid cap near any feasible design supplies a capped optimizer with the factor guarantee. -/
theorem grid_design_approximation (a : J → ι → ℝ) (floor c h p : ι → ℝ)
    (B x low high rate : ℝ) (N : ℕ) (hf : ∀ i, 0 < floor i) (hx : 0 ≤ x)
    (hlow : 0 < low) (hrate : 1 < rate) (hN : high ≤ low * rate ^ N)
    (hp : Feasible floor c B p) (hrange : maxRange h p ∈ Set.Icc low high) :
    ∃ cap ∈ grid low high rate N, ∃ q,
      Feasible (cappedFloor floor h cap) c B q ∧
      IsMinOn (worstVariance a) {r | Feasible (cappedFloor floor h cap) c B r} q ∧
      fullRadius a h q x ≤ rate * fullRadius a h p x := by
  obtain ⟨cap, hc, hmc, hcm⟩ := grid_covers low high rate (maxRange h p) N hlow hrate hN hrange
  have hcap : 0 < cap := (hlow.trans_le hrange.1).trans_le hmc
  have hpc := (capped_feasible_iff floor c h p B cap hf hcap).mpr ⟨hp, hmc⟩
  obtain ⟨q, hq, hmin⟩ := capped_optimum_exists a floor c h B cap hf ⟨p, hpc⟩
  have hqu := (capped_feasible_iff floor c h q B cap hf hcap).mp hq
  refine ⟨cap, hc, q, hq, hmin, ?_⟩
  exact (radius_mono _ cap _ _ x hqu.2 (le_refl _) hx).trans
    (radius_factor (maxRange h p) cap (worstVariance a p) (worstVariance a q) x rate
      hx hrate.le hcm (hmin hpc))

end Descent.Portability.GeometricAuditCaps

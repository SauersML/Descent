/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarginalTurnoverRegion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

assert_below Descent.Decision Descent.Program

/-!
# Extremal marginal-turnover laws charge at most `n+1` sign configurations

TQ Theorem 3.9 finishes with the claim that turns its identification region into
a finite algorithm: the minimum and the maximum of the objective on the
marginal-turnover polytope of `MarginalTurnoverRegion` are attained by joint
sign laws supported on at most `n+1` sign configurations, so enumerating
supports of that size and solving their linear constraints is exact. The proof
is the standard basic-feasible-solution argument, carried out here in full: a
support larger than `n+1` makes the moment vectors `(1, z)` linearly dependent,
the resulting null direction leaves normalisation and every one-locus mean
unchanged, optimality forces the objective to be flat along it, and moving until
one support probability reaches zero gives an optimum of strictly smaller
support.

## Empirical status

None. The bodies here are algebra and linear algebra: a weight vector on the sign
cube is the input, and every definition is its support or the moment vector of a
sign configuration. No definition names a measurable quantity or carries a fitted
constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarginalSupportBound

open Foundations TurnoverDependence MarginalTurnoverRegion

noncomputable section

variable {n : ℕ}

section SupportAndDirections

/-- The set of sign configurations a weight vector charges. -/
def support (n : ℕ) (p : (Fin n → Bool) → ℝ) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun z ↦ p z ≠ 0

/-- Membership in the support. -/
theorem mem_support_iff (p : (Fin n → Bool) → ℝ) (z : Fin n → Bool) :
    z ∈ support n p ↔ p z ≠ 0 := by
  rw [support, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ z, h⟩⟩

/-- The moment vector of a sign configuration: a one followed by its coordinates. These
are the columns of the polytope's constraint matrix. -/
def momentVector (n : ℕ) (z : Fin n → Bool) : Fin (n + 1) → ℝ :=
  Fin.cons 1 fun i ↦ sgn (z i)

/-- **More than `n+1` configurations carry a null direction** of the constraint matrix:
a nonzero signed perturbation with zero total mass and zero change in every one-locus
mean. -/
theorem exists_null_direction (T : Finset (Fin n → Bool)) (hT : n + 1 < T.card) :
    ∃ w : (Fin n → Bool) → ℝ, (∀ z, z ∉ T → w z = 0) ∧ (∃ z ∈ T, w z ≠ 0) ∧
      (∑ z, w z = 0) ∧ ∀ i, ∑ z, w z * sgn (z i) = 0 := by
  classical
  have hnli : ¬ LinearIndependent ℝ fun z : {x // x ∈ T} ↦
      momentVector n (z : Fin n → Bool) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnli
  obtain ⟨g, hg, z0, hz0⟩ := hnli
  refine ⟨fun z ↦ if h : z ∈ T then g ⟨z, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact dif_neg hz
  · refine ⟨(z0 : Fin n → Bool), z0.2, ?_⟩
    show (if h : (z0 : Fin n → Bool) ∈ T then g ⟨(z0 : Fin n → Bool), h⟩ else 0) ≠ 0
    rw [dif_pos z0.2]
    exact hz0
  · have hout : ∀ z : Fin n → Bool, z ∉ T → (if h : z ∈ T then g ⟨z, h⟩ else 0) = 0 :=
      fun z hz ↦ dif_neg hz
    rw [← Finset.sum_subset (Finset.subset_univ T) fun x _ hx ↦ hout x hx,
      ← Finset.sum_coe_sort T fun z ↦ if h : z ∈ T then g ⟨z, h⟩ else 0]
    have hval : ∀ z : {x // x ∈ T},
        (if h : (z : Fin n → Bool) ∈ T then g ⟨(z : Fin n → Bool), h⟩ else 0) = g z :=
      fun z ↦ dif_pos z.2
    rw [Finset.sum_congr rfl fun z _ ↦ hval z]
    have h0 := congrFun hg 0
    simpa [momentVector, Finset.sum_apply] using h0
  · intro i
    have hout : ∀ z : Fin n → Bool, z ∉ T →
        (if h : z ∈ T then g ⟨z, h⟩ else 0) * sgn (z i) = 0 := by
      intro z hz
      rw [dif_neg hz, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ T) fun x _ hx ↦ hout x hx,
      ← Finset.sum_coe_sort T fun z ↦ (if h : z ∈ T then g ⟨z, h⟩ else 0) * sgn (z i)]
    have hval : ∀ z : {x // x ∈ T},
        (if h : (z : Fin n → Bool) ∈ T then g ⟨(z : Fin n → Bool), h⟩ else 0)
            * sgn ((z : Fin n → Bool) i)
          = g z * sgn ((z : Fin n → Bool) i) := fun z ↦ by rw [dif_pos z.2]
    rw [Finset.sum_congr rfl fun z _ ↦ hval z]
    have hi := congrFun hg i.succ
    simpa [momentVector, Finset.sum_apply] using hi

end SupportAndDirections

section Perturbation

/-- Moving a feasible law along a null direction keeps it feasible while it stays
nonnegative.

Assumes: `MarginalFeasible n mrg p`, witnessed by `productSign_feasible`. -/
theorem perturb_feasible (mrg : Fin n → ℝ) (p w : (Fin n → Bool) → ℝ)
    (hp : MarginalFeasible n mrg p) (hwsum : ∑ z, w z = 0)
    (hwmarg : ∀ i, ∑ z, w z * sgn (z i) = 0) (c : ℝ) (hnn : ∀ z, 0 ≤ p z + c * w z) :
    MarginalFeasible n mrg fun z ↦ p z + c * w z := by
  refine ⟨hnn, ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2.1, hwsum, mul_zero, add_zero]
  · intro i
    have hrw : ∀ z : Fin n → Bool, (p z + c * w z) * sgn (z i)
        = p z * sgn (z i) + c * (w z * sgn (z i)) := fun z ↦ by ring
    rw [Finset.sum_congr rfl fun z _ ↦ hrw z, Finset.sum_add_distrib, ← Finset.mul_sum,
      hp.2.2 i, hwmarg i, mul_zero, add_zero]

/-- The objective moves linearly along a perturbation. -/
theorem perturb_objective (p w f : (Fin n → Bool) → ℝ) (c : ℝ) :
    ∑ z, (p z + c * w z) * f z = (∑ z, p z * f z) + c * ∑ z, w z * f z := by
  have hrw : ∀ z : Fin n → Bool, (p z + c * w z) * f z = p z * f z + c * (w z * f z) :=
    fun z ↦ by ring
  rw [Finset.sum_congr rfl fun z _ ↦ hrw z, Finset.sum_add_distrib, ← Finset.mul_sum]

end Perturbation

section SmallSupport

/-- **Support reduction at an optimum.**  A minimising feasible law can be replaced by a
minimising feasible law charging at most `n+1` sign configurations.

Assumes: `MarginalFeasible n mrg`, witnessed by `productSign_feasible`. -/
theorem exists_small_support_min (mrg : Fin n → ℝ) (f : (Fin n → Bool) → ℝ) :
    ∀ (N : ℕ) (p : (Fin n → Bool) → ℝ), (support n p).card ≤ N → MarginalFeasible n mrg p →
      (∀ q, MarginalFeasible n mrg q → ∑ z, p z * f z ≤ ∑ z, q z * f z) →
      ∃ p', MarginalFeasible n mrg p' ∧ (∑ z, p' z * f z) = ∑ z, p z * f z ∧
        (support n p').card ≤ n + 1
  | 0, p, hcard, hp, _ => by
      exfalso
      have hzero : ∀ z : Fin n → Bool, p z = 0 := by
        intro z
        by_contra hne
        have hmem : z ∈ support n p := (mem_support_iff p z).mpr hne
        have hpos := Finset.card_pos.mpr ⟨z, hmem⟩
        omega
      have hsum := hp.2.1
      rw [Finset.sum_congr rfl fun z _ ↦ hzero z] at hsum
      simp at hsum
  | N + 1, p, hcard, hp, hopt => by
      by_cases hsmall : (support n p).card ≤ n + 1
      · exact ⟨p, hp, rfl, hsmall⟩
      · push_neg at hsmall
        obtain ⟨w, hwout, ⟨z1, hz1T, hz1⟩, hwsum, hwmarg⟩ :=
          exists_null_direction (support n p) hsmall
        have hppos : ∀ z ∈ support n p, 0 < p z := fun z hz ↦
          lt_of_le_of_ne (hp.1 z) (Ne.symm ((mem_support_iff p z).mp hz))
        have hTne : (support n p).Nonempty := ⟨z1, hz1T⟩
        have hpzero : ∀ z : Fin n → Bool, z ∉ support n p → p z = 0 := by
          intro z hz
          by_contra hc
          exact hz ((mem_support_iff p z).mpr hc)
        set δ := (support n p).inf' hTne fun z ↦ p z / (1 + |w z|) with hδdef
        have hδpos : 0 < δ := by
          rw [hδdef, Finset.lt_inf'_iff]
          intro z hz
          exact div_pos (hppos z hz) (by positivity)
        have hbound : ∀ z : Fin n → Bool, δ * |w z| ≤ p z := by
          intro z
          by_cases hz : z ∈ support n p
          · have hle : δ ≤ p z / (1 + |w z|) := Finset.inf'_le _ hz
            rw [le_div_iff₀ (by positivity)] at hle
            nlinarith [abs_nonneg (w z), hδpos.le]
          · rw [hwout z hz, hpzero z hz]
            simp
        have hnn1 : ∀ z : Fin n → Bool, 0 ≤ p z + δ * w z := by
          intro z
          nlinarith [hbound z, neg_abs_le (w z), hδpos.le]
        have hnn2 : ∀ z : Fin n → Bool, 0 ≤ p z + (-δ) * w z := by
          intro z
          nlinarith [hbound z, le_abs_self (w z), hδpos.le]
        have hf1 := hopt _ (perturb_feasible mrg p w hp hwsum hwmarg δ hnn1)
        have hf2 := hopt _ (perturb_feasible mrg p w hp hwsum hwmarg (-δ) hnn2)
        rw [perturb_objective] at hf1 hf2
        have hrw : (-δ) * (∑ z, w z * f z) = -(δ * ∑ z, w z * f z) := by ring
        rw [hrw] at hf2
        have hprod : δ * (∑ z, w z * f z) = 0 := by linarith
        have hflat : ∑ z, w z * f z = 0 := by
          rcases mul_eq_zero.mp hprod with hc | hc
          · exact absurd hc (ne_of_gt hδpos)
          · exact hc
        have hneg : ∃ z ∈ support n p, w z < 0 := by
          by_contra hc
          push_neg at hc
          have hnn : ∀ z ∈ (Finset.univ : Finset (Fin n → Bool)), 0 ≤ w z := by
            intro z _
            by_cases hz : z ∈ support n p
            · exact hc z hz
            · rw [hwout z hz]
          exact hz1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hwsum z1 (Finset.mem_univ z1))
        set NegSet := (support n p).filter fun z ↦ w z < 0 with hNegdef
        have hNegne : NegSet.Nonempty := by
          obtain ⟨z, hzT, hzneg⟩ := hneg
          exact ⟨z, by rw [hNegdef, Finset.mem_filter]; exact ⟨hzT, hzneg⟩⟩
        set ε := NegSet.inf' hNegne fun z ↦ p z / (-w z) with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef, Finset.lt_inf'_iff]
          intro z hz
          rw [hNegdef, Finset.mem_filter] at hz
          exact div_pos (hppos z hz.1) (by linarith [hz.2])
        obtain ⟨zstar, hzstarmem, hzstareq⟩ :=
          Finset.exists_mem_eq_inf' hNegne fun z ↦ p z / (-w z)
        rw [hNegdef, Finset.mem_filter] at hzstarmem
        have hzstarT : zstar ∈ support n p := hzstarmem.1
        have hzstarneg : w zstar < 0 := hzstarmem.2
        have hc0 : (0 : ℝ) < -w zstar := by linarith
        have hzero : p zstar + ε * w zstar = 0 := by
          have h1 : ε * w zstar = -(p zstar) := by
            rw [hεdef, hzstareq, div_mul_eq_mul_div, eq_comm, eq_div_iff (ne_of_gt hc0)]
            ring
          rw [h1]
          ring
        have hnn' : ∀ z : Fin n → Bool, 0 ≤ p z + ε * w z := by
          intro z
          by_cases hz : z ∈ support n p
          · rcases le_or_gt 0 (w z) with hwz | hwz
            · nlinarith [hp.1 z, hεpos.le]
            · have hmem : z ∈ NegSet := by
                rw [hNegdef, Finset.mem_filter]
                exact ⟨hz, hwz⟩
              have hle : ε ≤ p z / (-w z) := by
                rw [hεdef]
                exact Finset.inf'_le _ hmem
              rw [le_div_iff₀ (by linarith)] at hle
              nlinarith
          · rw [hwout z hz, mul_zero, add_zero]
            exact hp.1 z
        have hp' : MarginalFeasible n mrg fun z ↦ p z + ε * w z :=
          perturb_feasible mrg p w hp hwsum hwmarg ε hnn'
        have hval : ∑ z, (p z + ε * w z) * f z = ∑ z, p z * f z := by
          rw [perturb_objective, hflat, mul_zero, add_zero]
        have hopt' : ∀ q, MarginalFeasible n mrg q →
            ∑ z, (p z + ε * w z) * f z ≤ ∑ z, q z * f z := by
          intro q hq
          rw [hval]
          exact hopt q hq
        have hsub : (support n fun z ↦ p z + ε * w z) ⊆ support n p := by
          intro z hz
          by_contra hcon
          have hzz : p z + ε * w z = 0 := by
            rw [hwout z hcon, hpzero z hcon, mul_zero, add_zero]
          exact ((mem_support_iff (fun z ↦ p z + ε * w z) z).mp hz) hzz
        have hstrict : (support n fun z ↦ p z + ε * w z) ⊂ support n p := by
          rw [Finset.ssubset_iff_of_subset hsub]
          refine ⟨zstar, hzstarT, ?_⟩
          rw [mem_support_iff]
          push_neg
          exact hzero
        have hcard' : (support n fun z ↦ p z + ε * w z).card ≤ N := by
          have hlt := Finset.card_lt_card hstrict
          omega
        obtain ⟨p'', hp'', hval'', hcard''⟩ :=
          exists_small_support_min mrg f N (fun z ↦ p z + ε * w z) hcard' hp' hopt'
        exact ⟨p'', hp'', hval''.trans hval, hcard''⟩

end SmallSupport

section Extrema

/-- Both extrema of a linear objective exist on the marginal-turnover polytope. -/
theorem feasible_extrema (mrg : Fin n → ℝ) (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1)
    (f : (Fin n → Bool) → ℝ) :
    ∃ pmin pmax : (Fin n → Bool) → ℝ, MarginalFeasible n mrg pmin ∧
      MarginalFeasible n mrg pmax ∧
      ∀ q, MarginalFeasible n mrg q →
        ∑ z, pmin z * f z ≤ ∑ z, q z * f z ∧ ∑ z, q z * f z ≤ ∑ z, pmax z * f z := by
  obtain ⟨lo, hi, hle, hset⟩ := linear_range_is_interval
    {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p}
    ⟨productSign n mrg, productSign_feasible n mrg hm⟩
    (marginalFeasible_isCompact n mrg) (marginalFeasible_convex n mrg) f
  have hlo : lo ∈ Set.Icc lo hi := Set.left_mem_Icc.mpr hle
  have hhi : hi ∈ Set.Icc lo hi := Set.right_mem_Icc.mpr hle
  rw [← hset] at hlo hhi
  obtain ⟨pmin, hpmin, hvmin⟩ := hlo
  obtain ⟨pmax, hpmax, hvmax⟩ := hhi
  refine ⟨pmin, pmax, hpmin, hpmax, fun q hq ↦ ?_⟩
  have hmem : (∑ z, q z * f z) ∈ Set.Icc lo hi := by
    rw [← hset]
    exact ⟨q, hq, rfl⟩
  rw [hvmin, hvmax]
  exact ⟨hmem.1, hmem.2⟩

/-- **TQ Theorem 3.9, the finite algorithm.**  Both extrema of a linear objective on the
marginal-turnover polytope are attained by joint sign laws charging at most `n+1` sign
configurations, so enumerating supports of that size is exact. -/
theorem extrema_small_support (mrg : Fin n → ℝ) (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1)
    (f : (Fin n → Bool) → ℝ) :
    ∃ pmin pmax : (Fin n → Bool) → ℝ, MarginalFeasible n mrg pmin ∧
      MarginalFeasible n mrg pmax ∧
      (support n pmin).card ≤ n + 1 ∧ (support n pmax).card ≤ n + 1 ∧
      ∀ q, MarginalFeasible n mrg q →
        ∑ z, pmin z * f z ≤ ∑ z, q z * f z ∧ ∑ z, q z * f z ≤ ∑ z, pmax z * f z := by
  obtain ⟨p0, q0, hp0, hq0, hopt⟩ := feasible_extrema mrg hm f
  have hneg : ∀ r : (Fin n → Bool) → ℝ, ∑ z, r z * (-f z) = -∑ z, r z * f z := by
    intro r
    have hrw : ∀ z : Fin n → Bool, r z * (-f z) = -(r z * f z) := fun z ↦ by ring
    rw [Finset.sum_congr rfl fun z _ ↦ hrw z, Finset.sum_neg_distrib]
  obtain ⟨pmin, hpmin, hvmin, hcmin⟩ :=
    exists_small_support_min mrg f (support n p0).card p0 le_rfl hp0 fun q hq ↦ (hopt q hq).1
  obtain ⟨pmax, hpmax, hvmax, hcmax⟩ :=
    exists_small_support_min mrg (fun z ↦ -f z) (support n q0).card q0 le_rfl hq0
      fun q hq ↦ by
        rw [hneg q0, hneg q]
        linarith [(hopt q hq).2]
  refine ⟨pmin, pmax, hpmin, hpmax, hcmin, hcmax, fun q hq ↦ ?_⟩
  constructor
  · rw [hvmin]
    exact (hopt q hq).1
  · have h1 : ∑ z, pmax z * (-f z) = ∑ z, q0 z * (-f z) := hvmax
    rw [hneg pmax, hneg q0] at h1
    have h2 : ∑ z, pmax z * f z = ∑ z, q0 z * f z := by linarith
    rw [h2]
    exact (hopt q hq).2

end Extrema

end

end Descent.Portability.MarginalSupportBound

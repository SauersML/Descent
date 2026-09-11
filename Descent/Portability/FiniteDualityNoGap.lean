/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportRegionCertificates
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

assert_below Descent.Decision Descent.Program

/-!
# No duality gap for a finite report bound

A dual certificate for the specified linear information is a multiplier on total mass
together with a potential for each specified summary, dominating the report statistic state
by state. Weak duality says every such certificate bounds every compatible law. This module
proves there is no gap: the attained maximum of the report statistic over the compatible laws
is the greatest lower bound of the dual certificate values, so a certificate exists within
any positive tolerance of the truth.

This closes the primal-dual equality of DC Theorem 2.1 (2.5)-(2.6) and PL Theorem 10.1
(10.4) in the finite setting. The proof avoids any closed-cone or Farkas import. The
constraint values and the report value of a law are read off as one point of a finite
coordinate space; the image of the standard simplex under that reading is compact and convex;
the target point, which carries the observed summaries, total mass one, and a report value
strictly above the attained maximum, is not in that image; separating it produces a
functional whose weight on the report coordinate is proved positive, and normalizing by that
weight turns the separating functional into a dual certificate of value below the tolerance.

Attainment of the dual minimum is not proved. The equality is stated as a greatest lower
bound, which is what the no-gap claim asserts; a minimizing certificate would need a vertex
argument on an unbounded dual polyhedron. The hypotheses are the manuscript's domain
conditions: the specified information is consistent, so a compatible law exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteDualityNoGap

open FiniteMetricIdentification

noncomputable section

variable {S O : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The value of a dual certificate: the multiplier on total mass plus the observed summaries
paired with their potentials. -/
def dualValue (observed : O → ℝ) (level : ℝ) (potential : O → ℝ) : ℝ :=
  level + pairing potential observed

/-- Weak duality including the total-mass row: a dual certificate bounds the report statistic
of every compatible law. -/
theorem le_dualValue (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ) (level : ℝ)
    (potential : O → ℝ)
    (hdual : ∀ s, metric s ≤ level + ∑ o, potential o * observe o s)
    (p : S → ℝ) (hp : p ∈ feasible observe observed) :
    pairing metric p ≤ dualValue observed level potential := by
  have hcross : ∑ s, ∑ o, potential o * observe o s * p s =
      ∑ o, potential o * pairing (observe o) p := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hsplit : ∑ s, (level + ∑ o, potential o * observe o s) * p s =
      level * (∑ s, p s) + ∑ o, potential o * pairing (observe o) p := by
    have hpoint : ∀ s : S, (level + ∑ o, potential o * observe o s) * p s =
        level * p s + ∑ o, potential o * observe o s * p s := by
      intro s
      rw [add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun s _ ↦ hpoint s, Finset.sum_add_distrib, ← Finset.mul_sum,
      hcross]
  have hfinal : level * (∑ s, p s) + ∑ o, potential o * pairing (observe o) p =
      dualValue observed level potential := by
    rw [hp.1.2, mul_one, dualValue, pairing]
    refine congrArg (fun x ↦ level + x) (Finset.sum_congr rfl fun o _ ↦ ?_)
    rw [hp.2 o]
  calc pairing metric p
      ≤ ∑ s, (level + ∑ o, potential o * observe o s) * p s :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right (hdual s) (hp.1.1 s)
    _ = level * (∑ s, p s) + ∑ o, potential o * pairing (observe o) p := hsplit
    _ = dualValue observed level potential := hfinal

/-- The law concentrated at a single state. -/
def pointVector (state : S) : S → ℝ := fun other ↦ if state = other then 1 else 0

/-- A point mass is a probability law. -/
theorem pointVector_mem_stdSimplex (state : S) : pointVector state ∈ stdSimplex ℝ S := by
  constructor
  · intro other
    by_cases h : state = other <;> simp [pointVector, h]
  · simp [pointVector]

/-- Pairing with a point mass evaluates the statistic at that state. -/
theorem pairing_pointVector (statistic : S → ℝ) (state : S) :
    pairing statistic (pointVector state) = statistic state := by
  simp [pairing, pointVector]

/-- A point mass has total mass one. -/
theorem sum_pointVector (state : S) : ∑ other, pointVector state other = 1 := by
  simp [pointVector]

/-- The constraint-and-objective coordinates of a law: its report value, its total mass, and
each of its specified summaries. -/
def dualityCoords (observe : O → S → ℝ) (metric : S → ℝ) (p : S → ℝ) :
    Option (Option O) → ℝ
  | none => pairing metric p
  | some none => ∑ s, p s
  | some (some o) => pairing (observe o) p

/-- The target point: a report value above the attained maximum, total mass one, and the
observed summaries. -/
def dualityTarget (observed : O → ℝ) (value : ℝ) : Option (Option O) → ℝ
  | none => value
  | some none => 1
  | some (some o) => observed o

/-- A sum over the doubly optioned index splits into its report term, its mass term, and its
summary terms. -/
theorem sum_option_option (summand : Option (Option O) → ℝ) :
    ∑ i, summand i =
      summand none + (summand (some none) + ∑ o, summand (some (some o))) := by
  rw [Fintype.sum_option, Fintype.sum_option]

/-- The coordinate reading is continuous. -/
theorem continuous_dualityCoords (observe : O → S → ℝ) (metric : S → ℝ) :
    Continuous (dualityCoords observe metric) := by
  refine continuous_pi fun i ↦ ?_
  rcases i with _ | i
  · exact continuous_pairing metric
  · rcases i with _ | o
    · exact continuous_finset_sum _ fun s _ ↦ continuous_apply s
    · exact continuous_pairing (observe o)

/-- The coordinate reading of the standard simplex is convex. -/
theorem convex_dualityImage (observe : O → S → ℝ) (metric : S → ℝ) :
    Convex ℝ (dualityCoords observe metric '' stdSimplex ℝ S) := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ a b ha hb hab
  refine ⟨a • p + b • q, convex_stdSimplex ℝ S hp hq ha hb hab, ?_⟩
  funext i
  rcases i with _ | i
  · show pairing metric (a • p + b • q) = _
    rw [pairing_add, pairing_smul, pairing_smul]
    rfl
  · rcases i with _ | o
    · show ∑ s, (a • p + b • q) s = _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    · show pairing (observe o) (a • p + b • q) = _
      rw [pairing_add, pairing_smul, pairing_smul]
      rfl

/-- The coordinate reading of the standard simplex is compact. -/
theorem isCompact_dualityImage (observe : O → S → ℝ) (metric : S → ℝ) :
    IsCompact (dualityCoords observe metric '' stdSimplex ℝ S) :=
  (isCompact_stdSimplex S).image (continuous_dualityCoords observe metric)

/-- A report value strictly above the attained maximum is unreachable. -/
theorem target_not_mem_dualityImage (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (p : S → ℝ)
    (hmax : ∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p)
    (eps : ℝ) (heps : 0 < eps) :
    dualityTarget observed (pairing metric p + eps) ∉
      dualityCoords observe metric '' stdSimplex ℝ S := by
  rintro ⟨q, hq, heq⟩
  have hmass := congrFun heq (some none)
  have hval := congrFun heq none
  have hobs : ∀ o, pairing (observe o) q = observed o := by
    intro o
    have := congrFun heq (some (some o))
    exact this
  have hqfeas : q ∈ feasible observe observed := ⟨hq, hobs⟩
  have hle := hmax q hqfeas
  have hvaleq : pairing metric q = pairing metric p + eps := hval
  linarith

/-- No duality gap: there is an attained maximizing compatible law, and for every positive
tolerance a dual certificate whose value is within that tolerance of the maximum. -/
theorem exists_dual_certificate_near (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (hne : (feasible observe observed).Nonempty) :
    ∃ p ∈ feasible observe observed,
      (∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p) ∧
        ∀ eps : ℝ, 0 < eps → ∃ (level : ℝ) (potential : O → ℝ),
          (∀ s, metric s ≤ level + ∑ o, potential o * observe o s) ∧
            dualValue observed level potential < pairing metric p + eps := by
  classical
  obtain ⟨p, hp, hmaxon⟩ := (feasible_compact observe observed).exists_isMaxOn hne
    (continuous_pairing metric).continuousOn
  have hmax : ∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p :=
    fun q hq ↦ hmaxon hq
  refine ⟨p, hp, hmax, ?_⟩
  intro eps heps
  obtain ⟨sep, lvl, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    (convex_dualityImage observe metric) (isCompact_dualityImage observe metric).isClosed
    (target_not_mem_dualityImage observe observed metric p hmax eps heps)
  obtain ⟨coef, hform⟩ : ∃ c : Option (Option O) → ℝ,
      ∀ x : Option (Option O) → ℝ, ∑ i, c i * x i = sep x := by
    refine ⟨fun i ↦ sep fun j ↦ if i = j then (1 : ℝ) else 0, fun x ↦ ?_⟩
    have hx := LinearMap.pi_apply_eq_sum_univ
      (sep : (Option (Option O) → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe] at hx
    rw [hx]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul]; ring
  have hsimplex : ∀ q ∈ stdSimplex ℝ S,
      coef none * pairing metric q +
        (coef (some none) * (∑ s, q s) +
          ∑ o, coef (some (some o)) * pairing (observe o) q) < lvl := by
    intro q hq
    have hmem := hlt (dualityCoords observe metric q) ⟨q, hq, rfl⟩
    rw [← hform (dualityCoords observe metric q),
      sum_option_option fun i ↦ coef i * dualityCoords observe metric q i] at hmem
    exact hmem
  have htarget : lvl < coef none * (pairing metric p + eps) +
      (coef (some none) * 1 + ∑ o, coef (some (some o)) * observed o) := by
    rw [← hform (dualityTarget observed (pairing metric p + eps)),
      sum_option_option
        fun i ↦ coef i * dualityTarget observed (pairing metric p + eps) i] at hgt
    exact hgt
  have hatp := hsimplex p hp.1
  rw [hp.1.2] at hatp
  have hobsp : ∑ o, coef (some (some o)) * pairing (observe o) p =
      ∑ o, coef (some (some o)) * observed o :=
    Finset.sum_congr rfl fun o _ ↦ by rw [hp.2 o]
  rw [hobsp] at hatp
  have hpos : 0 < coef none := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hatp, htarget]
  have hne0 : coef none ≠ 0 := ne_of_gt hpos
  refine ⟨(lvl - coef (some none)) / coef none,
    fun o ↦ -(coef (some (some o)) / coef none), ?_, ?_⟩
  · intro s
    have hat := hsimplex (pointVector s) (pointVector_mem_stdSimplex s)
    rw [pairing_pointVector, sum_pointVector, mul_one] at hat
    have hcoords : ∑ o, coef (some (some o)) * pairing (observe o) (pointVector s) =
        ∑ o, coef (some (some o)) * observe o s :=
      Finset.sum_congr rfl fun o _ ↦ by rw [pairing_pointVector]
    rw [hcoords] at hat
    have hrewrite : ∑ o, -(coef (some (some o)) / coef none) * observe o s =
        -((∑ o, coef (some (some o)) * observe o s) / coef none) := by
      rw [eq_neg_iff_add_eq_zero, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun o _ ↦ by ring
    rw [hrewrite, show (lvl - coef (some none)) / coef none +
        -((∑ o, coef (some (some o)) * observe o s) / coef none) =
        (lvl - coef (some none) - ∑ o, coef (some (some o)) * observe o s) / coef none
      from by ring, le_div_iff₀ hpos]
    nlinarith [hat]
  · have hrewrite : pairing (fun o ↦ -(coef (some (some o)) / coef none)) observed =
        -((∑ o, coef (some (some o)) * observed o) / coef none) := by
      rw [pairing, eq_neg_iff_add_eq_zero, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun o _ ↦ by ring
    rw [dualValue, hrewrite, show (lvl - coef (some none)) / coef none +
        -((∑ o, coef (some (some o)) * observed o) / coef none) =
        (lvl - coef (some none) - ∑ o, coef (some (some o)) * observed o) / coef none
      from by ring, div_lt_iff₀ hpos]
    nlinarith [htarget]

/-- DC (2.5) and PL (10.4) in the finite setting: the attained maximum of the report
statistic over the compatible laws is exactly the greatest lower bound of the dual
certificate values, so the primal and dual optima agree. -/
theorem isGLB_dualValue (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ)
    (hne : (feasible observe observed).Nonempty) :
    ∃ p ∈ feasible observe observed,
      (∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p) ∧
        IsGLB {value : ℝ | ∃ (level : ℝ) (potential : O → ℝ),
          (∀ s, metric s ≤ level + ∑ o, potential o * observe o s) ∧
            value = dualValue observed level potential} (pairing metric p) := by
  obtain ⟨p, hp, hmax, hnear⟩ := exists_dual_certificate_near observe observed metric hne
  refine ⟨p, hp, hmax, ?_, ?_⟩
  · rintro value ⟨level, potential, hdual, rfl⟩
    exact le_dualValue observe observed metric level potential hdual p hp
  · intro bound hbound
    by_contra hcon
    push_neg at hcon
    obtain ⟨level, potential, hdual, hvalue⟩ := hnear (bound - pairing metric p) (by linarith)
    have hmem : dualValue observed level potential ∈
        {value : ℝ | ∃ (level : ℝ) (potential : O → ℝ),
          (∀ s, metric s ≤ level + ∑ o, potential o * observe o s) ∧
            value = dualValue observed level potential} :=
      ⟨level, potential, hdual, rfl⟩
    have := hbound hmem
    linarith

/-- DC (2.5) and PL (10.4) as the manuscript states them, for a linear contrast of the
attainable report region: the attained maximum of the contrast over the region equals the
greatest lower bound of the values of its dual certificates. -/
theorem isGLB_dualValue_reportRegion {J : Type*} [Fintype J] (observe : O → S → ℝ)
    (observed : O → ℝ) (reportTable : J → S → ℝ) (contrast : J → ℝ)
    (hne : (feasible observe observed).Nonempty) :
    ∃ r ∈ ReportRegionCertificates.reportRegion observe observed reportTable,
      (∀ r' ∈ ReportRegionCertificates.reportRegion observe observed reportTable,
          pairing contrast r' ≤ pairing contrast r) ∧
        IsGLB {value : ℝ | ∃ (level : ℝ) (potential : O → ℝ),
          (∀ s, ∑ j, contrast j * reportTable j s ≤
              level + ∑ o, potential o * observe o s) ∧
            value = dualValue observed level potential} (pairing contrast r) := by
  obtain ⟨p, hp, hmax, hglb⟩ :=
    isGLB_dualValue observe observed (fun s ↦ ∑ j, contrast j * reportTable j s) hne
  refine ⟨fun j ↦ pairing (reportTable j) p, ⟨p, hp, rfl⟩, ?_, ?_⟩
  · rintro r' ⟨q, hq, rfl⟩
    rw [ReportRegionCertificates.pairing_contrast_reportRegion,
      ReportRegionCertificates.pairing_contrast_reportRegion]
    exact hmax q hq
  · rw [ReportRegionCertificates.pairing_contrast_reportRegion]
    exact hglb

end

end Descent.Portability.FiniteDualityNoGap

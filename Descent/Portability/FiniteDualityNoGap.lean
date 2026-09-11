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

Dual attainment is proved separately, under an interior condition on the specified
information: every summary vector within a fixed radius of the observed one is attainable by
some probability law. That condition makes the certificates of bounded value uniformly
bounded, because testing dual feasibility against the laws realizing the nearby summary
vectors bounds each potential, so the bounded dual certificates form a compact set and the
infimum is a minimum. The condition is not vacuous: a two-state space reporting the mass of
one state satisfies it, and that witness is proved here.

The hypotheses are the manuscript's domain conditions. The no-gap equality needs only that
the specified information is consistent, so a compatible law exists; the interior condition
is needed only for attainment, and every statement says which of the two it uses.
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

/-- Dual feasibility bounds the report value of every probability law by the certificate's
level plus its potentials paired with that law's own summaries. -/
theorem le_dual_at_law (observe : O → S → ℝ) (metric : S → ℝ) (level : ℝ)
    (potential : O → ℝ)
    (hdual : ∀ s, metric s ≤ level + ∑ o, potential o * observe o s)
    (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S) :
    pairing metric q ≤ level + ∑ o, potential o * pairing (observe o) q := by
  have hcross : ∑ s, ∑ o, potential o * observe o s * q s =
      ∑ o, potential o * pairing (observe o) q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hsplit : ∑ s, (level + ∑ o, potential o * observe o s) * q s =
      level * (∑ s, q s) + ∑ o, potential o * pairing (observe o) q := by
    have hpoint : ∀ s : S, (level + ∑ o, potential o * observe o s) * q s =
        level * q s + ∑ o, potential o * observe o s * q s := by
      intro s
      rw [add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun s _ ↦ hpoint s, Finset.sum_add_distrib, ← Finset.mul_sum,
      hcross]
  calc pairing metric q
      ≤ ∑ s, (level + ∑ o, potential o * observe o s) * q s :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_right (hdual s) (hq.1 s)
    _ = level * (∑ s, q s) + ∑ o, potential o * pairing (observe o) q := hsplit
    _ = level + ∑ o, potential o * pairing (observe o) q := by rw [hq.2, mul_one]

/-- Weak duality including the total-mass row: a dual certificate bounds the report statistic
of every compatible law. -/
theorem le_dualValue (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ) (level : ℝ)
    (potential : O → ℝ)
    (hdual : ∀ s, metric s ≤ level + ∑ o, potential o * observe o s)
    (p : S → ℝ) (hp : p ∈ feasible observe observed) :
    pairing metric p ≤ dualValue observed level potential := by
  refine le_trans (le_dual_at_law observe metric level potential hdual p hp.1) (le_of_eq ?_)
  rw [dualValue, pairing]
  exact congrArg (fun x ↦ level + x) (Finset.sum_congr rfl fun o _ ↦ by rw [hp.2 o])

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

/-- Every probability law's report value is bounded below by the total size of the
statistic, with no reference to any minimiser. -/
theorem neg_sum_abs_le_pairing (metric : S → ℝ) (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S) :
    -(∑ s, |metric s|) ≤ pairing metric q := by
  have hle : ∀ s : S, q s ≤ 1 := by
    intro s
    have hsingle := Finset.single_le_sum (f := q) (fun t _ ↦ hq.1 t) (Finset.mem_univ s)
    rw [hq.2] at hsingle
    exact hsingle
  have hterm : ∀ s : S, -|metric s| ≤ metric s * q s := by
    intro s
    rcases le_or_gt 0 (metric s) with hm | hm
    · rw [abs_of_nonneg hm]
      nlinarith [hq.1 s]
    · rw [abs_of_neg hm]
      nlinarith [hle s]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (f := fun s ↦ -|metric s|) (g := fun s ↦ metric s * q s) fun s _ ↦ hterm s
  simpa [pairing] using hsum

/-- Under the interior condition, the potentials of every dual certificate of bounded value
are bounded, uniformly in the certificate. -/
theorem abs_potential_le (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hslater : ∀ d : O → ℝ, (∀ o, |d o| ≤ radius) →
      ∃ q ∈ stdSimplex ℝ S, ∀ o, pairing (observe o) q = observed o + d o)
    (bound level : ℝ) (potential : O → ℝ)
    (hdual : ∀ s, metric s ≤ level + ∑ o, potential o * observe o s)
    (hvalue : dualValue observed level potential ≤ bound) (target : O) :
    |potential target| ≤ (|bound| + ∑ s, |metric s|) / radius := by
  classical
  have hstep : ∀ sign : ℝ, |sign| = 1 →
      -(∑ s, |metric s|) ≤ bound + potential target * (sign * radius) := by
    intro sign hsign
    obtain ⟨q, hq, hqsum⟩ :=
      hslater (fun o ↦ if o = target then sign * radius else 0) (by
        intro o
        show |(if o = target then sign * radius else 0)| ≤ radius
        by_cases ho : o = target
        · rw [if_pos ho, abs_mul, hsign, one_mul, abs_of_pos hradius]
        · rw [if_neg ho, abs_zero]
          linarith)
    have hle := le_dual_at_law observe metric level potential hdual q hq
    have hexpand : ∑ o, potential o * pairing (observe o) q =
        (∑ o, potential o * observed o) + potential target * (sign * radius) := by
      have hpoint : ∀ o : O, potential o * pairing (observe o) q =
          potential o * observed o +
            potential o * (if o = target then sign * radius else 0) := by
        intro o
        rw [hqsum o]
        ring
      rw [Finset.sum_congr rfl fun o _ ↦ hpoint o, Finset.sum_add_distrib]
      refine congrArg (fun x ↦ (∑ o, potential o * observed o) + x) ?_
      rw [Finset.sum_eq_single target]
      · rw [if_pos rfl]
      · intro o _ ho
        rw [if_neg ho, mul_zero]
      · intro hno
        exact absurd (Finset.mem_univ target) hno
    have hlow := neg_sum_abs_le_pairing metric q hq
    have hval : dualValue observed level potential =
        level + ∑ o, potential o * observed o := by rw [dualValue, pairing]
    rw [hexpand] at hle
    linarith
  have h1 := hstep 1 (by norm_num)
  have h2 := hstep (-1) (by norm_num)
  have habs := le_abs_self bound
  have hup : potential target * radius ≤ |bound| + ∑ s, |metric s| := by nlinarith [h2]
  have hdown : -potential target * radius ≤ |bound| + ∑ s, |metric s| := by nlinarith [h1]
  rw [abs_le]
  refine ⟨?_, (le_div_iff₀ hradius).2 hup⟩
  rw [neg_le, le_div_iff₀ hradius]
  linarith

/-- The dual certificates whose value is at most a given bound. -/
def boundedDualSet (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ) (bound : ℝ) :
    Set (ℝ × (O → ℝ)) :=
  {z | ∀ s, metric s ≤ z.1 + ∑ o, z.2 o * observe o s} ∩
    {z | dualValue observed z.1 z.2 ≤ bound}

/-- The dual feasibility expression at a state is continuous in the certificate. -/
theorem continuous_dualExpr (observe : O → S → ℝ) (s : S) :
    Continuous fun z : ℝ × (O → ℝ) ↦ z.1 + ∑ o, z.2 o * observe o s :=
  continuous_fst.add (continuous_finset_sum _ fun o _ ↦
    ((continuous_apply o).comp continuous_snd).mul continuous_const)

/-- The dual value is continuous in the certificate. -/
theorem continuous_dualValueProd (observed : O → ℝ) :
    Continuous fun z : ℝ × (O → ℝ) ↦ dualValue observed z.1 z.2 :=
  continuous_fst.add (continuous_finset_sum _ fun o _ ↦
    ((continuous_apply o).comp continuous_snd).mul continuous_const)

/-- The bounded dual set is closed. -/
theorem isClosed_boundedDualSet (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ)
    (bound : ℝ) : IsClosed (boundedDualSet observe observed metric bound) := by
  refine IsClosed.inter ?_ (isClosed_le (continuous_dualValueProd observed) continuous_const)
  have hrw : {z : ℝ × (O → ℝ) | ∀ s, metric s ≤ z.1 + ∑ o, z.2 o * observe o s} =
      ⋂ s : S, {z : ℝ × (O → ℝ) | metric s ≤ z.1 + ∑ o, z.2 o * observe o s} := by
    ext z
    simp
  rw [hrw]
  exact isClosed_iInter fun s ↦ isClosed_le continuous_const (continuous_dualExpr observe s)

/-- Under the interior condition the bounded dual set is compact, so a minimising certificate
exists inside it. -/
theorem isCompact_boundedDualSet (observe : O → S → ℝ) (observed : O → ℝ) (metric : S → ℝ)
    (radius : ℝ) (hradius : 0 < radius)
    (hslater : ∀ d : O → ℝ, (∀ o, |d o| ≤ radius) →
      ∃ q ∈ stdSimplex ℝ S, ∀ o, pairing (observe o) q = observed o + d o)
    (bound : ℝ) : IsCompact (boundedDualSet observe observed metric bound) := by
  classical
  obtain ⟨base, hbase, hbasesum⟩ := hslater (fun _ ↦ 0) (fun _ ↦ by simpa using hradius.le)
  set potBound : ℝ := (|bound| + ∑ s, |metric s|) / radius with hpotBound
  have hpotNonneg : 0 ≤ potBound := by
    refine div_nonneg ?_ hradius.le
    have : (0 : ℝ) ≤ ∑ s, |metric s| := Finset.sum_nonneg fun s _ ↦ abs_nonneg _
    linarith [abs_nonneg bound]
  set levelBound : ℝ :=
    |bound| + (∑ s, |metric s|) + potBound * ∑ o, |observed o| with hlevelBound
  refine IsCompact.of_isClosed_subset
    (IsCompact.prod (isCompact_Icc (a := -levelBound) (b := levelBound))
      (isCompact_univ_pi fun _ : O ↦ isCompact_Icc (a := -potBound) (b := potBound)))
    (isClosed_boundedDualSet observe observed metric bound) ?_
  rintro ⟨level, potential⟩ ⟨hdual, hvalue⟩
  simp only [Set.mem_setOf_eq] at hdual hvalue
  have hpot : ∀ o, |potential o| ≤ potBound := fun o ↦
    abs_potential_le observe observed metric radius hradius hslater bound level potential
      hdual hvalue o
  have hcross : |∑ o, potential o * observed o| ≤ potBound * ∑ o, |observed o| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun o _ ↦ ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hpot o) (abs_nonneg _)
  have hcrossbounds := abs_le.1 hcross
  have hval : dualValue observed level potential =
      level + ∑ o, potential o * observed o := by rw [dualValue, pairing]
  have hbaselow := neg_sum_abs_le_pairing metric base hbase
  have hbasedual := le_dual_at_law observe metric level potential hdual base hbase
  have hbaseobs : ∑ o, potential o * pairing (observe o) base =
      ∑ o, potential o * observed o :=
    Finset.sum_congr rfl fun o _ ↦ by rw [hbasesum o]; ring
  rw [hbaseobs] at hbasedual
  have habsb := le_abs_self bound
  have hsumnn : (0 : ℝ) ≤ ∑ s, |metric s| := Finset.sum_nonneg fun s _ ↦ abs_nonneg _
  constructor
  · simp only [Set.mem_Icc]
    constructor
    · rw [hlevelBound]
      linarith [hcrossbounds.2, abs_nonneg bound]
    · rw [hlevelBound]
      linarith [hcrossbounds.1]
  · refine Set.mem_univ_pi.2 fun o ↦ ?_
    exact Set.mem_Icc.2 (abs_le.1 (hpot o))

/-- Dual attainment under the interior condition: the attained primal maximum is attained by
a dual certificate as well, so the no-gap equality of DC (2.5) and PL (10.4) is a genuine
maximum equal to a genuine minimum. -/
theorem exists_optimal_dual_certificate (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (radius : ℝ) (hradius : 0 < radius)
    (hslater : ∀ d : O → ℝ, (∀ o, |d o| ≤ radius) →
      ∃ q ∈ stdSimplex ℝ S, ∀ o, pairing (observe o) q = observed o + d o) :
    ∃ p ∈ feasible observe observed,
      (∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p) ∧
        ∃ (level : ℝ) (potential : O → ℝ),
          (∀ s, metric s ≤ level + ∑ o, potential o * observe o s) ∧
            dualValue observed level potential = pairing metric p ∧
            ∀ other : ℝ × (O → ℝ),
              (∀ s, metric s ≤ other.1 + ∑ o, other.2 o * observe o s) →
                dualValue observed level potential ≤ dualValue observed other.1 other.2 := by
  classical
  obtain ⟨base, hbase, hbasesum⟩ := hslater (fun _ ↦ 0) (fun _ ↦ by simpa using hradius.le)
  have hne : (feasible observe observed).Nonempty := by
    refine ⟨base, hbase, fun o ↦ ?_⟩
    rw [hbasesum o, add_zero]
  obtain ⟨p, hp, hmax, hnear⟩ := exists_dual_certificate_near observe observed metric hne
  obtain ⟨level0, potential0, hdual0, hvalue0⟩ := hnear 1 one_pos
  have hmemK : (level0, potential0) ∈
      boundedDualSet observe observed metric (pairing metric p + 1) :=
    ⟨hdual0, le_of_lt hvalue0⟩
  obtain ⟨z, hz, hminon⟩ :=
    (isCompact_boundedDualSet observe observed metric radius hradius hslater
      (pairing metric p + 1)).exists_isMinOn ⟨_, hmemK⟩
      (continuous_dualValueProd observed).continuousOn
  have hmin : ∀ w ∈ boundedDualSet observe observed metric (pairing metric p + 1),
      dualValue observed z.1 z.2 ≤ dualValue observed w.1 w.2 := fun w hw ↦ hminon hw
  have hge : pairing metric p ≤ dualValue observed z.1 z.2 :=
    le_dualValue observe observed metric z.1 z.2 hz.1 p hp
  have hle : dualValue observed z.1 z.2 ≤ pairing metric p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨level, potential, hdual, hvalue⟩ :=
      hnear (min ((dualValue observed z.1 z.2 - pairing metric p) / 2) (1 / 2))
        (lt_min (by linarith) (by norm_num))
    have hsmall : min ((dualValue observed z.1 z.2 - pairing metric p) / 2) (1 / 2) ≤
        (dualValue observed z.1 z.2 - pairing metric p) / 2 := min_le_left _ _
    have hhalf : min ((dualValue observed z.1 z.2 - pairing metric p) / 2) (1 / 2) ≤ 1 / 2 :=
      min_le_right _ _
    have hmemw : (level, potential) ∈
        boundedDualSet observe observed metric (pairing metric p + 1) := by
      refine ⟨hdual, ?_⟩
      show dualValue observed level potential ≤ pairing metric p + 1
      linarith
    have := hmin (level, potential) hmemw
    linarith
  refine ⟨p, hp, hmax, z.1, z.2, hz.1, le_antisymm hle hge, fun other hother ↦ ?_⟩
  by_cases hmemother : dualValue observed other.1 other.2 ≤ pairing metric p + 1
  · exact hmin other ⟨hother, hmemother⟩
  · push_neg at hmemother
    linarith [le_antisymm hle hge]

/-- The interior condition is satisfiable: a two-state space reporting the mass of one state
admits every observed value in the middle half, so the hypothesis of dual attainment is not
vacuous. -/
theorem slater_witness :
    ∀ d : Unit → ℝ, (∀ o, |d o| ≤ (1 : ℝ) / 4) →
      ∃ q ∈ stdSimplex ℝ Bool,
        ∀ o : Unit, pairing (fun s : Bool ↦ if s then (1 : ℝ) else 0) q =
          (fun _ : Unit ↦ (1 : ℝ) / 2) o + d o := by
  intro d hd
  have hbound := abs_le.1 (hd ())
  refine ⟨fun s ↦ if s then 1 / 2 + d () else 1 / 2 - d (), ⟨fun s ↦ ?_, ?_⟩, fun o ↦ ?_⟩
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      linarith [hbound.2]
    · simp only [if_true]
      linarith [hbound.1]
  · simp [Fintype.sum_bool]
    ring
  · simp [pairing, Fintype.sum_bool]

end

end Descent.Portability.FiniteDualityNoGap

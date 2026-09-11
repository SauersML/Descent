/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AngularExtremalReports
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

assert_below Descent.Decision Descent.Program

/-!
# The exact joint feasible region of coupled reports

PL Theorem 9.3 describes the set of pairs (supplied features, calculated reports) achievable by
some law on the valid states, when both are computed from the same state.  This module proves it
over a finite state set, which is the regime PL Section 10 actually evaluates: a finite record
kernel.

`report_region_eq_convexHull` is the boxed identity PL (9.5): the achievable expectations are
exactly the convex hull of the pointwise values.  Both inclusions are proved, the forward one
because an expectation is a convex combination and the reverse one because the achievable set is
itself convex and contains every pointwise value.  Nothing about the split between features and
reports is used, which is the point of the theorem: the coupling is preserved because both
blocks are read off the same state.

`report_region_finite_support` is the finite-witness clause: every achievable point is realized
by a law on at most `N + 1` states with strictly positive weights, where `N` is the total number
of scalar coordinates, that is the manuscript's `m + r + 1` bound.  It is Carathéodory's theorem
plus the cardinality bound for an affinely independent family.

`dual_certificate` is the inequality half of PL (9.6): any multiplier vector together with any
pointwise bound on the Lagrangian is an explicit certificate for an upper bound on the report,
valid for every feasible law.  The manuscript emphasizes exactly this reading, that a pointwise
inequality is a verifiable certificate rather than a plug-in estimate.

The equality of values in PL (9.6), and the primal attainment statement, are proved in the
companion results below when the feasible set is nonempty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.JointReportFeasibility

open Foundations CohortEvaluationOperators

noncomputable section

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N m : ℕ}

/-- The expectation of a vector-valued report under a finite law on the states. -/
def reportExpectation (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (g : Ω → Fin N → ℝ) : Fin N → ℝ :=
  fun j ↦ weightedExp p hp hs (fun ω ↦ g ω j)

omit [DecidableEq Ω] in
/-- Each coordinate of the report expectation is the corpus weighted expectation. -/
theorem reportExpectation_apply (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (g : Ω → Fin N → ℝ) (j : Fin N) :
    reportExpectation p hp hs g j = weightedExp p hp hs (fun ω ↦ g ω j) := rfl

omit [DecidableEq Ω] in
/-- The report expectation is the convex combination of the pointwise values. -/
theorem reportExpectation_eq_sum (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (g : Ω → Fin N → ℝ) : reportExpectation p hp hs g = ∑ ω, p ω • g ω := by
  funext j
  rw [reportExpectation, weightedExp_apply]
  simp [Finset.sum_apply]

/-- **PL (9.5), the exact joint feasible region.**  The achievable pairs of supplied features and
calculated reports are exactly the convex hull of the pointwise values.  No independence between
the two blocks is assumed or introduced: both are read off the same state, and the convex hull
of the coupled image is generally smaller than the product of the separate hulls. -/
theorem report_region_eq_convexHull (g : Ω → Fin N → ℝ) :
    {y : Fin N → ℝ | ∃ (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1),
        y = reportExpectation p hp hs g}
      = convexHull ℝ (Set.range g) := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, hs, rfl⟩
    rw [reportExpectation_eq_sum]
    refine Convex.sum_mem (convex_convexHull ℝ _) (fun ω _ ↦ hp ω) hs fun ω _ ↦ ?_
    exact subset_convexHull ℝ _ (Set.mem_range_self ω)
  · refine convexHull_min ?_ ?_
    · rintro y ⟨ω₀, rfl⟩
      refine ⟨fun ω ↦ if ω = ω₀ then 1 else 0, fun ω ↦ ?_, ?_, ?_⟩
      · by_cases hω : ω = ω₀ <;> simp [hω]
      · simp
      · funext j
        rw [reportExpectation, weightedExp_apply]
        simp
    · rintro y₁ ⟨p₁, hp₁, hs₁, rfl⟩ y₂ ⟨p₂, hp₂, hs₂, rfl⟩ a b ha hb hab
      refine ⟨fun ω ↦ a * p₁ ω + b * p₂ ω,
        fun ω ↦ add_nonneg (mul_nonneg ha (hp₁ ω)) (mul_nonneg hb (hp₂ ω)), ?_, ?_⟩
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs₁, hs₂, mul_one,
          mul_one, hab]
      · funext j
        simp only [reportExpectation, weightedExp_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ω _ ↦ by ring

omit [Fintype Ω] [DecidableEq Ω] in
/-- **PL (9.5), the finite-witness clause.**  Every achievable point of the joint region is
realized by a law on at most `N + 1` states, all with strictly positive weight.  With the
features in the first block and the reports in the second this is the manuscript's `m + r + 1`
bound. -/
theorem report_region_finite_support (g : Ω → Fin N → ℝ) (y : Fin N → ℝ)
    (hy : y ∈ convexHull ℝ (Set.range g)) :
    ∃ (ι : Type) (_ : Fintype ι) (z : ι → Fin N → ℝ) (w : ι → ℝ),
      Set.range z ⊆ Set.range g ∧ Fintype.card ι ≤ N + 1 ∧ (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = y := by
  obtain ⟨ι, hfin, z, w, hzs, haff, hwpos, hwsum, hweq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  refine ⟨ι, hfin, z, w, hzs, ?_, hwpos, hwsum, hweq⟩
  have hcard := AffineIndependent.card_le_finrank_succ haff
  have hle : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ N := by
    have hsub := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    rwa [Module.finrank_fin_fun (R := ℝ)] at hsub
  omega

omit [DecidableEq Ω] in
/-- **PL (9.6), the certificate inequality.**  A multiplier vector together with a pointwise
bound on the Lagrangian bounds the report of every feasible law.  This is what makes the dual
side of PL (9.6) a verifiable certificate rather than an unverified plug-in estimate: the
hypotheses are finitely many scalar inequalities, one per state. -/
theorem dual_certificate (h : Ω → Fin m → ℝ) (f : Ω → ℝ) (c lam : Fin m → ℝ) (bound : ℝ)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1)
    (hfeas : ∀ j, weightedExp p hp hs (fun ω ↦ h ω j) = c j)
    (hbound : ∀ ω, f ω - dot lam (h ω) ≤ bound) :
    weightedExp p hp hs f ≤ dot lam c + bound := by
  have hlag : weightedExp p hp hs (fun ω ↦ f ω - dot lam (h ω)) ≤ bound := by
    have hle := (weightedExp p hp hs).eval_mono
      (f := fun ω ↦ f ω - dot lam (h ω)) (g := fun _ ↦ bound) hbound
    rwa [ExpFunctional.eval_const] at hle
  have hsplit : weightedExp p hp hs (fun ω ↦ f ω - dot lam (h ω))
      = weightedExp p hp hs f - dot lam c := by
    have hexp : weightedExp p hp hs (fun ω ↦ dot lam (h ω)) = dot lam c := by
      have hlhs : weightedExp p hp hs (fun ω ↦ dot lam (h ω))
          = ∑ i, lam i * ∑ ω, p ω * h ω i := by
        simp only [weightedExp_apply, dot, Descent.Core.innerSum, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [hlhs]
      show ∑ i, lam i * ∑ ω, p ω * h ω i = ∑ i, lam i * c i
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← hfeas i, weightedExp_apply]
    rw [← hexp]
    simp only [weightedExp_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ by ring
  linarith [hsplit ▸ hlag]

/-! ## PL (9.6): the exact value of the dual -/

omit [DecidableEq Ω] in
/-- Negation distributes over a finite sum. -/
theorem neg_finset_sum {ι : Type*} [Fintype ι] (F : ι → ℝ) : -(∑ i, F i) = ∑ i, -(F i) := by
  simp

/-- **PL (9.5) in a general real vector space.**  The achievable expectations of a
vector-valued observable are exactly the convex hull of its pointwise values.  The version for
`Fin N → ℝ` above is this statement read coordinatewise. -/
theorem region_eq_convexHull_of_module {E : Type*} [AddCommGroup E] [Module ℝ E] (g : Ω → E) :
    {y : E | ∃ (p : Ω → ℝ) (_ : ∀ ω, 0 ≤ p ω) (_ : ∑ ω, p ω = 1), y = ∑ ω, p ω • g ω}
      = convexHull ℝ (Set.range g) := by
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, hs, rfl⟩
    refine Convex.sum_mem (convex_convexHull ℝ _) (fun ω _ ↦ hp ω) hs fun ω _ ↦ ?_
    exact subset_convexHull ℝ _ (Set.mem_range_self ω)
  · refine convexHull_min ?_ ?_
    · rintro y ⟨ω₀, rfl⟩
      refine ⟨fun ω ↦ if ω = ω₀ then 1 else 0, fun ω ↦ ?_, ?_, ?_⟩
      · by_cases hω : ω = ω₀ <;> simp [hω]
      · simp
      · simp
    · rintro y₁ ⟨p₁, hp₁, hs₁, rfl⟩ y₂ ⟨p₂, hp₂, hs₂, rfl⟩ a b ha hb hab
      refine ⟨fun ω ↦ a * p₁ ω + b * p₂ ω,
        fun ω ↦ add_nonneg (mul_nonneg ha (hp₁ ω)) (mul_nonneg hb (hp₂ ω)), ?_, ?_⟩
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs₁, hs₂, mul_one,
          mul_one, hab]
      · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [smul_smul, smul_smul, add_smul]

/-- The state's supplied features paired with its scalar report, both read off the same state. -/
def featureReportPair (h : Ω → Fin m → ℝ) (f : Ω → ℝ) : Ω → (Fin m → ℝ) × ℝ :=
  fun ω ↦ (h ω, f ω)

/-- The report values achievable by a law matching the prescribed supplied features. -/
def primalValues (h : Ω → Fin m → ℝ) (f : Ω → ℝ) (c : Fin m → ℝ) : Set ℝ :=
  {t : ℝ | ∃ (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1),
    (∀ j, weightedExp p hp hs (fun ω ↦ h ω j) = c j) ∧ t = weightedExp p hp hs f}

/-- The values of the dual objective of PL (9.6), one for each multiplier vector. -/
def dualValues (h : Ω → Fin m → ℝ) (f : Ω → ℝ) (c : Fin m → ℝ)
    (hΩ : (Finset.univ : Finset Ω).Nonempty) : Set ℝ :=
  {v : ℝ | ∃ lam : Fin m → ℝ,
    v = dot lam c + Finset.univ.sup' hΩ fun ω ↦ f ω - dot lam (h ω)}

omit [DecidableEq Ω] in
/-- The primal achievable values form a compact set: the feasible laws are a closed subset of
the standard simplex, and the report is a continuous function of the law. -/
theorem isCompact_primalValues (h : Ω → Fin m → ℝ) (f : Ω → ℝ) (c : Fin m → ℝ) :
    IsCompact (primalValues h f c) := by
  have hcont : ∀ F : Ω → ℝ, Continuous fun p : Ω → ℝ ↦ ∑ ω, p ω * F ω := by
    intro F
    exact continuous_finset_sum _ fun ω _ ↦ (continuous_apply ω).mul continuous_const
  have hclosed : IsClosed {p : Ω → ℝ | ∀ j, ∑ ω, p ω * h ω j = c j} := by
    have hset : {p : Ω → ℝ | ∀ j, ∑ ω, p ω * h ω j = c j}
        = ⋂ j, {p : Ω → ℝ | ∑ ω, p ω * h ω j = c j} := by
      ext p
      simp [Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter fun j ↦ isClosed_eq (hcont fun ω ↦ h ω j) continuous_const
  have himage : primalValues h f c
      = (fun p : Ω → ℝ ↦ ∑ ω, p ω * f ω) ''
          (stdSimplex ℝ Ω ∩ {p : Ω → ℝ | ∀ j, ∑ ω, p ω * h ω j = c j}) := by
    ext t
    constructor
    · rintro ⟨p, hp, hs, hfe, rfl⟩
      refine ⟨p, ⟨⟨hp, hs⟩, fun j ↦ ?_⟩, rfl⟩
      rw [← hfe j, weightedExp_apply]
    · rintro ⟨p, ⟨⟨hp, hs⟩, hfe⟩, rfl⟩
      exact ⟨p, hp, hs, fun j ↦ by rw [weightedExp_apply]; exact hfe j, rfl⟩
  rw [himage]
  exact ((isCompact_stdSimplex Ω).inter_right hclosed).image (hcont f)

/-- **PL (9.6), the exact value of the dual.**  When some law matches the prescribed supplied
features, the primal report optimum is attained, and the dual objective has that optimum as its
greatest lower bound.  The infimum need not be attained, which is why the conclusion is stated
as `IsGLB`: the manuscript records exactly that a finite optimizing multiplier may fail to exist
at a boundary information vector, without affecting the equality of values or primal
attainment. -/
theorem primal_max_eq_dual_inf (h : Ω → Fin m → ℝ) (f : Ω → ℝ) (c : Fin m → ℝ)
    (hΩ : (Finset.univ : Finset Ω).Nonempty) (hfeas : (primalValues h f c).Nonempty) :
    ∃ U : ℝ, IsGreatest (primalValues h f c) U ∧ IsGLB (dualValues h f c hΩ) U := by
  obtain ⟨U, hU⟩ := (isCompact_primalValues h f c).exists_isGreatest hfeas
  obtain ⟨p, hp, hs, hfe, hUval⟩ := hU.1
  refine ⟨U, hU, ?_, ?_⟩
  · rintro v ⟨lam, rfl⟩
    rw [hUval]
    refine dual_certificate h f c lam _ p hp hs hfe fun ω ↦ ?_
    exact Finset.le_sup' (fun ω ↦ f ω - dot lam (h ω)) (Finset.mem_univ ω)
  · intro w hw
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hAclosed : IsClosed (convexHull ℝ (Set.range (featureReportPair h f))) :=
      (Set.finite_range (featureReportPair h f)).isClosed_convexHull
    have hcU : ((c, U) : (Fin m → ℝ) × ℝ)
        ∈ convexHull ℝ (Set.range (featureReportPair h f)) := by
      rw [← region_eq_convexHull_of_module]
      refine ⟨p, hp, hs, ?_⟩
      refine (Prod.ext ?_ ?_).symm
      · rw [Prod.fst_sum]
        funext j
        simp only [featureReportPair, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
          Finset.sum_apply]
        rw [← hfe j, weightedExp_apply]
      · rw [Prod.snd_sum]
        simp only [featureReportPair, Prod.smul_snd, smul_eq_mul]
        rw [hUval, weightedExp_apply]
    have hnot : ((c, U + ε) : (Fin m → ℝ) × ℝ)
        ∉ convexHull ℝ (Set.range (featureReportPair h f)) := by
      intro hmem
      rw [← region_eq_convexHull_of_module] at hmem
      obtain ⟨q, hq, hqs, hqeq⟩ := hmem
      have hfst : ∀ j, weightedExp q hq hqs (fun ω ↦ h ω j) = c j := by
        intro j
        have := congrArg (fun z : (Fin m → ℝ) × ℝ ↦ z.1 j) hqeq
        simp only [Prod.fst_sum, featureReportPair, Prod.smul_fst, Pi.smul_apply,
          smul_eq_mul, Finset.sum_apply] at this
        rw [weightedExp_apply]
        exact this.symm
      have hsnd : weightedExp q hq hqs f = U + ε := by
        have := congrArg (fun z : (Fin m → ℝ) × ℝ ↦ z.2) hqeq
        simp only [Prod.snd_sum, featureReportPair, Prod.smul_snd, smul_eq_mul] at this
        rw [weightedExp_apply]
        exact this.symm
      have hmem' : U + ε ∈ primalValues h f c := ⟨q, hq, hqs, hfst, hsnd.symm⟩
      linarith [hU.2 hmem']
    obtain ⟨φ, u, hlt, hgt⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hAclosed hnot
    have hdecomp : ∀ (a : Fin m → ℝ) (y : ℝ), φ (a, y) = φ (a, 0) + y * φ (0, 1) := by
      intro a y
      have hdec : ((a, y) : (Fin m → ℝ) × ℝ) = (a, 0) + y • (0, 1) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [hdec, map_add, map_smul, smul_eq_mul]
    have hκpos : 0 < φ ((0 : Fin m → ℝ), (1 : ℝ)) := by
      have h1 := hlt _ hcU
      rw [hdecomp c U] at h1
      rw [hdecomp c (U + ε)] at hgt
      by_contra hcon
      push_neg at hcon
      nlinarith [h1, hgt, hε, hcon]
    have hphi : ∀ a : Fin m → ℝ,
        φ (a, 0) = ∑ j, a j * φ ((Pi.single j 1 : Fin m → ℝ), (0 : ℝ)) := by
      intro a
      have hdec : ((a, (0 : ℝ)) : (Fin m → ℝ) × ℝ)
          = ∑ j, a j • ((Pi.single j 1 : Fin m → ℝ), (0 : ℝ)) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]
          funext i
          simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
        · rw [Prod.snd_sum]
          simp
      rw [hdec, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
    obtain ⟨lam, hlam⟩ : ∃ lam : Fin m → ℝ,
        ∀ a : Fin m → ℝ, φ ((0 : Fin m → ℝ), (1 : ℝ)) * dot lam a = -(φ (a, 0)) := by
      refine ⟨fun j ↦ -(φ ((Pi.single j 1 : Fin m → ℝ), (0 : ℝ)))
        / φ ((0 : Fin m → ℝ), (1 : ℝ)), fun a ↦ ?_⟩
      have hne : φ ((0 : Fin m → ℝ), (1 : ℝ)) ≠ 0 := ne_of_gt hκpos
      rw [hphi a, neg_finset_sum]
      simp only [dot, Descent.Core.innerSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      field_simp
    obtain ⟨ω₀, -, hω₀⟩ := Finset.exists_mem_eq_sup' hΩ fun ω ↦ f ω - dot lam (h ω)
    have hbound : w ≤ dot lam c + Finset.univ.sup' hΩ (fun ω ↦ f ω - dot lam (h ω)) :=
      hw ⟨lam, rfl⟩
    rw [hω₀] at hbound
    have he1 : φ (h ω₀, (0 : ℝ)) = -(φ ((0 : Fin m → ℝ), (1 : ℝ)) * dot lam (h ω₀)) := by
      rw [hlam (h ω₀), neg_neg]
    have he2 : φ (c, (0 : ℝ)) = -(φ ((0 : Fin m → ℝ), (1 : ℝ)) * dot lam c) := by
      rw [hlam c, neg_neg]
    have h1 := hlt (featureReportPair h f ω₀)
      (subset_convexHull ℝ _ (Set.mem_range_self ω₀))
    rw [show featureReportPair h f ω₀ = (h ω₀, f ω₀) from rfl, hdecomp (h ω₀) (f ω₀), he1] at h1
    rw [hdecomp c (U + ε), he2] at hgt
    by_contra hcon
    push_neg at hcon
    have hX : U + ε < dot lam c + (f ω₀ - dot lam (h ω₀)) := lt_of_lt_of_le hcon hbound
    nlinarith [h1, hgt, hκpos, hX]

end

end Descent.Portability.JointReportFeasibility

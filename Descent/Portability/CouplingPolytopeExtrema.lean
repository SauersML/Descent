/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverCouplingPolytope

assert_below Descent.Decision Descent.Program

/-!
# Extremal coadapted path laws exist at a finite horizon

UPT Theorem 5.3 ends by asserting that the exact attainable expectation of a
finite-horizon path report is the interval between its minimum and its maximum
on the coupling polytope, both attained. `TurnoverCouplingPolytope` supplies the
polytope itself, its nonemptiness and its convexity; what is added here is the
existence of the two extremal path laws.

The obstacle is that history masses are indexed by `List`, which is not finite.
It is removed by noticing that every constraint of the polytope touches only
histories of length between one and the horizon, so a feasible mass vector may
be truncated to vanish elsewhere without changing either its feasibility or the
report. Truncated feasible vectors have every coordinate in `[0,1]`, because the
prefix-flow constraint makes masses decrease along extension from an initial law
of total mass one. They therefore form a closed subset of a product of compact
intervals, compact by Tychonoff, and the report is continuous and linear on it,
so the extreme value theorem applies and mixing fills the interval between the
two extremes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CouplingPolytopeExtrema

open Foundations TurnoverCouplingPolytope

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : Type*} [Fintype Z] [DecidableEq Z]

section Truncation

/-- The horizon-`T` expectation of a path report under a history-mass vector. -/
def pathReport (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ) (γ : List (ι → Z) → ℝ) : ℝ :=
  ∑ u : Fin (T + 1) → ι → Z, γ (List.ofFn u) * F u

/-- Truncation of a history-mass vector to the histories the horizon constrains. -/
def truncate (T : ℕ) (γ : List (ι → Z) → ℝ) : List (ι → Z) → ℝ :=
  fun v ↦ if 1 ≤ v.length ∧ v.length ≤ T + 1 then γ v else 0

/-- Value of a truncated mass vector. -/
@[simp] theorem truncate_apply (T : ℕ) (γ : List (ι → Z) → ℝ) (v : List (ι → Z)) :
    truncate T γ v = if 1 ≤ v.length ∧ v.length ≤ T + 1 then γ v else 0 := rfl

/-- Each initial mass is at most one. -/
theorem init_le_one {μ : (ι → Z) → ℝ} (hμnn : ∀ a, 0 ≤ μ a) (hμsum : ∑ a, μ a = 1)
    (a : ι → Z) : μ a ≤ 1 := by
  have h := Finset.single_le_sum (f := μ) (fun x _ ↦ hμnn x) (Finset.mem_univ a)
  rw [hμsum] at h
  exact h

/-- **Feasible history masses never exceed one**: prefix flow makes them decrease along
extension from an initial law of total mass one.

Assumes: `InPolytope μ K T γ`, witnessed by `productKernel_pathLaw_inPolytope`. -/
theorem inPolytope_le_one {μ : (ι → Z) → ℝ} (hμ1 : ∀ a, μ a ≤ 1)
    {K : ℕ → ι → (ι → Z) → Z → ℝ} {T : ℕ} {γ : List (ι → Z) → ℝ}
    (hpoly : InPolytope μ K T γ) :
    ∀ v : List (ι → Z), 1 ≤ v.length → v.length ≤ T + 1 → γ v ≤ 1
  | [], hcon, _ => absurd hcon (by simp)
  | [a], _, _ => by
      rw [hpoly.2.1 a]
      exact hμ1 a
  | a :: z :: h, _, hlen => by
      have hlen' : h.length + 1 ≤ T := by
        simp only [List.length_cons] at hlen
        omega
      have hstep : γ (a :: z :: h) ≤ γ (z :: h) := by
        rw [← hpoly.2.2.1 z h hlen']
        refine Finset.single_le_sum (f := fun a' ↦ γ (a' :: z :: h)) ?_ (Finset.mem_univ a)
        intro a' _
        refine hpoly.1 _ (by simp) ?_
        simp only [List.length_cons]
        omega
      have hprev : γ (z :: h) ≤ 1 := by
        refine inPolytope_le_one hμ1 hpoly (z :: h) (by simp) ?_
        simp only [List.length_cons]
        omega
      linarith

/-- **Truncation preserves feasibility**, because every constraint of the polytope touches
only histories of length between one and the horizon.

Assumes: `InPolytope μ K T γ`, witnessed by `productKernel_pathLaw_inPolytope`. -/
theorem truncate_inPolytope {μ : (ι → Z) → ℝ} {K : ℕ → ι → (ι → Z) → Z → ℝ} {T : ℕ}
    {γ : List (ι → Z) → ℝ} (hpoly : InPolytope μ K T γ) :
    InPolytope μ K T (truncate T γ) := by
  have hval : ∀ v : List (ι → Z), 1 ≤ v.length → v.length ≤ T + 1 → truncate T γ v = γ v := by
    intro v h1 h2
    rw [truncate_apply, if_pos ⟨h1, h2⟩]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v h1 h2
    rw [hval v h1 h2]
    exact hpoly.1 v h1 h2
  · intro a
    rw [hval [a] (by simp) (by simp)]
    exact hpoly.2.1 a
  · intro z h hlen
    have he : ∀ a : ι → Z, truncate T γ (a :: z :: h) = γ (a :: z :: h) := by
      intro a
      refine hval _ (by simp) ?_
      simp only [List.length_cons]
      omega
    rw [Finset.sum_congr rfl fun a _ ↦ he a, hpoly.2.2.1 z h hlen]
    refine (hval (z :: h) (by simp) ?_).symm
    simp only [List.length_cons]
    omega
  · intro z h i b hlen
    have he : ∀ a : ι → Z, truncate T γ (a :: z :: h) = γ (a :: z :: h) := by
      intro a
      refine hval _ (by simp) ?_
      simp only [List.length_cons]
      omega
    rw [Finset.sum_congr rfl fun a _ ↦ he a, hpoly.2.2.2 z h i b hlen]
    congr 1
    refine (hval (z :: h) (by simp) ?_).symm
    simp only [List.length_cons]
    omega

/-- Truncation leaves every horizon report unchanged. -/
theorem pathReport_truncate (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ)
    (γ : List (ι → Z) → ℝ) : pathReport T F (truncate T γ) = pathReport T F γ := by
  have hu : ∀ u : Fin (T + 1) → ι → Z,
      1 ≤ (List.ofFn u).length ∧ (List.ofFn u).length ≤ T + 1 := by
    intro u
    rw [List.length_ofFn]
    omega
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [truncate_apply, if_pos (hu u)]

/-- The horizon report is linear along mixtures. -/
theorem pathReport_mixture (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ)
    (γ₁ γ₂ : List (ι → Z) → ℝ) (θ : ℝ) :
    pathReport T F (fun v ↦ θ * γ₁ v + (1 - θ) * γ₂ v)
      = θ * pathReport T F γ₁ + (1 - θ) * pathReport T F γ₂ := by
  have hrw : ∀ u : Fin (T + 1) → ι → Z,
      (θ * γ₁ (List.ofFn u) + (1 - θ) * γ₂ (List.ofFn u)) * F u
        = θ * (γ₁ (List.ofFn u) * F u) + (1 - θ) * (γ₂ (List.ofFn u) * F u) := fun u ↦ by ring
  show ∑ u : Fin (T + 1) → ι → Z,
      (θ * γ₁ (List.ofFn u) + (1 - θ) * γ₂ (List.ofFn u)) * F u = _
  rw [Finset.sum_congr rfl fun u _ ↦ hrw u, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-- The horizon report is continuous in the history masses. -/
theorem pathReport_continuous (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ) :
    Continuous (pathReport T F) := by
  show Continuous fun γ : List (ι → Z) → ℝ ↦ ∑ u : Fin (T + 1) → ι → Z, γ (List.ofFn u) * F u
  exact continuous_finset_sum _ fun u _ ↦
    (continuous_apply (List.ofFn u)).mul continuous_const

end Truncation

section Compactness

/-- The horizon-truncated coupling polytope: feasible history masses vanishing outside the
horizon. -/
def horizonPolytope (μ : (ι → Z) → ℝ) (K : ℕ → ι → (ι → Z) → Z → ℝ) (T : ℕ) :
    Set (List (ι → Z) → ℝ) :=
  {γ | InPolytope μ K T γ ∧
    ∀ v : List (ι → Z), ¬(1 ≤ v.length ∧ v.length ≤ T + 1) → γ v = 0}

/-- The truncated polytope is closed. -/
theorem horizonPolytope_isClosed (μ : (ι → Z) → ℝ) (K : ℕ → ι → (ι → Z) → Z → ℝ) (T : ℕ) :
    IsClosed (horizonPolytope μ K T) := by
  have h1 : IsClosed {γ : List (ι → Z) → ℝ |
      ∀ v : List (ι → Z), 1 ≤ v.length → v.length ≤ T + 1 → 0 ≤ γ v} := by
    have hrw : {γ : List (ι → Z) → ℝ |
        ∀ v : List (ι → Z), 1 ≤ v.length → v.length ≤ T + 1 → 0 ≤ γ v}
        = ⋂ (v : List (ι → Z)) (_ : 1 ≤ v.length) (_ : v.length ≤ T + 1),
            {γ : List (ι → Z) → ℝ | 0 ≤ γ v} := by
      ext γ
      simp
    rw [hrw]
    exact isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const (continuous_apply v)
  have h2 : IsClosed {γ : List (ι → Z) → ℝ | ∀ a, γ [a] = μ a} := by
    have hrw : {γ : List (ι → Z) → ℝ | ∀ a, γ [a] = μ a}
        = ⋂ a : ι → Z, {γ : List (ι → Z) → ℝ | γ [a] = μ a} := by
      ext γ
      simp
    rw [hrw]
    exact isClosed_iInter fun a ↦ isClosed_eq (continuous_apply [a]) continuous_const
  have h3 : IsClosed {γ : List (ι → Z) → ℝ |
      ∀ (z : ι → Z) (h : List (ι → Z)), h.length + 1 ≤ T →
        ∑ a, γ (a :: z :: h) = γ (z :: h)} := by
    have hrw : {γ : List (ι → Z) → ℝ |
        ∀ (z : ι → Z) (h : List (ι → Z)), h.length + 1 ≤ T →
          ∑ a, γ (a :: z :: h) = γ (z :: h)}
        = ⋂ (z : ι → Z) (h : List (ι → Z)) (_ : h.length + 1 ≤ T),
            {γ : List (ι → Z) → ℝ | ∑ a, γ (a :: z :: h) = γ (z :: h)} := by
      ext γ
      simp
    rw [hrw]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun h ↦ isClosed_iInter fun _ ↦ ?_
    exact isClosed_eq (continuous_finset_sum _ fun a _ ↦ continuous_apply (a :: z :: h))
      (continuous_apply (z :: h))
  have h4 : IsClosed {γ : List (ι → Z) → ℝ |
      ∀ (z : ι → Z) (h : List (ι → Z)) (i : ι) (b : Z), h.length + 1 ≤ T →
        ∑ a ∈ Finset.univ.filter fun a : ι → Z ↦ a i = b, γ (a :: z :: h)
          = K h.length i z b * γ (z :: h)} := by
    have hrw : {γ : List (ι → Z) → ℝ |
        ∀ (z : ι → Z) (h : List (ι → Z)) (i : ι) (b : Z), h.length + 1 ≤ T →
          ∑ a ∈ Finset.univ.filter fun a : ι → Z ↦ a i = b, γ (a :: z :: h)
            = K h.length i z b * γ (z :: h)}
        = ⋂ (z : ι → Z) (h : List (ι → Z)) (i : ι) (b : Z) (_ : h.length + 1 ≤ T),
            {γ : List (ι → Z) → ℝ |
              ∑ a ∈ Finset.univ.filter fun a : ι → Z ↦ a i = b, γ (a :: z :: h)
                = K h.length i z b * γ (z :: h)} := by
      ext γ
      simp
    rw [hrw]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun h ↦ isClosed_iInter fun i ↦
      isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦ ?_
    exact isClosed_eq (continuous_finset_sum _ fun a _ ↦ continuous_apply (a :: z :: h))
      (continuous_const.mul (continuous_apply (z :: h)))
  have h5 : IsClosed {γ : List (ι → Z) → ℝ |
      ∀ v : List (ι → Z), ¬(1 ≤ v.length ∧ v.length ≤ T + 1) → γ v = 0} := by
    have hrw : {γ : List (ι → Z) → ℝ |
        ∀ v : List (ι → Z), ¬(1 ≤ v.length ∧ v.length ≤ T + 1) → γ v = 0}
        = ⋂ (v : List (ι → Z)) (_ : ¬(1 ≤ v.length ∧ v.length ≤ T + 1)),
            {γ : List (ι → Z) → ℝ | γ v = 0} := by
      ext γ
      simp
    rw [hrw]
    exact isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply v) continuous_const
  have hsplit : horizonPolytope μ K T
      = {γ : List (ι → Z) → ℝ |
          ∀ v : List (ι → Z), 1 ≤ v.length → v.length ≤ T + 1 → 0 ≤ γ v}
        ∩ (({γ : List (ι → Z) → ℝ | ∀ a, γ [a] = μ a}
          ∩ ({γ : List (ι → Z) → ℝ |
              ∀ (z : ι → Z) (h : List (ι → Z)), h.length + 1 ≤ T →
                ∑ a, γ (a :: z :: h) = γ (z :: h)}
            ∩ {γ : List (ι → Z) → ℝ |
              ∀ (z : ι → Z) (h : List (ι → Z)) (i : ι) (b : Z), h.length + 1 ≤ T →
                ∑ a ∈ Finset.univ.filter fun a : ι → Z ↦ a i = b, γ (a :: z :: h)
                  = K h.length i z b * γ (z :: h)}))
          ∩ {γ : List (ι → Z) → ℝ |
              ∀ v : List (ι → Z), ¬(1 ≤ v.length ∧ v.length ≤ T + 1) → γ v = 0}) := rfl
  rw [hsplit]
  exact h1.inter ((h2.inter (h3.inter h4)).inter h5)

/-- **The truncated polytope is compact.**  Every coordinate lies in the unit interval, so
it is a closed subset of a Tychonoff product of compact intervals. -/
theorem horizonPolytope_isCompact {μ : (ι → Z) → ℝ} (hμnn : ∀ a, 0 ≤ μ a)
    (hμsum : ∑ a, μ a = 1) (K : ℕ → ι → (ι → Z) → Z → ℝ) (T : ℕ) :
    IsCompact (horizonPolytope μ K T) := by
  have hsub : horizonPolytope μ K T ⊆ Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1 := by
    intro γ hγ v _
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · by_cases hv : 1 ≤ v.length ∧ v.length ≤ T + 1
      · exact hγ.1.1 v hv.1 hv.2
      · rw [hγ.2 v hv]
    · by_cases hv : 1 ≤ v.length ∧ v.length ≤ T + 1
      · exact inPolytope_le_one (init_le_one hμnn hμsum) hγ.1 v hv.1 hv.2
      · rw [hγ.2 v hv]
        norm_num
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset
    (horizonPolytope_isClosed μ K T) hsub

/-- **The truncated polytope is nonempty**: the truncated independent product coupling
belongs to it. -/
theorem horizonPolytope_nonempty {μ : (ι → Z) → ℝ} (hμnn : ∀ a, 0 ≤ μ a)
    {K : ℕ → ι → (ι → Z) → Z → ℝ} (hKnn : ∀ t i z b, 0 ≤ K t i z b)
    (hKsum : ∀ t i z, ∑ b, K t i z b = 1) (T : ℕ) :
    (horizonPolytope μ K T).Nonempty := by
  refine ⟨truncate T (pathLaw μ (productKernel K)),
    truncate_inPolytope (productKernel_pathLaw_inPolytope hμnn K hKnn hKsum T), ?_⟩
  intro v hv
  rw [truncate_apply, if_neg hv]

end Compactness

section Extrema

/-- **UPT Theorem 5.3, extremal path laws.**  A finite-horizon path report attains a minimum
and a maximum over the coadapted path laws.

Assumes: `InPolytope μ K T`, witnessed by `productKernel_pathLaw_inPolytope`. -/
theorem inPolytope_report_extrema {μ : (ι → Z) → ℝ} (hμnn : ∀ a, 0 ≤ μ a)
    (hμsum : ∑ a, μ a = 1) {K : ℕ → ι → (ι → Z) → Z → ℝ} (hKnn : ∀ t i z b, 0 ≤ K t i z b)
    (hKsum : ∀ t i z, ∑ b, K t i z b = 1) (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ) :
    ∃ γmin γmax : List (ι → Z) → ℝ, InPolytope μ K T γmin ∧ InPolytope μ K T γmax ∧
      ∀ γ, InPolytope μ K T γ →
        pathReport T F γmin ≤ pathReport T F γ ∧
          pathReport T F γ ≤ pathReport T F γmax := by
  have hcomp := horizonPolytope_isCompact hμnn hμsum K T
  have hne := horizonPolytope_nonempty hμnn hKnn hKsum T
  have hcont := (pathReport_continuous T F).continuousOn (s := horizonPolytope μ K T)
  obtain ⟨γmin, hminmem, hmin⟩ := hcomp.exists_isMinOn hne hcont
  obtain ⟨γmax, hmaxmem, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  refine ⟨γmin, γmax, hminmem.1, hmaxmem.1, fun γ hγ ↦ ?_⟩
  have htr : truncate T γ ∈ horizonPolytope μ K T := by
    refine ⟨truncate_inPolytope hγ, ?_⟩
    intro v hv
    rw [truncate_apply, if_neg hv]
  have heq : pathReport T F (truncate T γ) = pathReport T F γ := pathReport_truncate T F γ
  constructor
  · have h := isMinOn_iff.mp hmin _ htr
    rwa [heq] at h
  · have h := isMaxOn_iff.mp hmax _ htr
    rwa [heq] at h

/-- **UPT Theorem 5.3, the exact attainable report range.**  The set of expectations of a
finite-horizon path report over the coadapted path laws is exactly a closed interval, both
endpoints attained.

Assumes: `InPolytope μ K T`, witnessed by `productKernel_pathLaw_inPolytope`. -/
theorem inPolytope_report_range {μ : (ι → Z) → ℝ} (hμnn : ∀ a, 0 ≤ μ a)
    (hμsum : ∑ a, μ a = 1) {K : ℕ → ι → (ι → Z) → Z → ℝ} (hKnn : ∀ t i z b, 0 ≤ K t i z b)
    (hKsum : ∀ t i z, ∑ b, K t i z b = 1) (T : ℕ) (F : (Fin (T + 1) → ι → Z) → ℝ) :
    ∃ lo hi : ℝ, lo ≤ hi ∧
      {y | ∃ γ, InPolytope μ K T γ ∧ pathReport T F γ = y} = Set.Icc lo hi := by
  obtain ⟨γmin, γmax, hmin, hmax, hopt⟩ :=
    inPolytope_report_extrema hμnn hμsum hKnn hKsum T F
  refine ⟨pathReport T F γmin, pathReport T F γmax, (hopt γmax hmax).1, ?_⟩
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨(hopt γ hγ).1, (hopt γ hγ).2⟩
  · rintro ⟨hy1, hy2⟩
    by_cases hdeg : pathReport T F γmax = pathReport T F γmin
    · refine ⟨γmin, hmin, ?_⟩
      rw [hdeg] at hy2
      linarith
    · have hlt : pathReport T F γmin < pathReport T F γmax :=
        lt_of_le_of_ne (le_trans hy1 hy2) (Ne.symm hdeg)
      have hden : (0 : ℝ) < pathReport T F γmax - pathReport T F γmin := by linarith
      have hdenne : pathReport T F γmax - pathReport T F γmin ≠ 0 := ne_of_gt hden
      set θ := (pathReport T F γmax - y) / (pathReport T F γmax - pathReport T F γmin) with hθ
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
      have hθ1 : θ ≤ 1 := by
        rw [hθ, div_le_one hden]
        linarith
      refine ⟨fun v ↦ θ * γmin v + (1 - θ) * γmax v,
        inPolytope_mixture hmin hmax hθ0 hθ1, ?_⟩
      rw [pathReport_mixture]
      have hstep : θ * (pathReport T F γmax - pathReport T F γmin)
          = pathReport T F γmax - y := by
        rw [hθ, div_mul_eq_mul_div, mul_comm, mul_div_assoc,
          div_self hdenne, mul_one]
      linarith [hstep]

end Extrema

end

end Descent.Portability.CouplingPolytopeExtrema

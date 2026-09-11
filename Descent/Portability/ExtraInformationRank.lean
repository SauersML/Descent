/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportRegionCertificates
import Descent.Portability.ObservableClosureLaw
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

assert_below Descent.Decision Descent.Program

/-!
# The minimum extra linear information that identifies a report vector

The directions two compatible laws can differ by form a subspace: they carry zero total mass,
are invisible to every specified summary, and vanish wherever every compatible law vanishes.
The report table maps that subspace onto a space of report movements, and the dimension of
that image is exactly the number of additional scalar linear expectation summaries needed to
identify the whole report vector uniformly. Fewer summaries always leave two compatible laws
that agree on the old and the new information yet report differently; that many summaries
always suffice, and an explicit family attaining the bound is constructed.

This is PL Theorem 10.2 (10.6), continuing PL Theorem 10.2 (10.5) which is
`ReportRegionCertificates.report_identified_iff_invisible_directions_vanish`. The lower bound
uses `ObservableClosureLaw.linear_factorization_iff`: if the extra summaries did identify the
report, the report movement would factor through them, and a linear image cannot raise
dimension. The upper bound extends a basis of coordinate functionals on the image and pulls
them back, so the attaining summaries are exhibited rather than asserted to exist.

The manuscript's uniform qualifier is respected: the summaries must identify the report for
every attainable value of those summaries on the current compatible set, which is exactly the
quantifier used below. The hypotheses are the manuscript's domain conditions: the specified
information is consistent, so a compatible law exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExtraInformationRank

open FiniteMetricIdentification ReportRegionCertificates

noncomputable section

variable {S O J : Type*} [Fintype S] [Fintype O] [Fintype J]

/-- The directions two compatible laws can differ by: zero total mass, invisible to every
specified summary, and vanishing wherever every compatible law vanishes. -/
def invisibleDirections (observe : O → S → ℝ) (observed : O → ℝ) : Submodule ℝ (S → ℝ) where
  carrier := {h | (∀ s, (∀ q ∈ feasible observe observed, q s = 0) → h s = 0) ∧
    (∑ s, h s = 0) ∧ ∀ o, pairing (observe o) h = 0}
  zero_mem' := by
    refine ⟨fun _ _ ↦ rfl, by simp, fun o ↦ ?_⟩
    simp [pairing]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun s hs ↦ by simp [Pi.add_apply, ha1 s hs, hb1 s hs], ?_, fun o ↦ ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, ha2, hb2, add_zero]
    · rw [pairing_add, ha3 o, hb3 o, add_zero]
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    refine ⟨fun s hs ↦ by simp [Pi.smul_apply, ha1 s hs], ?_, fun o ↦ ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, ha2, mul_zero]
    · rw [pairing_smul, ha3 o, mul_zero]

/-- The report movement produced by a direction, as a linear map. -/
def reportMap (reportTable : J → S → ℝ) : (S → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun h := fun j ↦ pairing (reportTable j) h
  map_add' a b := by
    funext j
    exact pairing_add _ _ _
  map_smul' c a := by
    funext j
    exact pairing_smul _ _ _

/-- PL (10.6): the minimum number of additional scalar linear expectation summaries needed
to identify the report vector uniformly. -/
def extraRank (observe : O → S → ℝ) (observed : O → ℝ) (reportTable : J → S → ℝ) : ℕ :=
  Module.finrank ℝ ((invisibleDirections observe observed).map (reportMap reportTable))

/-- The difference of two compatible laws is an invisible direction. -/
theorem sub_mem_invisibleDirections (observe : O → S → ℝ) (observed : O → ℝ)
    (p q : S → ℝ) (hp : p ∈ feasible observe observed) (hq : q ∈ feasible observe observed) :
    p - q ∈ invisibleDirections observe observed := by
  refine ⟨fun s hs ↦ by simp [Pi.sub_apply, hs p hp, hs q hq], ?_, fun o ↦ ?_⟩
  · simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hp.1.2, hq.1.2, sub_self]
  · rw [pairing_sub, hp.2 o, hq.2 o, sub_self]

/-- A compatible law can be moved a positive distance along any invisible direction and stay
compatible, which is what turns an invisible direction into two genuine countermodels. -/
theorem exists_positive_shift (observe : O → S → ℝ) (observed : O → ℝ)
    (hne : (feasible observe observed).Nonempty) :
    ∃ p₀ ∈ feasible observe observed, ∀ dir ∈ invisibleDirections observe observed,
      ∃ eps : ℝ, 0 < eps ∧ p₀ + eps • dir ∈ feasible observe observed := by
  classical
  obtain ⟨p₀, hp₀, hpos⟩ := exists_feasible_pos_on_active observe observed hne
  have hS : Nonempty S := by
    rcases isEmpty_or_nonempty S with hempty | hnonempty
    · exact absurd hp₀.1.2 (by simp)
    · exact hnonempty
  refine ⟨p₀, hp₀, ?_⟩
  rintro dir ⟨hsupp, hmass, hobs⟩
  have hactive : ∀ s, dir s ≠ 0 → 0 < p₀ s := by
    intro s hs
    refine hpos s ?_
    by_contra hno
    push_neg at hno
    exact hs (hsupp s fun q hq ↦ le_antisymm (hno q hq) (hq.1.1 s))
  have hstep_pos : ∀ s, (0 : ℝ) < (if dir s = 0 then (1 : ℝ) else p₀ s / |dir s|) := by
    intro s
    by_cases hzero : dir s = 0
    · simp [hzero]
    · rw [if_neg hzero]
      exact div_pos (hactive s hzero) (abs_pos.mpr hzero)
  refine ⟨Finset.univ.inf' Finset.univ_nonempty
    (fun s ↦ if dir s = 0 then (1 : ℝ) else p₀ s / |dir s|),
    (Finset.lt_inf'_iff _).2 fun s _ ↦ hstep_pos s, ?_⟩
  refine ⟨⟨fun s ↦ ?_, ?_⟩, fun o ↦ ?_⟩
  · by_cases hzero : dir s = 0
    · simpa [hzero] using hp₀.1.1 s
    · have hbound := Finset.inf'_le
        (f := fun t ↦ if dir t = 0 then (1 : ℝ) else p₀ t / |dir t|) (Finset.mem_univ s)
      rw [if_neg hzero] at hbound
      have habs : (0 : ℝ) < |dir s| := abs_pos.mpr hzero
      have hmul := mul_le_mul_of_nonneg_right hbound habs.le
      rw [div_mul_cancel₀ _ (ne_of_gt habs)] at hmul
      have hneg := neg_abs_le (dir s)
      have hposeps : (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty
          (fun t ↦ if dir t = 0 then (1 : ℝ) else p₀ t / |dir t|) :=
        (Finset.lt_inf'_iff _).2 fun t _ ↦ hstep_pos t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, hp₀.1.2, ← Finset.mul_sum, hmass, mul_zero, add_zero]
  · rw [pairing_add, pairing_smul, hp₀.2 o, hobs o, mul_zero, add_zero]

/-- PL Theorem 10.2 (10.6), the lower bound: fewer than `extraRank` additional linear
summaries always leave two compatible laws that agree on the old and the new information yet
report differently. -/
theorem extra_summaries_lower_bound (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (hne : (feasible observe observed).Nonempty) (count : ℕ)
    (extra : Fin count → S → ℝ) (hcount : count < extraRank observe observed reportTable) :
    ∃ p ∈ feasible observe observed, ∃ q ∈ feasible observe observed,
      (∀ k, pairing (extra k) p = pairing (extra k) q) ∧
        ∃ j, pairing (reportTable j) p ≠ pairing (reportTable j) q := by
  classical
  set summaryMap : (S → ℝ) →ₗ[ℝ] (Fin count → ℝ) :=
    { toFun := fun h k ↦ pairing (extra k) h
      map_add' := fun a b ↦ by
        funext k
        exact pairing_add _ _ _
      map_smul' := fun c a ↦ by
        funext k
        exact pairing_smul _ _ _ } with hsummary
  have hnotle : ¬ (LinearMap.ker
      (summaryMap.domRestrict (invisibleDirections observe observed)) ≤
        LinearMap.ker ((reportMap reportTable).domRestrict
          (invisibleDirections observe observed))) := by
    intro hle
    obtain ⟨update, hupdate⟩ := (ObservableClosureLaw.linear_factorization_iff _ _).2 hle
    have hrange : LinearMap.range ((reportMap reportTable).domRestrict
        (invisibleDirections observe observed)) =
          (LinearMap.range (summaryMap.domRestrict
            (invisibleDirections observe observed))).map update := by
      rw [← hupdate, LinearMap.range_comp]
    have hle1 : Module.finrank ℝ (LinearMap.range ((reportMap reportTable).domRestrict
        (invisibleDirections observe observed))) ≤
          Module.finrank ℝ (LinearMap.range (summaryMap.domRestrict
            (invisibleDirections observe observed))) := by
      rw [hrange]
      exact Submodule.finrank_map_le _ _
    have hle2 : Module.finrank ℝ (LinearMap.range (summaryMap.domRestrict
        (invisibleDirections observe observed))) ≤ count := by
      have hbound := Submodule.finrank_le (LinearMap.range
        (summaryMap.domRestrict (invisibleDirections observe observed)))
      rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hbound
    rw [LinearMap.range_domRestrict] at hle1
    rw [extraRank] at hcount
    omega
  have hwitness : ∃ dir ∈ invisibleDirections observe observed,
      (∀ k, pairing (extra k) dir = 0) ∧ ∃ j, pairing (reportTable j) dir ≠ 0 := by
    by_contra hno
    push_neg at hno
    refine hnotle fun x hx ↦ ?_
    have hzero : ∀ k, pairing (extra k) (x : S → ℝ) = 0 := by
      intro k
      have hker : summaryMap (x : S → ℝ) = 0 := by
        simpa [LinearMap.domRestrict_apply] using hx
      exact congrFun hker k
    have hreport := hno (x : S → ℝ) x.2 hzero
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    funext j
    simpa [reportMap] using hreport j
  obtain ⟨dir, hdir, hextra, j, hj⟩ := hwitness
  obtain ⟨p₀, hp₀, hshift⟩ := exists_positive_shift observe observed hne
  obtain ⟨eps, heps, hfeas⟩ := hshift dir hdir
  refine ⟨p₀ + eps • dir, hfeas, p₀, hp₀, fun k ↦ ?_, j, ?_⟩
  · rw [pairing_add, pairing_smul, hextra k, mul_zero, add_zero]
  · rw [pairing_add, pairing_smul]
    intro heq
    have hval : eps * pairing (reportTable j) dir =
        (pairing (reportTable j) p₀ + eps * pairing (reportTable j) dir) -
          pairing (reportTable j) p₀ := by ring
    rw [heq, sub_self] at hval
    rcases mul_eq_zero.1 hval with hz | hz
    · exact absurd hz (ne_of_gt heps)
    · exact hj hz

/-- PL Theorem 10.2 (10.6), the upper bound: `extraRank` additional linear summaries suffice,
and an attaining family is exhibited. -/
theorem exists_extra_summaries (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) :
    ∃ extra : Fin (extraRank observe observed reportTable) → (S → ℝ),
      ∀ p ∈ feasible observe observed, ∀ q ∈ feasible observe observed,
        (∀ k, pairing (extra k) p = pairing (extra k) q) →
          ∀ j, pairing (reportTable j) p = pairing (reportTable j) q := by
  classical
  have hbasis := Module.finBasis ℝ
    ((invisibleDirections observe observed).map (reportMap reportTable))
  have hext : ∀ k, ∃ φ : (J → ℝ) →ₗ[ℝ] ℝ,
      φ.comp ((invisibleDirections observe observed).map
        (reportMap reportTable)).subtype = hbasis.coord k := fun k ↦
    LinearMap.exists_extend (hbasis.coord k)
  choose φ hφ using hext
  have hrep : ∀ (k : Fin (extraRank observe observed reportTable)) (x : S → ℝ),
      pairing (fun s ↦ ((φ k).comp (reportMap reportTable))
          (fun t ↦ if s = t then (1 : ℝ) else 0)) x =
        ((φ k).comp (reportMap reportTable)) x := by
    intro k x
    rw [LinearMap.pi_apply_eq_sum_univ ((φ k).comp (reportMap reportTable)) x]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [smul_eq_mul]; ring
  refine ⟨fun k s ↦ ((φ k).comp (reportMap reportTable))
    (fun t ↦ if s = t then (1 : ℝ) else 0), ?_⟩
  intro p hp q hq hagree j
  have hmem : p - q ∈ invisibleDirections observe observed :=
    sub_mem_invisibleDirections observe observed p q hp hq
  have hmap : reportMap reportTable (p - q) ∈
      (invisibleDirections observe observed).map (reportMap reportTable) :=
    Submodule.mem_map_of_mem hmem
  have hcoord : ∀ k, hbasis.coord k ⟨reportMap reportTable (p - q), hmap⟩ = 0 := by
    intro k
    have hcomp := LinearMap.congr_fun (hφ k) ⟨reportMap reportTable (p - q), hmap⟩
    rw [← hcomp]
    have hzero : ((φ k).comp (reportMap reportTable)) (p - q) = 0 := by
      rw [← hrep k (p - q), pairing_sub, hagree k, sub_self]
    simpa using hzero
  have hsub := hbasis.forall_coord_eq_zero_iff.1 hcoord
  have hvec : reportMap reportTable (p - q) = 0 := by
    have hval : (⟨reportMap reportTable (p - q), hmap⟩ :
        ((invisibleDirections observe observed).map (reportMap reportTable))).1 =
          (0 : ((invisibleDirections observe observed).map
            (reportMap reportTable))).1 := congrArg Subtype.val hsub
    simpa using hval
  have hj : pairing (reportTable j) (p - q) = 0 := by
    simpa [reportMap] using congrFun hvec j
  rw [pairing_sub] at hj
  linarith

end

end Descent.Portability.ExtraInformationRank

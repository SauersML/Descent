/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMetricIdentification
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

assert_below Descent.Decision Descent.Program

/-!
# The complete finite joint report region and its dual certificates

A finite family of completed states carries an unknown law constrained only by the
specified linear information already formalized as `FiniteMetricIdentification.feasible`.
Each named end-to-end report contributes one row of a report table, whose entries are the
study kernel's exact expectations. This module builds the attainable vector of expected
reports as a set, proves it is a compact convex polytope every point of which is attained by
an actual compatible law, proves weak linear-programming duality so that a potential
certifies a bound and a feasible law refutes one, proves both extrema of every report
contrast are attained, and proves that the support inequalities cut out the region exactly.
It then characterizes exact identification of the whole report vector by the vanishing of the
report table on every summary-invisible direction supported on the active states.

This is DC Theorem 2.1 (2.4)-(2.6) and Corollary 2.2, and PL Theorem 10.1 (10.3)-(10.4) and
Theorem 10.2 (10.5). It builds on `FiniteMetricIdentification.feasible`, `feasible_compact`,
`feasible_convex`, `pairing`, `dual_upper` and `dual_lower`, which already supply the scalar
interval of TQ Theorem 7.3 (7.7); the vector region, the joint support function, the
separation characterization and the identification criterion are what is added here.

The hypotheses are the manuscript's domain conditions: the constraint set is nonempty, and
total mass one is carried by the standard simplex rather than by a designated row of the
constraint matrix. Strong duality is not proved here; every bound below is the weak-duality
direction, which is what a certificate needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReportRegionCertificates

open FiniteMetricIdentification

noncomputable section

variable {S O J : Type*} [Fintype S]

/-- The exact attainable vector of expected reports, PL (10.3) and DC (2.4). Coordinate `j`
is the expectation of the `j`-th named report function, whose state-by-state values
`reportTable j` already integrate the specified study kernel. -/
def reportRegion (observe : O → S → ℝ) (observed : O → ℝ) (reportTable : J → S → ℝ) :
    Set (J → ℝ) :=
  (fun p j ↦ pairing (reportTable j) p) '' feasible observe observed

/-- The pairing of a law with a difference of laws splits, so differences of compatible
laws are exactly the directions invisible to every specified summary. -/
theorem pairing_sub (f p q : S → ℝ) : pairing f (p - q) = pairing f p - pairing f q := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

/-- A linear contrast of the report vector is the expectation of the corresponding
combined state function. This is the reduction used by both duality directions. -/
theorem pairing_contrast_reportRegion [Fintype J] (reportTable : J → S → ℝ) (u : J → ℝ)
    (p : S → ℝ) :
    pairing u (fun j ↦ pairing (reportTable j) p) =
      pairing (fun s ↦ ∑ j, u j * reportTable j s) p := by
  simp only [pairing, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Membership in the region is attainment: a report vector is attainable exactly when some
compatible completed-state law produces it coordinate by coordinate. -/
theorem mem_reportRegion_iff (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (r : J → ℝ) :
    r ∈ reportRegion observe observed reportTable ↔
      ∃ p ∈ feasible observe observed, ∀ j, r j = pairing (reportTable j) p := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun _ ↦ rfl⟩
  · rintro ⟨p, hp, hr⟩
    exact ⟨p, hp, by funext j; exact (hr j).symm⟩

/-- The report region is nonempty whenever the specified information is consistent. -/
theorem reportRegion_nonempty (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (hne : (feasible observe observed).Nonempty) :
    (reportRegion observe observed reportTable).Nonempty :=
  hne.image _

/-- The attainable report region is compact: DC Theorem 2.1, PL Theorem 10.1. -/
theorem reportRegion_isCompact (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) :
    IsCompact (reportRegion observe observed reportTable) :=
  (feasible_compact observe observed).image
    (continuous_pi fun j ↦ continuous_pairing (reportTable j))

/-- The attainable report region is convex: mixing two compatible completed-state laws
mixes their report vectors. -/
theorem reportRegion_convex (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) :
    Convex ℝ (reportRegion observe observed reportTable) := by
  rintro r ⟨p, hp, rfl⟩ r' ⟨q, hq, rfl⟩ a c ha hc hac
  refine ⟨a • p + c • q, feasible_convex observe observed hp hq ha hc hac, ?_⟩
  funext j
  simp [pairing_add, pairing_smul]

/-- Weak duality, DC (2.5)-(2.6) and PL (10.4): potentials dominating the contrasted report
table certify an upper bound on every attainable report contrast. -/
theorem report_contrast_le_dual_value [Fintype O] [Fintype J] (observe : O → S → ℝ)
    (observed : O → ℝ)
    (reportTable : J → S → ℝ) (u : J → ℝ) (potential : O → ℝ)
    (hdual : ∀ s, ∑ j, u j * reportTable j s ≤ ∑ o, potential o * observe o s)
    (r : J → ℝ) (hr : r ∈ reportRegion observe observed reportTable) :
    pairing u r ≤ pairing potential observed := by
  obtain ⟨p, hp, rfl⟩ := hr
  rw [pairing_contrast_reportRegion]
  exact dual_upper observe observed _ potential hdual p hp

/-- The lower weak-duality certificate: potentials dominated by the contrasted report table
certify a lower bound on every attainable report contrast. -/
theorem dual_value_le_report_contrast [Fintype O] [Fintype J] (observe : O → S → ℝ)
    (observed : O → ℝ)
    (reportTable : J → S → ℝ) (u : J → ℝ) (potential : O → ℝ)
    (hdual : ∀ s, ∑ o, potential o * observe o s ≤ ∑ j, u j * reportTable j s)
    (r : J → ℝ) (hr : r ∈ reportRegion observe observed reportTable) :
    pairing potential observed ≤ pairing u r := by
  obtain ⟨p, hp, rfl⟩ := hr
  rw [pairing_contrast_reportRegion]
  exact dual_lower observe observed _ potential hdual p hp

/-- Both extrema of every report contrast are attained by an actual compatible law, so the
support function of DC (2.5) is a maximum and not merely a supremum. -/
theorem exists_extreme_report_contrast [Fintype J] (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (hne : (feasible observe observed).Nonempty) (u : J → ℝ) :
    ∃ rmin ∈ reportRegion observe observed reportTable,
      ∃ rmax ∈ reportRegion observe observed reportTable,
        ∀ r ∈ reportRegion observe observed reportTable,
          pairing u rmin ≤ pairing u r ∧ pairing u r ≤ pairing u rmax := by
  obtain ⟨rmin, hmin, hminle⟩ :=
    (reportRegion_isCompact observe observed reportTable).exists_isMinOn
      (reportRegion_nonempty observe observed reportTable hne)
      (continuous_pairing u).continuousOn
  obtain ⟨rmax, hmax, hmaxle⟩ :=
    (reportRegion_isCompact observe observed reportTable).exists_isMaxOn
      (reportRegion_nonempty observe observed reportTable hne)
      (continuous_pairing u).continuousOn
  exact ⟨rmin, hmin, rmax, hmax, fun r hr ↦ ⟨hminle hr, hmaxle hr⟩⟩

/-- A report vector outside the region is strictly separated from it by a linear contrast.
Together with weak duality this is DC Theorem 2.1's closing claim that all the support
inequalities characterize the joint region exactly, so separate coordinate intervals are
strictly weaker information. -/
theorem not_mem_reportRegion_iff_separating_contrast [Fintype J] [DecidableEq J]
    (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (r : J → ℝ) :
    r ∉ reportRegion observe observed reportTable ↔
      ∃ u : J → ℝ, ∀ r' ∈ reportRegion observe observed reportTable,
        pairing u r' < pairing u r := by
  constructor
  · intro hr
    obtain ⟨f, level, hlt, hgt⟩ :=
      geometric_hahn_banach_closed_point (reportRegion_convex observe observed reportTable)
        (reportRegion_isCompact observe observed reportTable).isClosed hr
    refine ⟨fun i ↦ f fun j ↦ if i = j then (1 : ℝ) else 0, fun r' hr' ↦ ?_⟩
    have hform : ∀ x : J → ℝ,
        pairing (fun i ↦ f fun j ↦ if i = j then (1 : ℝ) else 0) x = f x := by
      intro x
      have hx := LinearMap.pi_apply_eq_sum_univ (f : (J → ℝ) →ₗ[ℝ] ℝ) x
      simp only [ContinuousLinearMap.coe_coe] at hx
      rw [hx]
      simp only [pairing]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_eq_mul]; ring
    rw [hform, hform]
    exact lt_trans (hlt r' hr') hgt
  · rintro ⟨u, hu⟩ hr
    exact lt_irrefl _ (hu r hr)

/-- A compatible law that charges every state some compatible law charges. This relative
interior point is the one PL Theorem 10.2 builds by averaging finitely many feasible laws. -/
theorem exists_feasible_pos_on_active (observe : O → S → ℝ) (observed : O → ℝ)
    (hne : (feasible observe observed).Nonempty) :
    ∃ p₀ ∈ feasible observe observed,
      ∀ s, (∃ q ∈ feasible observe observed, 0 < q s) → 0 < p₀ s := by
  classical
  obtain ⟨base, hbase⟩ := hne
  have hS : Nonempty S := by
    rcases isEmpty_or_nonempty S with hempty | hnonempty
    · exact absurd hbase.1.2 (by simp)
    · exact hnonempty
  have hcard : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hS
  have hchoice : ∀ s : S, ∃ q ∈ feasible observe observed,
      ((∃ q' ∈ feasible observe observed, 0 < q' s) → 0 < q s) := by
    intro s
    by_cases hact : ∃ q' ∈ feasible observe observed, 0 < q' s
    · obtain ⟨q, hq, hqs⟩ := hact
      exact ⟨q, hq, fun _ ↦ hqs⟩
    · exact ⟨base, hbase, fun hcontra ↦ absurd hcontra hact⟩
  choose sel hsel hselpos using hchoice
  refine ⟨∑ s, (Fintype.card S : ℝ)⁻¹ • sel s, ?_, ?_⟩
  · refine Convex.sum_mem (feasible_convex observe observed) (fun i _ ↦ ?_) ?_ fun i _ ↦ hsel i
    · positivity
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
  · intro t hact
    have hval : (∑ s, (Fintype.card S : ℝ)⁻¹ • sel s) t =
        ∑ s, (Fintype.card S : ℝ)⁻¹ * sel s t := by
      simp
    have hterm : (0 : ℝ) < (Fintype.card S : ℝ)⁻¹ * sel t t := by
      have hpos := hselpos t hact
      positivity
    have hle : (Fintype.card S : ℝ)⁻¹ * sel t t ≤
        ∑ s, (Fintype.card S : ℝ)⁻¹ * sel s t := by
      refine Finset.single_le_sum (f := fun s ↦ (Fintype.card S : ℝ)⁻¹ * sel s t)
        (fun i _ ↦ ?_) (Finset.mem_univ t)
      have := (hsel i).1.1 t
      positivity
    rw [hval]
    linarith

/-- PL Theorem 10.2 (10.5): the entire report vector is determined by the specified linear
information exactly when every direction that is invisible to the summaries, has zero total
mass, and is supported on the active states is also invisible to the report table. -/
theorem report_identified_iff_invisible_directions_vanish (observe : O → S → ℝ)
    (observed : O → ℝ) (reportTable : J → S → ℝ)
    (hne : (feasible observe observed).Nonempty) :
    (∀ p ∈ feasible observe observed, ∀ q ∈ feasible observe observed,
        ∀ j, pairing (reportTable j) p = pairing (reportTable j) q) ↔
      ∀ dir : S → ℝ, (∀ s, (∀ q ∈ feasible observe observed, q s = 0) → dir s = 0) →
        ∑ s, dir s = 0 → (∀ o, pairing (observe o) dir = 0) →
        ∀ j, pairing (reportTable j) dir = 0 := by
  classical
  obtain ⟨p₀, hp₀, hpos⟩ := exists_feasible_pos_on_active observe observed hne
  have hS : Nonempty S := by
    rcases isEmpty_or_nonempty S with hempty | hnonempty
    · exact absurd hp₀.1.2 (by simp)
    · exact hnonempty
  constructor
  · intro hident dir hsupp hmass hobs j
    have hstep_pos : ∀ s, (0 : ℝ) <
        (if dir s = 0 then (1 : ℝ) else p₀ s / |dir s|) := by
      intro s
      by_cases hzero : dir s = 0
      · simp [hzero]
      · have hactive : ∃ q ∈ feasible observe observed, 0 < q s := by
          by_contra hno
          push_neg at hno
          exact hzero (hsupp s fun q hq ↦ le_antisymm (hno q hq) (hq.1.1 s))
        rw [if_neg hzero]
        exact div_pos (hpos s hactive) (abs_pos.mpr hzero)
    set eps := Finset.univ.inf' Finset.univ_nonempty
      (fun s ↦ if dir s = 0 then (1 : ℝ) else p₀ s / |dir s|) with heps
    have heps_pos : 0 < eps := (Finset.lt_inf'_iff _).2 fun s _ ↦ hstep_pos s
    have hshift : p₀ + eps • dir ∈ feasible observe observed := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro s
        by_cases hzero : dir s = 0
        · simpa [hzero] using hp₀.1.1 s
        · have hbound : eps ≤ p₀ s / |dir s| := by
            have hmem := Finset.inf'_le
              (f := fun t ↦ if dir t = 0 then (1 : ℝ) else p₀ t / |dir t|)
              (Finset.mem_univ s)
            rw [heps]
            simpa [hzero] using hmem
          have habs : (0 : ℝ) < |dir s| := abs_pos.mpr hzero
          have hmul : eps * |dir s| ≤ p₀ s := by
            have := mul_le_mul_of_nonneg_right hbound habs.le
            rwa [div_mul_cancel₀ _ (ne_of_gt habs)] at this
          have hneg : -|dir s| ≤ dir s := neg_abs_le _
          have : -(eps * |dir s|) ≤ eps * dir s := by nlinarith [heps_pos.le]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linarith
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, hp₀.1.2, ← Finset.mul_sum, hmass]
        ring
      · intro o
        rw [pairing_add, pairing_smul, hp₀.2 o, hobs o]
        ring
    have hequal := hident (p₀ + eps • dir) hshift p₀ hp₀ j
    rw [pairing_add, pairing_smul] at hequal
    have : eps * pairing (reportTable j) dir = 0 := by linarith
    rcases mul_eq_zero.1 this with hzero | hzero
    · exact absurd hzero (ne_of_gt heps_pos)
    · exact hzero
  · intro hinv p hp q hq j
    have hsupp : ∀ s, (∀ r ∈ feasible observe observed, r s = 0) → (p - q) s = 0 := by
      intro s hzero
      simp [hzero p hp, hzero q hq]
    have hmass : ∑ s, (p - q) s = 0 := by
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib, hp.1.2, hq.1.2, sub_self]
    have hobs : ∀ o, pairing (observe o) (p - q) = 0 := by
      intro o
      rw [pairing_sub, hp.2 o, hq.2 o, sub_self]
    have := hinv (p - q) hsupp hmass hobs j
    rw [pairing_sub] at this
    linarith

end

end Descent.Portability.ReportRegionCertificates

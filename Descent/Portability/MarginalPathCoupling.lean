/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportRegionCertificates
import Descent.Portability.FiniteGeneticTransition

assert_below Descent.Decision Descent.Program

/-!
# Completions of prescribed marginal path laws

Each coordinate of a finite architecture has a completely specified observed path law. A
joint path completion is any joint mass on the product of the coordinate path spaces whose
coordinate marginals are exactly those prescribed laws. This module writes that constraint
system as the linear information of `FiniteMetricIdentification.feasible`, so the whole
report-region apparatus applies to it verbatim, and proves the product coupling satisfies it,
which is DC Theorem 2.1's nonemptiness. It also identifies the dual variables: a potential
indexed by a coordinate and one of its paths pairs with a completion exactly through the sum
of per-coordinate potentials evaluated along the completed path, which is the shape of the
manuscript's dual constraint.

This is DC Theorem 2.1 (2.2), (2.4)-(2.6), obtained by instantiating
`ReportRegionCertificates`. It also proves DC Proposition 2.3 in its finite form: a joint
completion of the observation skeletons, refined coordinatewise and independently by
specified conditional laws, is a joint law whose every coordinate marginal is the original
coordinate law refined by its own conditional law, so each coordinate's complete path law is
preserved.

The coordinate path spaces are taken to be one common finite path space rather than one per
coordinate, which is the manuscript's setting after a common encoding; the constraint
system, the dual and the product coupling are unchanged by that choice. The hypotheses are
the manuscript's domain conditions: finitely many coordinates, a finite path space, and a
specified probability law per coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarginalPathCoupling

open FiniteMetricIdentification FiniteGeneticTransition

noncomputable section

variable {Coord Path : Type*} [Fintype Coord] [DecidableEq Coord] [Fintype Path]
  [DecidableEq Path]

/-- A product over coordinates, weighted by a function of one coordinate, sums against the
independent product to that coordinate's own weighted sum. This is the repeated finite
summation behind every marginal computation below. -/
theorem sum_prod_mul_coordinate (factor : Coord → Path → ℝ)
    (hone : ∀ j, ∑ x, factor j x = 1) (i : Coord) (weight : Path → ℝ) :
    ∑ ω : Coord → Path, (∏ j, factor j (ω j)) * weight (ω i) =
      ∑ x, factor i x * weight x := by
  classical
  have hfactor : ∀ ω : Coord → Path,
      (∏ j, if j = i then factor j (ω j) * weight (ω j) else factor j (ω j)) =
        (∏ j, factor j (ω j)) * weight (ω i) := by
    intro ω
    have herase : ∏ j ∈ Finset.univ.erase i,
        (if j = i then factor j (ω j) * weight (ω j) else factor j (ω j)) =
          ∏ j ∈ Finset.univ.erase i, factor j (ω j) :=
      Finset.prod_congr rfl fun j hj ↦ if_neg (Finset.ne_of_mem_erase hj)
    rw [← Finset.mul_prod_erase Finset.univ
        (fun j ↦ if j = i then factor j (ω j) * weight (ω j) else factor j (ω j))
        (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j ↦ factor j (ω j)) (Finset.mem_univ i),
      if_pos rfl, herase]
    ring
  have hprodsum : (∏ j : Coord, ∑ x : Path,
      (if j = i then factor j x * weight x else factor j x)) =
        ∑ ω : Coord → Path, ∏ j : Coord,
          (if j = i then factor j (ω j) * weight (ω j) else factor j (ω j)) :=
    Fintype.prod_sum fun j x ↦ if j = i then factor j x * weight x else factor j x
  have hterm : ∀ j : Coord,
      (∑ x, if j = i then factor j x * weight x else factor j x) =
        if j = i then (∑ x, factor j x * weight x) else 1 := by
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, hone j]
  have hkeep : ∏ j ∈ Finset.univ.erase i,
      (if j = i then (∑ x, factor j x * weight x) else (1 : ℝ)) =
        ∏ _j ∈ Finset.univ.erase i, (1 : ℝ) :=
    Finset.prod_congr rfl fun j hj ↦ if_neg (Finset.ne_of_mem_erase hj)
  rw [← Finset.sum_congr rfl fun ω _ ↦ hfactor ω, ← hprodsum,
    Finset.prod_congr rfl fun j _ ↦ hterm j,
    ← Finset.mul_prod_erase Finset.univ
      (fun j ↦ if j = i then (∑ x, factor j x * weight x) else (1 : ℝ))
      (Finset.mem_univ i),
    if_pos rfl, hkeep, Finset.prod_const_one, mul_one]

/-- The coordinate marginal constraint of DC (2.2), written as one linear summary per
coordinate and observed path. -/
def couplingObserve (i : Coord) (a : Path) (ω : Coord → Path) : ℝ :=
  if ω i = a then 1 else 0

/-- The prescribed value of that summary: the coordinate's own path mass. -/
def couplingObserved (marginal : Coord → FiniteReportLaw Path) (i : Coord) (a : Path) : ℝ :=
  (marginal i).mass a

/-- Pairing a completion with a coordinate marginal summary is exactly the coordinate
marginal of that completion. -/
theorem pairing_couplingObserve (i : Coord) (a : Path) (joint : (Coord → Path) → ℝ) :
    pairing (couplingObserve i a) joint =
      ∑ ω : Coord → Path, if ω i = a then joint ω else 0 := by
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  by_cases hω : ω i = a
  · simp [couplingObserve, hω]
  · simp [couplingObserve, hω]

/-- The independent product of the prescribed coordinate laws is a joint completion, so the
set of completions in DC (2.2) is nonempty. -/
theorem productCoupling_mem_feasible (marginal : Coord → FiniteReportLaw Path) :
    (piLaw marginal).mass ∈
      feasible (fun p : Coord × Path ↦ couplingObserve p.1 p.2)
        (fun p : Coord × Path ↦ couplingObserved marginal p.1 p.2) := by
  refine ⟨⟨fun ω ↦ (piLaw marginal).mass_nonneg ω, (piLaw marginal).mass_sum⟩, ?_⟩
  rintro ⟨i, a⟩
  rw [pairing]
  have hrewrite : ∀ ω : Coord → Path,
      couplingObserve i a ω * (piLaw marginal).mass ω =
        (∏ j, (marginal j).mass (ω j)) * (if ω i = a then (1 : ℝ) else 0) := by
    intro ω
    rw [couplingObserve, piLaw_mass]
    ring
  rw [Finset.sum_congr rfl fun ω _ ↦ hrewrite ω,
    sum_prod_mul_coordinate (fun j x ↦ (marginal j).mass x)
      (fun j ↦ (marginal j).mass_sum) i (fun x ↦ if x = a then (1 : ℝ) else 0)]
  simp [couplingObserved]

/-- DC (2.6): a potential indexed by a coordinate and one of its paths pairs with a
completion only through the sum of per-coordinate potentials along the completed path. -/
theorem couplingObserve_potential_sum (potential : Coord → Path → ℝ)
    (ω : Coord → Path) :
    ∑ p : Coord × Path, potential p.1 p.2 * couplingObserve p.1 p.2 ω =
      ∑ i, potential i (ω i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single (ω i)]
  · simp [couplingObserve]
  · intro a _ ha
    simp [couplingObserve, Ne.symm ha]
  · intro hno
    exact absurd (Finset.mem_univ (ω i)) hno

/-- DC (2.5): the dual objective is the prescribed marginal mass paired with the
per-coordinate potentials. -/
theorem couplingObserved_potential_value (marginal : Coord → FiniteReportLaw Path)
    (potential : Coord → Path → ℝ) :
    pairing (fun p : Coord × Path ↦ potential p.1 p.2)
        (fun p : Coord × Path ↦ couplingObserved marginal p.1 p.2) =
      ∑ i, ∑ a, potential i a * (marginal i).mass a := by
  rw [pairing, Fintype.sum_prod_type]
  rfl

/-- DC Theorem 2.1 and Corollary 2.2 for prescribed marginal path laws: a dual certificate
built from per-coordinate potentials bounds every attainable report contrast, and the
attainable region is nonempty because the product coupling is a completion. -/
theorem coupling_report_contrast_le_potential_value {ReportIdx : Type*} [Fintype ReportIdx]
    (marginal : Coord → FiniteReportLaw Path) (reportTable : ReportIdx → (Coord → Path) → ℝ)
    (contrast : ReportIdx → ℝ) (potential : Coord → Path → ℝ)
    (hdual : ∀ ω : Coord → Path,
      ∑ j, contrast j * reportTable j ω ≤ ∑ i, potential i (ω i))
    (report : ReportIdx → ℝ)
    (hreport : report ∈ ReportRegionCertificates.reportRegion
      (fun p : Coord × Path ↦ couplingObserve p.1 p.2)
      (fun p : Coord × Path ↦ couplingObserved marginal p.1 p.2) reportTable) :
    pairing contrast report ≤ ∑ i, ∑ a, potential i a * (marginal i).mass a := by
  have hbound := ReportRegionCertificates.report_contrast_le_dual_value
    (fun p : Coord × Path ↦ couplingObserve p.1 p.2)
    (fun p : Coord × Path ↦ couplingObserved marginal p.1 p.2) reportTable contrast
    (fun p : Coord × Path ↦ potential p.1 p.2)
    (fun ω ↦ by
      rw [couplingObserve_potential_sum potential ω]
      exact hdual ω) report hreport
  rwa [couplingObserved_potential_value marginal potential] at hbound

/-- DC Theorem 2.1: the attainable region of expected reports over the completions of the
prescribed marginal path laws is a nonempty compact convex set, every point of which is
attained by an actual joint completion. -/
theorem coupling_reportRegion_nonempty {ReportIdx : Type*}
    (marginal : Coord → FiniteReportLaw Path)
    (reportTable : ReportIdx → (Coord → Path) → ℝ) :
    (ReportRegionCertificates.reportRegion
      (fun p : Coord × Path ↦ couplingObserve p.1 p.2)
      (fun p : Coord × Path ↦ couplingObserved marginal p.1 p.2) reportTable).Nonempty :=
  ReportRegionCertificates.reportRegion_nonempty _ _ _
    ⟨_, productCoupling_mem_feasible marginal⟩

end

end Descent.Portability.MarginalPathCoupling

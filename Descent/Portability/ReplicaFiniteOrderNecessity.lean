/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaMomentCompleteness
import Descent.Portability.ObservableClosureLaw
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Pi

assert_below Descent.Decision Descent.Program

/-!
# Only polynomials of degree at most `n` are determined by size-`n` replica data

This is the necessity half of NOTE2 Theorem 3. Fix an alphabet of size `m` and a cohort size
`n`. `DeterminedAtOrder m n F` is the note's hypothesis: any two finitely supported mixing
laws on the simplex whose moments agree through total degree `n` report the same expectation
of `F`. The theorem `exists_moment_coefficients` says that such an `F` is exactly a linear
combination of the monomials of total degree at most `n`, and `determinedAtOrder_of_span` is
the converse, so the two together are the "iff" of NOTE2 Theorem 3 at fixed order.

The proof is the duality argument of the note, carried out through the corpus's
`ObservableClosureLaw.linear_factorization_iff`. Finitely supported signed measures on the
simplex form the vector space `simplex →₀ ℝ`; `momentMap` sends such a measure to its vector
of moments of degree at most `n` and `reportMap` sends it to the corresponding signed
expectation of `F`. The determinacy hypothesis is exactly the kernel inclusion
`ker momentMap ≤ ker reportMap`: a signed measure killed by the moment map has total mass
zero (the constant monomial is one of the coordinates), so splitting it into positive and
negative parts and dividing by their common total gives two genuine probability laws with
identical moments through degree `n`. The kernel inclusion produces a linear map on the
finite-dimensional moment space, and evaluating it on the canonical basis reads off the
coefficients.

Scope. The mixing laws in the hypothesis are finitely supported, which is what the note's
counterexample laws are and what makes the duality argument finite-dimensional; the statement
is therefore weaker as a hypothesis and so the conclusion is stronger. `F` is taken as a
function on the simplex itself rather than as a functional on the ambient space restricted to
it; the two formulations carry the same information. Nothing here is claimed about cohorts
that are not conditionally independent.

The monomials are `ReplicaMomentCompleteness.monomialMap`, so the two halves of NOTE2
Theorem 3 are stated against one and the same monomial family.

## Empirical status

None. The bodies here are algebra: `momentVector` is a stipulated vector of products, and
`DeterminedAtOrder` is a stipulated hypothesis about it, with no measured quantity anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReplicaFiniteOrderNecessity

open ReplicaMomentCompleteness

noncomputable section

/-! ### Exponent vectors of bounded total degree -/

/-- The exponent vectors on an alphabet of size `m` whose total degree is at most `n`. -/
def degreeSet (m n : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ ↦ Finset.range (n + 1)).filter fun e ↦ ∑ i, e i ≤ n

/-- Membership in the degree set is exactly the total-degree bound. -/
theorem mem_degreeSet (m n : ℕ) (e : Fin m → ℕ) : e ∈ degreeSet m n ↔ ∑ i, e i ≤ n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, h⟩
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans ?_ h))
    exact Finset.single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- The vector of monomial readouts of a probability vector, at every exponent vector of
total degree at most `n`. -/
def momentVector (m n : ℕ) (q : ↥(stdSimplex ℝ (Fin m))) : ↥(degreeSet m n) → ℝ :=
  fun e ↦ monomialMap m (e : Fin m → ℕ) q

/-- The moment vector is read off the monomial family of the completeness half. -/
theorem momentVector_eq_monomialMap (m n : ℕ) (q : ↥(stdSimplex ℝ (Fin m)))
    (e : ↥(degreeSet m n)) :
    momentVector m n q e = monomialMap m (e : Fin m → ℕ) q := rfl

/-- The moment vector's entries are the products the note writes down. -/
theorem momentVector_apply (m n : ℕ) (q : ↥(stdSimplex ℝ (Fin m))) (e : ↥(degreeSet m n)) :
    momentVector m n q e = ∏ i, (q : Fin m → ℝ) i ^ (e : Fin m → ℕ) i :=
  monomialMap_apply m _ q

/-- The constant monomial is one of the coordinates of the moment vector. -/
def zeroExponent (m n : ℕ) : ↥(degreeSet m n) :=
  ⟨0, (mem_degreeSet m n 0).mpr (by simp)⟩

/-- The constant coordinate of the moment vector is one, which is why a signed measure with
vanishing moments has total mass zero. -/
theorem momentVector_zeroExponent (m n : ℕ) (q : ↥(stdSimplex ℝ (Fin m))) :
    momentVector m n q (zeroExponent m n) = 1 := by
  rw [momentVector_apply]
  simp [zeroExponent]

/-! ### The two linear readouts of a finitely supported signed measure -/

/-- The moment readout of a finitely supported signed measure on the simplex. -/
def momentMap (m n : ℕ) :
    (↥(stdSimplex ℝ (Fin m)) →₀ ℝ) →ₗ[ℝ] (↥(degreeSet m n) → ℝ) :=
  Finsupp.linearCombination ℝ (momentVector m n)

/-- The signed expectation of a report under a finitely supported signed measure. -/
def reportMap (m : ℕ) (report : ↥(stdSimplex ℝ (Fin m)) → ℝ) :
    (↥(stdSimplex ℝ (Fin m)) →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ report

/-- The moment readout is the signed weighted sum of moment vectors. -/
theorem momentMap_apply (m n : ℕ) (signed : ↥(stdSimplex ℝ (Fin m)) →₀ ℝ)
    (e : ↥(degreeSet m n)) :
    momentMap m n signed e =
      ∑ q ∈ signed.support, signed q * momentVector m n q e := by
  simp only [momentMap, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun q _ ↦ rfl

/-- The report readout is the signed weighted sum of report values. -/
theorem reportMap_apply (m : ℕ) (report : ↥(stdSimplex ℝ (Fin m)) → ℝ)
    (signed : ↥(stdSimplex ℝ (Fin m)) →₀ ℝ) :
    reportMap m report signed = ∑ q ∈ signed.support, signed q * report q := by
  simp only [reportMap, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

/-! ### The determinacy hypothesis and its converse -/

/-- **NOTE2 Theorem 3, the hypothesis at fixed order.** Two finitely supported mixing laws
on the simplex whose moments agree through total degree `n` report the same expectation of
`report`.

Assumes: nothing about `report` beyond this property; `determinedAtOrder_of_span` constructs
report functions that satisfy it, so the hypothesis is not vacuous. -/
def DeterminedAtOrder (m n : ℕ) (report : ↥(stdSimplex ℝ (Fin m)) → ℝ) : Prop :=
  ∀ (source target : Finset ↥(stdSimplex ℝ (Fin m)))
    (weight weight' : ↥(stdSimplex ℝ (Fin m)) → ℝ),
    (∀ q ∈ source, 0 ≤ weight q) → ∑ q ∈ source, weight q = 1 →
    (∀ q ∈ target, 0 ≤ weight' q) → ∑ q ∈ target, weight' q = 1 →
    (∀ e : ↥(degreeSet m n),
      ∑ q ∈ source, weight q * momentVector m n q e =
        ∑ q ∈ target, weight' q * momentVector m n q e) →
    ∑ q ∈ source, weight q * report q = ∑ q ∈ target, weight' q * report q

/-- Expectations of a linear combination of moments reorganize as a linear combination of
moment expectations. -/
theorem sum_weighted_combination (m n : ℕ) (coefficient : ↥(degreeSet m n) → ℝ)
    (cells : Finset ↥(stdSimplex ℝ (Fin m))) (weight : ↥(stdSimplex ℝ (Fin m)) → ℝ) :
    ∑ q ∈ cells, weight q * ∑ e, coefficient e * momentVector m n q e =
      ∑ e, coefficient e * ∑ q ∈ cells, weight q * momentVector m n q e := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring

/-- **NOTE2 Theorem 3, sufficiency half.** Every linear combination of the monomials of total
degree at most `n` is determined by the size-`n` replica data, by linearity alone. This also
exhibits report functions satisfying `DeterminedAtOrder`. -/
theorem determinedAtOrder_of_span (m n : ℕ) (coefficient : ↥(degreeSet m n) → ℝ) :
    DeterminedAtOrder m n fun q ↦ ∑ e, coefficient e * momentVector m n q e := by
  intro source target weight weight' _ _ _ _ hmoment
  rw [sum_weighted_combination, sum_weighted_combination]
  exact Finset.sum_congr rfl fun e _ ↦ by rw [hmoment e]

/-! ### The duality step -/

/-- The determinacy hypothesis is exactly the kernel inclusion of the corpus's linear
factorization criterion: a signed measure with vanishing moments through degree `n` has
vanishing signed expectation of the report. -/
theorem ker_momentMap_le_ker_reportMap (m n : ℕ)
    (report : ↥(stdSimplex ℝ (Fin m)) → ℝ) (hdet : DeterminedAtOrder m n report) :
    LinearMap.ker (momentMap m n) ≤ LinearMap.ker (reportMap m report) := by
  intro signed hsigned
  rw [LinearMap.mem_ker] at hsigned ⊢
  rw [reportMap_apply]
  set cells := signed.support with hcells
  set positivePart : ↥(stdSimplex ℝ (Fin m)) → ℝ := fun q ↦ max (signed q) 0
    with hpositive
  set negativePart : ↥(stdSimplex ℝ (Fin m)) → ℝ := fun q ↦ max (-signed q) 0
    with hnegative
  have hsplit : ∀ q, signed q = positivePart q - negativePart q := by
    intro q
    simp only [hpositive, hnegative]
    rcases le_total (signed q) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hposnn : ∀ q, 0 ≤ positivePart q := fun q ↦ le_max_right _ _
  have hnegnn : ∀ q, 0 ≤ negativePart q := fun q ↦ le_max_right _ _
  have hmoment0 : ∀ e : ↥(degreeSet m n),
      ∑ q ∈ cells, signed q * momentVector m n q e = 0 := by
    intro e
    rw [← momentMap_apply, hsigned]
    rfl
  have hpair : ∀ e : ↥(degreeSet m n),
      ∑ q ∈ cells, positivePart q * momentVector m n q e =
        ∑ q ∈ cells, negativePart q * momentVector m n q e := by
    intro e
    have hzero : ∑ q ∈ cells, (positivePart q * momentVector m n q e -
        negativePart q * momentVector m n q e) = 0 := by
      rw [← hmoment0 e]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [hsplit q]; ring
    rw [Finset.sum_sub_distrib] at hzero
    linarith
  have hmass : ∑ q ∈ cells, positivePart q = ∑ q ∈ cells, negativePart q := by
    have h := hpair (zeroExponent m n)
    simpa only [momentVector_zeroExponent, mul_one] using h
  set total := ∑ q ∈ cells, positivePart q with htotal
  have htotalnn : 0 ≤ total := Finset.sum_nonneg fun q _ ↦ hposnn q
  have hgoal : ∑ q ∈ cells, positivePart q * report q =
      ∑ q ∈ cells, negativePart q * report q := by
    rcases eq_or_lt_of_le htotalnn with hzero | hpos
    · have hpz : ∀ q ∈ cells, positivePart q = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hposnn q).mp htotal.symm ▸
          (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hposnn q).mp hzero.symm
      have hnz : ∀ q ∈ cells, negativePart q = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hnegnn q).mp (hmass ▸ hzero.symm)
      rw [Finset.sum_congr rfl fun q hq ↦ by rw [hpz q hq]; ring,
        Finset.sum_congr rfl fun q hq ↦ by rw [hnz q hq]; ring]
    · have hne : total ≠ 0 := ne_of_gt hpos
      have hsum1 : ∑ q ∈ cells, positivePart q / total = 1 := by
        rw [← Finset.sum_div, ← htotal, div_self hne]
      have hsum2 : ∑ q ∈ cells, negativePart q / total = 1 := by
        rw [← Finset.sum_div, ← hmass, ← htotal, div_self hne]
      have hscaled : ∀ e : ↥(degreeSet m n),
          ∑ q ∈ cells, positivePart q / total * momentVector m n q e =
            ∑ q ∈ cells, negativePart q / total * momentVector m n q e := by
        intro e
        have hl : ∑ q ∈ cells, positivePart q / total * momentVector m n q e =
            (∑ q ∈ cells, positivePart q * momentVector m n q e) / total := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun q _ ↦ by ring
        have hr : ∑ q ∈ cells, negativePart q / total * momentVector m n q e =
            (∑ q ∈ cells, negativePart q * momentVector m n q e) / total := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun q _ ↦ by ring
        rw [hl, hr, hpair e]
      have hdiv := hdet cells cells (fun q ↦ positivePart q / total)
        (fun q ↦ negativePart q / total) (fun q _ ↦ div_nonneg (hposnn q) htotalnn) hsum1
        (fun q _ ↦ div_nonneg (hnegnn q) htotalnn) hsum2 hscaled
      have hl : ∑ q ∈ cells, positivePart q / total * report q =
          (∑ q ∈ cells, positivePart q * report q) / total := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun q _ ↦ by ring
      have hr : ∑ q ∈ cells, negativePart q / total * report q =
          (∑ q ∈ cells, negativePart q * report q) / total := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun q _ ↦ by ring
      rw [hl, hr] at hdiv
      exact (div_left_injective₀ hne) hdiv
  have hfinal : ∑ q ∈ cells, signed q * report q =
      ∑ q ∈ cells, positivePart q * report q -
        ∑ q ∈ cells, negativePart q * report q := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [hsplit q]; ring
  rw [hfinal, hgoal, sub_self]

/-- **NOTE2 Theorem 3, necessity half.** A report determined by size-`n` replica data for
every finitely supported mixing law is a linear combination of the monomials of total degree
at most `n`. Together with `determinedAtOrder_of_span` this is the note's "iff". -/
theorem exists_moment_coefficients (m n : ℕ) (report : ↥(stdSimplex ℝ (Fin m)) → ℝ)
    (hdet : DeterminedAtOrder m n report) :
    ∃ coefficient : ↥(degreeSet m n) → ℝ,
      ∀ q, report q = ∑ e, coefficient e * momentVector m n q e := by
  classical
  obtain ⟨update, hupdate⟩ :=
    (ObservableClosureLaw.linear_factorization_iff (momentMap m n) (reportMap m report)).mpr
      (ker_momentMap_le_ker_reportMap m n report hdet)
  refine ⟨fun e ↦ update (Pi.single e 1), fun q ↦ ?_⟩
  have hpoint : report q = update (momentVector m n q) := by
    have hcomp := congrArg
      (fun L : (↥(stdSimplex ℝ (Fin m)) →₀ ℝ) →ₗ[ℝ] ℝ ↦ L (Finsupp.single q 1)) hupdate
    simp only [LinearMap.comp_apply] at hcomp
    rw [momentMap, reportMap, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul] at hcomp
    exact hcomp.symm
  have hexpand : momentVector m n q =
      ∑ e, momentVector m n q e • Pi.single (M := fun _ : ↥(degreeSet m n) ↦ ℝ) e 1 :=
    pi_eq_sum_univ' (momentVector m n q)
  calc report q = update (momentVector m n q) := hpoint
    _ = update (∑ e, momentVector m n q e •
          Pi.single (M := fun _ : ↥(degreeSet m n) ↦ ℝ) e 1) := by rw [← hexpand]
    _ = ∑ e, momentVector m n q e •
          update (Pi.single (M := fun _ : ↥(degreeSet m n) ↦ ℝ) e 1) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun e _ ↦ map_smul _ _ _
    _ = ∑ e, update (Pi.single (M := fun _ : ↥(degreeSet m n) ↦ ℝ) e 1) *
          momentVector m n q e :=
        Finset.sum_congr rfl fun e _ ↦ by rw [smul_eq_mul]; ring

end

end Descent.Portability.ReplicaFiniteOrderNecessity

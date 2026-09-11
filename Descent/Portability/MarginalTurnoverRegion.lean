/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverDependence
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.Compact

assert_below Descent.Decision Descent.Program

/-!
# The complete finite marginal-turnover problem

TQ Theorem 3.9 fixes the score weights, the effects and the one-locus sign means
and asks for the exact attainable range of expected accuracy over all joint sign
laws with those means. The feasible set is the finite polytope (3.15) of
nonnegative weight vectors on the sign cube with unit mass and the prescribed
coordinate means; the objective (3.14) is the expectation of the population `R²`
of `TurnoverDependence.turnoverWorld`, which is linear in the weight vector.
The attainable set of values is proved to be exactly a closed interval, with
both endpoints attained: the feasible set is nonempty (the independent product
law with the prescribed means), compact and convex, so its image under the
linear objective is a compact connected subset of the line. No fitted retention
parameter enters; the hypotheses are only that the prescribed means lie in
`[-1,1]`.

## Empirical status

None. The bodies here are algebra and topology: a weight vector on the sign cube
and a vector of prescribed one-locus means are inputs, and every definition is a
product, a sum or a feasibility condition on them. No definition names a
measurable quantity or carries a fitted constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarginalTurnoverRegion

open Foundations TurnoverDependence

noncomputable section

section ProductLaw

/-- The product sign law with a prescribed mean at each locus. -/
def productSign (n : ℕ) (mrg : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∏ i, (1 + mrg i * sgn (z i)) / 2

/-- The equal-mean product law of `TurnoverDependence` is the constant-marginal case of
`productSign`. -/
theorem bernoulliSign_eq_productSign (n : ℕ) (m : ℝ) (z : Fin n → Bool) :
    bernoulliSign n m z = productSign n (fun _ ↦ m) z := rfl

/-- The product sign law is a nonnegative weight vector. -/
theorem productSign_nonneg {n : ℕ} {mrg : Fin n → ℝ} (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1)
    (z : Fin n → Bool) : 0 ≤ productSign n mrg z := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  rcases sgn_cases (z i) with h | h <;> rw [h] <;> [linarith [(hm i).1, (hm i).2];
    linarith [(hm i).1, (hm i).2]]

/-- The product sign law has total mass one. -/
theorem sum_productSign (n : ℕ) (mrg : Fin n → ℝ) :
    ∑ z : Fin n → Bool, productSign n mrg z = 1 := by
  unfold productSign
  rw [sum_prod_bool fun l b ↦ (1 + mrg l * sgn b) / 2]
  refine (Finset.prod_congr rfl fun i _ ↦ ?_).trans Finset.prod_const_one
  rw [sgn_true, sgn_false]
  ring

/-- Locus `i` has mean `mrg i` under the product sign law. -/
theorem sum_productSign_sgn {n : ℕ} (mrg : Fin n → ℝ) (i : Fin n) :
    ∑ z : Fin n → Bool, productSign n mrg z * sgn (z i) = mrg i := by
  have hrw : ∀ z : Fin n → Bool, productSign n mrg z * sgn (z i)
      = ∏ l, ((1 + mrg l * sgn (z l)) / 2 * (if l = i then sgn (z l) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib, prod_one_index i fun l ↦ sgn (z l)]
    rfl
  rw [Finset.sum_congr rfl fun z _ ↦ hrw z,
    sum_prod_bool fun l b ↦ (1 + mrg l * sgn b) / 2 * (if l = i then sgn b else 1)]
  have hfac : ∀ l : Fin n,
      (1 + mrg l * sgn true) / 2 * (if l = i then sgn true else 1)
        + (1 + mrg l * sgn false) / 2 * (if l = i then sgn false else 1)
      = if l = i then mrg l else 1 := by
    intro l
    by_cases h : l = i
    · rw [if_pos h, if_pos h, if_pos h, sgn_true, sgn_false]
      ring
    · rw [if_neg h, if_neg h, if_neg h, sgn_true, sgn_false]
      ring
  rw [Finset.prod_congr rfl fun l _ ↦ hfac l, prod_one_index i mrg]

end ProductLaw

section FeasibleSet

/-- **The marginal-turnover polytope (3.15).**  A nonnegative weight vector on the sign
cube with unit mass and the prescribed one-locus sign means. -/
def MarginalFeasible (n : ℕ) (mrg : Fin n → ℝ) (p : (Fin n → Bool) → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ (∑ z, p z = 1) ∧ ∀ i, ∑ z, p z * sgn (z i) = mrg i

/-- **The polytope is nonempty**: independent signs with the prescribed means are feasible.
This is the witness that the feasibility hypothesis below is not vacuous. -/
theorem productSign_feasible (n : ℕ) (mrg : Fin n → ℝ)
    (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1) : MarginalFeasible n mrg (productSign n mrg) :=
  ⟨productSign_nonneg hm, sum_productSign n mrg, sum_productSign_sgn mrg⟩

/-- A feasible weight vector is a genuine expectation functional, and the objective is the
expectation it assigns.

Assumes: `MarginalFeasible n mrg p`, witnessed by `productSign_feasible`. -/
theorem feasible_expectation_eq {n : ℕ} {mrg : Fin n → ℝ} {p : (Fin n → Bool) → ℝ}
    (hp : MarginalFeasible n mrg p) (g : (Fin n → Bool) → ℝ) :
    weightedExp p hp.1 hp.2.1 g = ∑ z, p z * g z := rfl

/-- The polytope is a closed subset of the weight space. -/
theorem marginalFeasible_isClosed (n : ℕ) (mrg : Fin n → ℝ) :
    IsClosed {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p} := by
  have h1 : IsClosed {p : (Fin n → Bool) → ℝ | ∀ z, 0 ≤ p z} := by
    have hset : {p : (Fin n → Bool) → ℝ | ∀ z, 0 ≤ p z} = ⋂ z, {p | 0 ≤ p z} := by
      ext p
      simp
    rw [hset]
    exact isClosed_iInter fun z ↦ isClosed_le continuous_const (continuous_apply z)
  have h2 : IsClosed {p : (Fin n → Bool) → ℝ | ∑ z, p z = 1} :=
    isClosed_eq (continuous_finset_sum _ fun z _ ↦ continuous_apply z) continuous_const
  have h3 : IsClosed {p : (Fin n → Bool) → ℝ | ∀ i, ∑ z, p z * sgn (z i) = mrg i} := by
    have hset : {p : (Fin n → Bool) → ℝ | ∀ i, ∑ z, p z * sgn (z i) = mrg i}
        = ⋂ i, {p | ∑ z, p z * sgn (z i) = mrg i} := by
      ext p
      simp
    rw [hset]
    refine isClosed_iInter fun i ↦ isClosed_eq ?_ continuous_const
    exact continuous_finset_sum _ fun z _ ↦ (continuous_apply z).mul continuous_const
  have heq : {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p}
      = {p : (Fin n → Bool) → ℝ | ∀ z, 0 ≤ p z}
        ∩ ({p : (Fin n → Bool) → ℝ | ∑ z, p z = 1}
          ∩ {p : (Fin n → Bool) → ℝ | ∀ i, ∑ z, p z * sgn (z i) = mrg i}) := rfl
  rw [heq]
  exact h1.inter (h2.inter h3)

/-- The polytope is compact. -/
theorem marginalFeasible_isCompact (n : ℕ) (mrg : Fin n → ℝ) :
    IsCompact {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p} := by
  have hsub : {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p}
      ⊆ Set.univ.pi fun _ ↦ Set.Icc (0 : ℝ) 1 := by
    intro p hp z _
    have hp' : MarginalFeasible n mrg p := hp
    refine Set.mem_Icc.mpr ⟨hp'.1 z, ?_⟩
    have h := Finset.single_le_sum (f := p) (fun w _ ↦ hp'.1 w) (Finset.mem_univ z)
    rw [hp'.2.1] at h
    exact h
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset
    (marginalFeasible_isClosed n mrg) hsub

/-- The polytope is convex. -/
theorem marginalFeasible_convex (n : ℕ) (mrg : Fin n → ℝ) :
    Convex ℝ {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p} := by
  intro p hp q hq c d hc hd hcd
  have hp' : MarginalFeasible n mrg p := hp
  have hq' : MarginalFeasible n mrg q := hq
  have hval : ∀ z : Fin n → Bool, (c • p + d • q) z = c * p z + d * q z := fun _ ↦ rfl
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [hval z]
    exact add_nonneg (mul_nonneg hc (hp'.1 z)) (mul_nonneg hd (hq'.1 z))
  · rw [Finset.sum_congr rfl fun z _ ↦ hval z, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hp'.2.1, hq'.2.1, mul_one, mul_one]
    exact hcd
  · intro i
    have hrw : ∀ z : Fin n → Bool, (c • p + d • q) z * sgn (z i)
        = c * (p z * sgn (z i)) + d * (q z * sgn (z i)) := by
      intro z
      rw [hval z]
      ring
    rw [Finset.sum_congr rfl fun z _ ↦ hrw z, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hp'.2.2 i, hq'.2.2 i, ← add_mul, hcd, one_mul]

end FeasibleSet

section IntervalImage

/-- **A linear objective on a nonempty compact convex set of weight vectors attains exactly
a closed interval.**  This is the shape of every "exact attainable range" statement over a
finite identification polytope. -/
theorem linear_range_is_interval {α : Type*} [Fintype α] (Sset : Set (α → ℝ))
    (hne : Sset.Nonempty) (hcomp : IsCompact Sset) (hconv : Convex ℝ Sset) (f : α → ℝ) :
    ∃ lo hi : ℝ, lo ≤ hi ∧ {y | ∃ p ∈ Sset, ∑ a, p a * f a = y} = Set.Icc lo hi := by
  have hcont : Continuous fun p : α → ℝ ↦ ∑ a, p a * f a :=
    continuous_finset_sum _ fun a _ ↦ (continuous_apply a).mul continuous_const
  have himg : IsCompact ((fun p : α → ℝ ↦ ∑ a, p a * f a) '' Sset) := hcomp.image hcont
  have hconn : IsConnected ((fun p : α → ℝ ↦ ∑ a, p a * f a) '' Sset) :=
    ⟨hne.image _, hconv.isPreconnected.image _ hcont.continuousOn⟩
  refine ⟨sInf ((fun p : α → ℝ ↦ ∑ a, p a * f a) '' Sset),
    sSup ((fun p : α → ℝ ↦ ∑ a, p a * f a) '' Sset), ?_, ?_⟩
  · exact le_csSup himg.bddAbove (himg.sInf_mem hconn.nonempty)
  · rw [← eq_Icc_of_connected_compact hconn himg]
    rfl

end IntervalImage

section ExactRange

variable {n : ℕ}

/-- The objective (3.14): the expected population accuracy of a joint sign law, written out
from the master `R²` formula rather than postulated. -/
theorem objective_eq_formula (w b : Fin n → ℝ) (sigma : ℝ) (p : (Fin n → Bool) → ℝ) :
    ∑ z, p z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w
      = ∑ z, p z * ((∑ i, w i * b i * sgn (z i)) ^ 2
          / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))) :=
  Finset.sum_congr rfl fun z _ ↦ by
    rw [turnoverWorld_r2 b sigma (fun i ↦ sgn (z i)) w fun i ↦ sgn_cases (z i)]

/-- **TQ Theorem 3.9.**  At fixed weights, effects and one-locus sign means, the exact
attainable set of expected accuracy is the closed interval between the minimum and the
maximum of (3.14) on the polytope (3.15), and both endpoints are attained.

Assumes: `MarginalFeasible n mrg`, witnessed by `productSign_feasible`. -/
theorem marginal_turnover_range (w b : Fin n → ℝ) (sigma : ℝ) (mrg : Fin n → ℝ)
    (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1) :
    ∃ lo hi : ℝ, lo ≤ hi ∧
      {y | ∃ p, MarginalFeasible n mrg p ∧
          ∑ z, p z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w = y}
        = Set.Icc lo hi := by
  obtain ⟨lo, hi, hle, hset⟩ := linear_range_is_interval
    {p : (Fin n → Bool) → ℝ | MarginalFeasible n mrg p}
    ⟨productSign n mrg, productSign_feasible n mrg hm⟩
    (marginalFeasible_isCompact n mrg) (marginalFeasible_convex n mrg)
    (fun z ↦ (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w)
  refine ⟨lo, hi, hle, ?_⟩
  rw [← hset]
  ext y
  simp only [Set.mem_setOf_eq]

/-- **Both extremal laws exist.**  The minimum and the maximum of (3.14) on the polytope are
attained by joint sign laws with exactly the prescribed one-locus means. -/
theorem marginal_turnover_extrema (w b : Fin n → ℝ) (sigma : ℝ) (mrg : Fin n → ℝ)
    (hm : ∀ i, -1 ≤ mrg i ∧ mrg i ≤ 1) :
    ∃ pmin pmax : (Fin n → Bool) → ℝ, MarginalFeasible n mrg pmin ∧
      MarginalFeasible n mrg pmax ∧
      ∀ p, MarginalFeasible n mrg p →
        ∑ z, pmin z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w
            ≤ ∑ z, p z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w ∧
          ∑ z, p z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w
            ≤ ∑ z, pmax z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w := by
  obtain ⟨lo, hi, hle, hset⟩ := marginal_turnover_range w b sigma mrg hm
  have hlo : lo ∈ Set.Icc lo hi := Set.left_mem_Icc.mpr hle
  have hhi : hi ∈ Set.Icc lo hi := Set.right_mem_Icc.mpr hle
  rw [← hset] at hlo hhi
  obtain ⟨pmin, hpmin, hvmin⟩ := hlo
  obtain ⟨pmax, hpmax, hvmax⟩ := hhi
  refine ⟨pmin, pmax, hpmin, hpmax, fun p hp ↦ ?_⟩
  have hmem : (∑ z, p z * (turnoverWorld b sigma fun i ↦ sgn (z i)).r2 w) ∈ Set.Icc lo hi := by
    rw [← hset]
    exact ⟨p, hp, rfl⟩
  rw [hvmin, hvmax]
  exact ⟨hmem.1, hmem.2⟩

end ExactRange

end

end Descent.Portability.MarginalTurnoverRegion

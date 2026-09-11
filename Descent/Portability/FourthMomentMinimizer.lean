/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# The fourth-moment minimum is attained

UPT Theorem 3.1(a) asserts that the infimum `V(β, k, m)` of (3.5) is a minimum. The
manuscript's Step 3 argues this by weak compactness in `L⁴ × L²`. For a finitely supported
pre-outcome law the same conclusion is elementary and needs no functional analysis: the
feasible set of pairs `(b, a)` is a closed subset of a finite-dimensional space, and the
constraints `a ≥ b²`, `E a = m` with strictly positive weights bound both coordinates, so
it is compact; the objective `E[a²]` is continuous, hence attains its minimum there.

* `feasibleSet` is the constraint set (3.6) as a subset of `(Ω → ℝ) × (Ω → ℝ)`.
* `isClosed_feasibleSet` and `isCompact_feasibleSet` establish the compactness, with the
  explicit box `[-R, R]` given by `R = Σ_ω m/p_ω + 1`.
* `minFourthMoment_attained` produces an actual minimizing pair, so `V(β, k, m)` is a value
  of the program and not merely its infimum.
* `exists_minimizer` combines this with `GlobalFourthMomentRegion.slackPair_feasible`, so
  the only hypotheses left are UPT (3.1) orthonormality and UPT (3.4) feasibility.

The finitely supported laws of the corpus satisfy the representation hypothesis used
throughout: `weightedExp` is literally a weighted sum, which is
`PortabilityMasterTheorem.weightedExp_apply`.

Together with `GlobalFourthMomentRegion.minFourthMoment_eq_of_certificate` this separates
the two things Theorem 3.1(a) claims: that a minimizer exists, proved here for finite
support, and that a particular pair is one, proved there by a dual certificate for an
arbitrary law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourthMomentMinimizer

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion

noncomputable section

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constraint set (3.6) of UPT Theorem 3.1(a), as a subset of the finite-dimensional
space of pairs of conditional-moment functions. -/
def feasibleSet (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) :
    Set ((Ω → ℝ) × (Ω → ℝ)) :=
  {q | (∀ ω, q.1 ω ^ 2 ≤ q.2 ω) ∧ E q.1 = β ∧
    (∀ i, E (fun ω ↦ X ω i * q.1 ω) = k i) ∧ E q.2 = m}

omit [Fintype ι] [DecidableEq ι] in
/-- A finitely supported expectation is continuous in the observable it integrates. -/
theorem continuous_of_repr (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω)
    (F : (Ω → ℝ) × (Ω → ℝ) → Ω → ℝ) (hF : ∀ ω, Continuous fun q ↦ F q ω) :
    Continuous fun q ↦ E (F q) := by
  have hfun : (fun q ↦ E (F q)) = fun q ↦ ∑ ω, p ω * F q ω := by
    funext q
    exact hE (F q)
  rw [hfun]
  exact continuous_finset_sum _ fun ω _ ↦ continuous_const.mul (hF ω)

omit [Fintype ι] [DecidableEq ι] in
/-- The constraint set is closed: every constraint is an equality or a nonstrict inequality
between continuous functions of the pair. -/
theorem isClosed_feasibleSet (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) : IsClosed (feasibleSet E X β k m) := by
  have hfst : ∀ ω : Ω, Continuous fun q : (Ω → ℝ) × (Ω → ℝ) ↦ q.1 ω :=
    fun ω ↦ (continuous_apply ω).comp continuous_fst
  have hsnd : ∀ ω : Ω, Continuous fun q : (Ω → ℝ) × (Ω → ℝ) ↦ q.2 ω :=
    fun ω ↦ (continuous_apply ω).comp continuous_snd
  have h1 : IsClosed {q : (Ω → ℝ) × (Ω → ℝ) | ∀ ω, q.1 ω ^ 2 ≤ q.2 ω} := by
    have hrw : {q : (Ω → ℝ) × (Ω → ℝ) | ∀ ω, q.1 ω ^ 2 ≤ q.2 ω}
        = ⋂ ω : Ω, {q : (Ω → ℝ) × (Ω → ℝ) | q.1 ω ^ 2 ≤ q.2 ω} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    exact isClosed_iInter fun ω ↦ isClosed_le ((hfst ω).pow 2) (hsnd ω)
  have h2 : IsClosed {q : (Ω → ℝ) × (Ω → ℝ) | E q.1 = β} :=
    isClosed_eq (continuous_of_repr E p hE (fun q ↦ q.1) hfst) continuous_const
  have h3 : IsClosed
      {q : (Ω → ℝ) × (Ω → ℝ) | ∀ i, E (fun ω ↦ X ω i * q.1 ω) = k i} := by
    have hrw : {q : (Ω → ℝ) × (Ω → ℝ) | ∀ i, E (fun ω ↦ X ω i * q.1 ω) = k i}
        = ⋂ i : ι, {q : (Ω → ℝ) × (Ω → ℝ) | E (fun ω ↦ X ω i * q.1 ω) = k i} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hrw]
    refine isClosed_iInter fun i ↦ isClosed_eq ?_ continuous_const
    exact continuous_of_repr E p hE (fun q ω ↦ X ω i * q.1 ω)
      (fun ω ↦ continuous_const.mul (hfst ω))
  have h4 : IsClosed {q : (Ω → ℝ) × (Ω → ℝ) | E q.2 = m} :=
    isClosed_eq (continuous_of_repr E p hE (fun q ↦ q.2) hsnd) continuous_const
  have hrw : feasibleSet E X β k m
      = {q : (Ω → ℝ) × (Ω → ℝ) | ∀ ω, q.1 ω ^ 2 ≤ q.2 ω}
        ∩ ({q : (Ω → ℝ) × (Ω → ℝ) | E q.1 = β}
          ∩ ({q : (Ω → ℝ) × (Ω → ℝ) | ∀ i, E (fun ω ↦ X ω i * q.1 ω) = k i}
            ∩ {q : (Ω → ℝ) × (Ω → ℝ) | E q.2 = m})) := by
    ext q
    constructor
    · rintro ⟨ha, hb, hc, hd⟩
      exact ⟨ha, hb, hc, hd⟩
    · rintro ⟨ha, hb, hc, hd⟩
      exact ⟨ha, hb, hc, hd⟩
  rw [hrw]
  exact h1.inter (h2.inter (h3.inter h4))

omit [Fintype ι] [DecidableEq ι] in
/-- **The constraint set is compact.** With strictly positive weights, `E a = m` bounds
each `a(ω)` by `m / p(ω)`, and `a ≥ b²` then bounds each `b(ω)`; the set sits inside an
explicit box. -/
theorem isCompact_feasibleSet (E : ExpFunctional Ω) (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) : IsCompact (feasibleSet E X β k m) := by
  rcases Set.eq_empty_or_nonempty (feasibleSet E X β k m) with hempty | hnonempty
  · rw [hempty]
    exact isCompact_empty
  obtain ⟨q₁, hq₁⟩ := hnonempty
  have hm : 0 ≤ m := by
    rw [← hq₁.2.2.2]
    exact E.nonneg_eval _ fun ω ↦ le_trans (sq_nonneg (q₁.1 ω)) (hq₁.1 ω)
  set R := (∑ ω, m / p ω) + 1 with hRdef
  have hsumnn : 0 ≤ ∑ ω, m / p ω :=
    Finset.sum_nonneg fun ω _ ↦ div_nonneg hm (hp ω).le
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hRdef]
    linarith
  have hsub : feasibleSet E X β k m ⊆
      (Set.univ.pi fun _ : Ω ↦ Set.Icc (-R) R) ×ˢ
        (Set.univ.pi fun _ : Ω ↦ Set.Icc (-R) R) := by
    rintro q ⟨hq1, -, -, hq4⟩
    have hnn : ∀ ω, 0 ≤ q.2 ω := fun ω ↦ le_trans (sq_nonneg _) (hq1 ω)
    have hbound : ∀ ω, q.2 ω ≤ R := by
      intro ω
      have hterm : p ω * q.2 ω ≤ m := by
        rw [← hq4, hE]
        exact Finset.single_le_sum (f := fun ω' ↦ p ω' * q.2 ω')
          (fun ω' _ ↦ mul_nonneg (hp ω').le (hnn ω')) (Finset.mem_univ ω)
      have h1 : q.2 ω ≤ m / p ω := by
        rw [le_div_iff₀ (hp ω)]
        linarith
      have h2 : m / p ω ≤ ∑ ω', m / p ω' :=
        Finset.single_le_sum (f := fun ω' ↦ m / p ω')
          (fun ω' _ ↦ div_nonneg hm (hp ω').le) (Finset.mem_univ ω)
      rw [hRdef]
      linarith
    refine Set.mem_prod.mpr ⟨Set.mem_univ_pi.mpr fun ω ↦ ?_,
      Set.mem_univ_pi.mpr fun ω ↦ ⟨by linarith [hnn ω], hbound ω⟩⟩
    have hsq : q.1 ω ^ 2 ≤ R := le_trans (hq1 ω) (hbound ω)
    have hsq2 : q.1 ω ^ 2 ≤ R ^ 2 := by nlinarith
    have habs : |q.1 ω| ≤ R := by
      have h1 : Real.sqrt (q.1 ω ^ 2) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hsq2
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ R)] at h1
    exact abs_le.mp habs
  have hK : IsCompact ((Set.univ.pi fun _ : Ω ↦ Set.Icc (-R) R) ×ˢ
      (Set.univ.pi fun _ : Ω ↦ Set.Icc (-R) R)) :=
    (isCompact_univ_pi fun _ ↦ isCompact_Icc).prod (isCompact_univ_pi fun _ ↦ isCompact_Icc)
  exact hK.of_isClosed_subset (isClosed_feasibleSet E p hE X β k m) hsub

omit [Fintype ι] [DecidableEq ι] in
/-- **The infimum of UPT (3.5) is a minimum, for a finitely supported law with positive
weights.** There is an actual feasible pair whose objective equals `V(β, k, m)`. -/
theorem minFourthMoment_attained (E : ExpFunctional Ω) (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hne : (feasibleSet E X β k m).Nonempty) :
    ∃ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) ∧ E b = β ∧
      (∀ i, E (fun ω ↦ X ω i * b ω) = k i) ∧ E a = m ∧
      minFourthMoment E X β k m = E (fun ω ↦ a ω ^ 2) := by
  have hcont : Continuous fun q : (Ω → ℝ) × (Ω → ℝ) ↦ E (fun ω ↦ q.2 ω ^ 2) :=
    continuous_of_repr E p hE (fun q ω ↦ q.2 ω ^ 2)
      (fun ω ↦ (((continuous_apply ω).comp continuous_snd)).pow 2)
  obtain ⟨q₀, hq₀mem, hq₀min⟩ :=
    (isCompact_feasibleSet E p hp hE X β k m).exists_isMinOn hne hcont.continuousOn
  obtain ⟨h1, h2, h3, h4⟩ := hq₀mem
  refine ⟨q₀.1, q₀.2, h1, h2, h3, h4, ?_⟩
  refine IsLeast.csInf_eq ⟨⟨q₀.1, q₀.2, h1, h2, h3, h4, rfl⟩, ?_⟩
  rintro v ⟨b', a', hab', hb', hk', ha', rfl⟩
  exact isMinOn_iff.mp hq₀min (b', a') ⟨hab', hb', hk', ha'⟩

omit [Fintype Ω] in
/-- Feasibility in the sense of UPT (3.4) makes the constraint set nonempty, via the
explicit pair of Step 1. -/
theorem feasibleSet_nonempty (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hfeas : β ^ 2 + dot k k ≤ m) :
    (feasibleSet E X β k m).Nonempty := by
  obtain ⟨h1, h2, h3, h4⟩ := slackPair_feasible E X β k m hmean horth hfeas
  exact ⟨(featureMean β k X, slackSecond β k X m), h1, h2, h3, h4⟩

/-- **Attainment of the fourth-moment minimum under the manuscript's own hypotheses.** For
a finitely supported law with positive weights, orthonormal features, and a feasible triple
in the sense of UPT (3.4), the value `V(β, k, m)` is attained by an explicit pair. -/
theorem exists_minimizer (E : ExpFunctional Ω) (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hfeas : β ^ 2 + dot k k ≤ m) :
    ∃ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) ∧ E b = β ∧
      (∀ i, E (fun ω ↦ X ω i * b ω) = k i) ∧ E a = m ∧
      minFourthMoment E X β k m = E (fun ω ↦ a ω ^ 2) :=
  minFourthMoment_attained E p hp hE X β k m
    (feasibleSet_nonempty E X β k m hmean horth hfeas)

end

end Descent.Portability.FourthMomentMinimizer

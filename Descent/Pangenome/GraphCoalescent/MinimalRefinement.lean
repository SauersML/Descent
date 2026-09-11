/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Data.Fintype.Card

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The coarsest predictive Markov refinement of a pangenome report

Theorem A of the hidden-lineage clock restores, for each reported component `C`, the number `L_C`
of unresolved ancestral lineages inside it, and shows that the report together with these loads is
a strong lumping of the labeled Kingman chain: invisible mergers inside `C` at rate `C(L_C, 2)` and
visible mergers between `C` and `D` at rate `ρ_CD = L_C L_D`. Theorem B says how much of that load
information any predictive Markov refinement of the report must keep: every labeled load while the
report has at least three components, only the unordered pair of loads with two components, and
nothing once the report is connected. This module proves the necessity and sufficiency algebra of
Theorem B and states minimality in terms of the report-visible rates.

**(B1).** `load_sq_mul_visibleRate` is `L_C² ρ_DE = ρ_CD ρ_CE` and `load_sq_eq_visibleRates` its
division form `L_C² = ρ_CD ρ_CE / ρ_DE`. `load_eq_of_visibleRates_eq` concludes that two positive
load assignments on at least three components with the same visible merger rates between distinct
components are equal, and `visibleRates_eq_iff` is the equivalence.

**(B2).** `twoComponentGenerator` is the generator of the two-component load chain killed at the
visible merger. The survival `S_{a,b}` of the absorbing merger solves the backward equation of this
generator, so its derivatives at time zero are the generator's iterates applied to the constant one:
`twoComponentGenerator_one` is `S'(0) = -ab` and `twoComponentGenerator_twice_one` is
`S''(0) = (ab)² + C(a,2) b + C(b,2) a = (ab)² + ab(a + b - 2)/2`.
`unorderedPair_of_survivalDerivatives_eq` shows that these two numbers determine the unordered pair
`{a, b}`, and `survivalDerivatives_swap` that they cannot determine the order;
`survivalDerivatives_eq_iff` is the equivalence.

**Sufficiency.** For three or more components the loads are Theorem A. With two components
`twoComponentGenerator_swap` shows that the killed generator commutes with exchanging the two
components, so the unordered pair of loads is a strong lumping of the two-component chain. With one
component every merger is invisible and the report is constant. `killingRate_add_invisibleRates`
records that, with two components, the killing rate and the two invisible rates add up to the
Kingman death rate `Coalescent.deathRate (a + b)` of all hidden lineages, which is (A3) at `r = 2`.

**Minimality.** `refines_loads` and `refines_unorderedPair`: any statistic of the loads that
determines the report-visible merger rates (with at least three components) or the first two
survival derivatives (with two components) refines the load assignment, respectively the unordered
pair.

Not formalized here: the step from "a strong lumping of the labeled Kingman chain for every initial
labeled state that determines the report" to "determines the report-visible merger rates and the
survival derivatives", which is Rosenblatt's criterion applied to the chain of Theorem A and waits
for that chain's module; and the survival function as a semigroup, which is represented here by its
first two derivatives through the killed generator.

## Empirical status

None. The bodies here are algebra: loads are supplied natural numbers and every statement is an
identity or an implication between products and binomial coefficients of them, so no measurement
can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.MinimalRefinement

noncomputable section

/-! ### (B1): three or more components -/

/-- **Theorem B, (B1), cleared of the denominator.** With visible merger rates `ρ_CD = L_C L_D`,
the square of one load times the rate between two other components is the product of the two rates
through the first component: `L_C² ρ_DE = ρ_CD ρ_CE`. -/
theorem load_sq_mul_visibleRate {Component : Type*} (load : Component → ℕ) (C D E : Component) :
    load C ^ 2 * (load D * load E) = (load C * load D) * (load C * load E) := by
  ring

/-- **Theorem B, (B1).** For components with positive loads, the square of a load is the product
of the visible merger rates through it over the rate between the other two:
`L_C² = ρ_CD ρ_CE / ρ_DE`. -/
theorem load_sq_eq_visibleRates {Component : Type*} (load : Component → ℕ) (C D E : Component)
    (hD : 0 < load D) (hE : 0 < load E) :
    (load C : ℝ) ^ 2 =
      ((load C * load D : ℕ) : ℝ) * ((load C * load E : ℕ) : ℝ) / ((load D * load E : ℕ) : ℝ) := by
  have hne : ((load D * load E : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hD hE).ne'
  rw [eq_div_iff hne]
  push_cast
  ring

/-- A report with at least three components offers, beside any component, two other distinct
components. -/
theorem exists_two_others {Component : Type*} [Fintype Component] [DecidableEq Component]
    (hcard : 3 ≤ Fintype.card Component) (C : Component) :
    ∃ D E : Component, C ≠ D ∧ C ≠ E ∧ D ≠ E := by
  have hothers : 1 < (Finset.univ.erase C).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ C), Finset.card_univ]
    omega
  obtain ⟨D, hD, E, hE, hDE⟩ := Finset.one_lt_card.mp hothers
  exact ⟨D, E, (Finset.ne_of_mem_erase hD).symm, (Finset.ne_of_mem_erase hE).symm, hDE⟩

/-- **Theorem B, necessity with three or more components.** Two positive load assignments whose
visible merger rates agree for every pair of distinct components are equal. -/
theorem load_eq_of_visibleRates_eq {Component : Type*} [Fintype Component] [DecidableEq Component]
    (load other : Component → ℕ) (hload : ∀ C, 0 < load C) (hother : ∀ C, 0 < other C)
    (hrates : ∀ C D, C ≠ D → load C * load D = other C * other D)
    (hcard : 3 ≤ Fintype.card Component) : load = other := by
  funext C
  obtain ⟨D, E, hCD, hCE, hDE⟩ := exists_two_others hcard C
  have hsquare : load C ^ 2 * (load D * load E) = other C ^ 2 * (load D * load E) := by
    rw [load_sq_mul_visibleRate load C D E, hrates C D hCD, hrates C E hCE, hrates D E hDE,
      ← load_sq_mul_visibleRate other C D E]
  have hsq : load C ^ 2 = other C ^ 2 :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (hload D) (hload E)) hsquare
  exact Nat.pow_left_injective (by norm_num) hsq

/-- **Theorem B with three or more components.** The visible merger rates between distinct
components and the positive load assignment determine each other. -/
theorem visibleRates_eq_iff {Component : Type*} [Fintype Component] [DecidableEq Component]
    (hcard : 3 ≤ Fintype.card Component) (load other : Component → ℕ) (hload : ∀ C, 0 < load C)
    (hother : ∀ C, 0 < other C) :
    (∀ C D, C ≠ D → load C * load D = other C * other D) ↔ load = other :=
  ⟨fun hrates ↦ load_eq_of_visibleRates_eq load other hload hother hrates hcard,
    fun hequal C D _ ↦ by rw [hequal]⟩

/-- **Theorem B, minimality with three or more components.** A statistic of the load assignments
that determines every visible merger rate between distinct components refines the load assignment
itself. Assumes: the statistic determines the visible rates, which is what a Markov refinement of
the report must do, since these are the report's own jump rates. -/
theorem refines_loads {Component : Type*} [Fintype Component] [DecidableEq Component]
    {Statistic : Type*} (statistic : (Component → ℕ) → Statistic)
    (hcard : 3 ≤ Fintype.card Component)
    (hdetermines : ∀ load other : Component → ℕ, statistic load = statistic other →
      ∀ C D, C ≠ D → load C * load D = other C * other D)
    (load other : Component → ℕ) (hload : ∀ C, 0 < load C) (hother : ∀ C, 0 < other C)
    (hsame : statistic load = statistic other) : load = other :=
  load_eq_of_visibleRates_eq load other hload hother (hdetermines load other hsame) hcard

/-! ### (B2): two components -/

/-- **The two-component load chain killed at the visible merger.** With loads `a` and `b` the
hidden lineages merge inside the first component at rate `C(a,2)`, inside the second at rate
`C(b,2)`, and across the two at rate `ab`; the last merger connects the report and kills the chain.
This is the generator acting on a function of the two loads. -/
def twoComponentGenerator (f : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  (Nat.choose a 2 : ℝ) * (f (a - 1) b - f a b) + (Nat.choose b 2 : ℝ) * (f a (b - 1) - f a b) -
    (a : ℝ) * b * f a b

/-- **Theorem B, (B2), first derivative.** Applied to the constant one, the killed generator
returns minus the visible merger rate: `S'(0) = -ab`. -/
theorem twoComponentGenerator_one (a b : ℕ) :
    twoComponentGenerator (fun _ _ ↦ 1) a b = -((a : ℝ) * b) := by
  simp [twoComponentGenerator]

/-- **Theorem B, (B2), second derivative.** Applied twice to the constant one, the killed generator
returns `S''(0) = (ab)² + C(a,2) b + C(b,2) a = (ab)² + ab(a + b - 2)/2`. -/
theorem twoComponentGenerator_twice_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
        ((a : ℝ) * b) ^ 2 + (Nat.choose a 2 : ℝ) * b + (Nat.choose b 2 : ℝ) * a ∧
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
        ((a : ℝ) * b) ^ 2 + (a : ℝ) * b * ((a : ℝ) + b - 2) / 2 := by
  have hbinomial : twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
      ((a : ℝ) * b) ^ 2 + (Nat.choose a 2 : ℝ) * b + (Nat.choose b 2 : ℝ) * a := by
    rw [twoComponentGenerator, twoComponentGenerator_one, twoComponentGenerator_one,
      twoComponentGenerator_one, Nat.cast_sub ha, Nat.cast_sub hb]
    push_cast
    ring
  refine ⟨hbinomial, ?_⟩
  rw [hbinomial, Nat.cast_choose_two, Nat.cast_choose_two]
  ring

/-- **Theorem B, necessity with two components.** Positive loads `a, b` and `a', b'` with the same
first two survival derivatives form the same unordered pair. -/
theorem unorderedPair_of_survivalDerivatives_eq (a b a' b' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (hfirst : twoComponentGenerator (fun _ _ ↦ 1) a b =
      twoComponentGenerator (fun _ _ ↦ 1) a' b')
    (hsecond : twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a' b') :
    (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) := by
  rw [twoComponentGenerator_one, twoComponentGenerator_one] at hfirst
  rw [(twoComponentGenerator_twice_one a b ha hb).2,
    (twoComponentGenerator_twice_one a' b' ha' hb').2] at hsecond
  have hproduct : (a : ℝ) * b = a' * b' := by linarith
  have ha'Real : (1 : ℝ) ≤ a' := by exact_mod_cast ha'
  have hb'Real : (1 : ℝ) ≤ b' := by exact_mod_cast hb'
  have hproductPos : (0 : ℝ) < a' * b' := by nlinarith
  have hscaled : (a' : ℝ) * b' * (((a : ℝ) + b) - (a' + b')) = 0 := by
    rw [hproduct] at hsecond
    linarith
  have hsum : (a : ℝ) + b = a' + b' := by
    rcases mul_eq_zero.mp hscaled with hzero | hzero
    · exact absurd hzero hproductPos.ne'
    · linarith
  have hquadratic : ((a' : ℝ) - a) * (a' - b) = 0 := by
    linear_combination (-(a' : ℝ)) * hsum + hproduct
  rcases mul_eq_zero.mp hquadratic with hzero | hzero
  · left
    have hfirstLoad : (a' : ℝ) = a := by linarith
    have hsecondLoad : (b' : ℝ) = b := by linarith
    exact ⟨by exact_mod_cast hfirstLoad, by exact_mod_cast hsecondLoad⟩
  · right
    have hfirstLoad : (a' : ℝ) = b := by linarith
    have hsecondLoad : (b' : ℝ) = a := by linarith
    exact ⟨by exact_mod_cast hfirstLoad, by exact_mod_cast hsecondLoad⟩

/-- **Theorem B, sufficiency with two components.** The killed two-component generator commutes
with exchanging the two components, so functions of the unordered pair of loads go to functions of
the unordered pair: the unordered pair is a strong lumping of the two-component chain. -/
theorem twoComponentGenerator_swap (f : ℕ → ℕ → ℝ) (a b : ℕ) :
    twoComponentGenerator f b a = twoComponentGenerator (fun x y ↦ f y x) a b := by
  simp only [twoComponentGenerator]
  ring

/-- **(B2) does not see the order.** The first two survival derivatives of `(b, a)` are those of
`(a, b)`. -/
theorem survivalDerivatives_swap (a b : ℕ) :
    twoComponentGenerator (fun _ _ ↦ 1) b a = twoComponentGenerator (fun _ _ ↦ 1) a b ∧
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) b a =
        twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b := by
  have hsymmetric :
      (fun x y ↦ twoComponentGenerator (fun _ _ ↦ 1) y x) = twoComponentGenerator fun _ _ ↦ 1 := by
    ext x y
    simp only [twoComponentGenerator_one]
    ring
  refine ⟨?_, ?_⟩
  · rw [twoComponentGenerator_one, twoComponentGenerator_one, mul_comm]
  · rw [twoComponentGenerator_swap, hsymmetric]

/-- **Theorem B with two components.** For positive loads, the first two survival derivatives and
the unordered pair of loads determine each other. -/
theorem survivalDerivatives_eq_iff (a b a' b' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') :
    (twoComponentGenerator (fun _ _ ↦ 1) a b = twoComponentGenerator (fun _ _ ↦ 1) a' b' ∧
        twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
          twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a' b') ↔
      ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    exact unorderedPair_of_survivalDerivatives_eq a b a' b' ha hb ha' hb' hfirst hsecond
  · rintro (⟨hfirstLoad, hsecondLoad⟩ | ⟨hfirstLoad, hsecondLoad⟩)
    · rw [hfirstLoad, hsecondLoad]
      exact ⟨rfl, rfl⟩
    · rw [hfirstLoad, hsecondLoad]
      exact ⟨(survivalDerivatives_swap a b).1.symm, (survivalDerivatives_swap a b).2.symm⟩

/-- **Theorem B, minimality with two components.** A statistic of the two loads that determines
the first two survival derivatives refines the unordered pair of loads. Assumes: the statistic
determines the survival derivatives, which is what a Markov refinement of the two-component report
must do, since the survival is the law of the report's only remaining jump. -/
theorem refines_unorderedPair {Statistic : Type*} (statistic : ℕ → ℕ → Statistic)
    (hdetermines : ∀ a b a' b' : ℕ, statistic a b = statistic a' b' →
      twoComponentGenerator (fun _ _ ↦ 1) a b = twoComponentGenerator (fun _ _ ↦ 1) a' b' ∧
        twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
          twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a' b')
    (a b a' b' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (hsame : statistic a b = statistic a' b') : (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) :=
  (survivalDerivatives_eq_iff a b a' b' ha hb ha' hb').mp (hdetermines a b a' b' hsame)

/-- **(A3) with two components.** The killing rate of the two-component chain and its two
invisible merger rates add up to the Kingman death rate of all hidden lineages. -/
theorem killingRate_add_invisibleRates (a b : ℕ) :
    -twoComponentGenerator (fun _ _ ↦ 1) a b + Nat.choose a 2 + Nat.choose b 2 =
      Coalescent.deathRate (a + b) := by
  rw [twoComponentGenerator_one, Coalescent.deathRate, Descent.Core.pairCount,
    Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

end

end Descent.Pangenome.GraphCoalescent.MinimalRefinement

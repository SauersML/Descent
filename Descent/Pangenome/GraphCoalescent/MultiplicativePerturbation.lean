/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The mass perturbation of the multiplicative coalescent

Theorem F of the hidden-clock note compares the report of a compressed pangenome with the
finite-mass multiplicative coalescent `Z_p`.  (F1), proved in
`Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling`, uses the empirical fiber masses
`p^(n) = c/n`.  (F2) allows any mass vector `p` on the fibers, at the price `U ‖p^(n) - p‖₁`:

  `d_TV(L((Y_{u/n²})_{u ≤ U}), L((Z_p(u))_{u ≤ U})) ≤ min {1, U²/(4n) + U ‖p^(n) - p‖₁}`.  (F2)

## The coupling

`massStep mass` is `Z` uniformized at rate one in scaled time, for any nonnegative mass vector
on the individuals with total at most one; `multiplicativeStep n` is the case of unit masses
(`multiplicativeStep_eq_massStep`).  Two copies with masses `mass` and `mass'` are coupled by
`perturbedStep`.  While they agree, each pair of components merges in both copies at the smaller
of its two merge probabilities, and in one copy alone at the excess of its probability over the
smaller one, which raises the separation flag.  The separation chance per step is
`∑_{C<D} |p(C) p(D) - p'(C) p'(D)|`, and `perturbedStep_hazard` bounds it by `‖mass - mass'‖₁`.
Both products lie between the products of the componentwise minimum and maximum
(`pairExcessMass_add_le`); the pair sum of the maximum exceeds that of the minimum by at most the
`ℓ¹` distance of the component masses (`pairProductSum_max_sub_min_le`); and merging classes does
not increase that distance (`sum_abs_blockMass_sub_le`).  With a constant hazard the separation
mass grows linearly (`separationMass_le_mul`), and at the rings of a Poisson clock of mean `U`
the bound becomes `U ‖mass - mass'‖₁` through the Poisson mean (`hasSum_poissonPMFReal_mul_nat`).

## Main results

- `massPathTotalVariation_le`: after `m` steps the skeleton paths of `Z` from the interface with
  masses `mass` and `mass'` have total variation at most `m ‖mass - mass'‖₁`.
- `report_mass_pathTotalVariation_le`, `report_mass_pathTotalVariation_le_one`,
  `report_mass_poissonTotalVariation_le`: (F2) for the uniformized skeletons, by the triangle
  inequality with (F1).
- `spreadMass`: a mass vector `p` on the fibers, spread evenly over each fiber's individuals.  Its
  components at the interface carry `p` (`blockMass_spreadMass_graphKer`), and its `ℓ¹` distance
  to unit masses is the note's `‖p^(n) - p‖₁ = ∑_F |c_F/n - p_F|`
  (`sum_abs_unitMass_sub_spreadMass`).  `report_spread_poissonTotalVariation_le` is (F2) in the
  note's form.

## Scope

As in `MultiplicativeObservation`, the continuous-time processes enter through their
uniformization: the total variation is between the laws of the skeleton paths, mixed over the
rings of a Poisson clock.  `Z_p` runs on the partitions of the individuals from the interface,
with `p` read on the fibers through `spreadMass`, as `MultiplicativeCoupling` runs `Z_{p^(n)}`.

## Empirical status

None.  Every declaration here is a finite stochastic matrix, a finite sum or the Poisson mass
function.  The masses `p` are parameters, not estimates from any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset ProbabilityTheory

open scoped Classical

noncomputable section

/-! ### `Z` for any mass vector, uniformized in scaled time -/

/-- **`Z` with individual masses `mass`, uniformized at rate one in scaled time**: two components
merge with probability the product of their masses, and the chain holds with the rest.

Empirical status: NOT AN EMPIRICAL CLAIM.  The finite-mass multiplicative coalescent's rates. -/
def massStep {n : ℕ} (mass : Fin n → ℝ) (ζ ζ' : ER n) : ℝ :=
  (∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair ζ t = ζ'),
      ∏ C ∈ t, blockMass mass ζ C)
    + if ζ' = ζ then 1 - pairProductSum (blockMass mass ζ) else 0

/-- Unit masses give the uniformized `Z_p` of `MultiplicativeCoupling`. -/
theorem multiplicativeStep_eq_massStep (n : ℕ) : multiplicativeStep n = massStep (unitMass n) :=
  rfl

/-- The uniformized kernel of `Z` is stochastic for every mass vector. -/
theorem sum_massStep {n : ℕ} (mass : Fin n → ℝ) (ζ : ER n) : ∑ ζ', massStep mass ζ ζ' = 1 := by
  simp only [massStep, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_fiberwise ((univ : Finset (Quotient ζ)).powersetCard 2)
    (mergePair ζ) fun t ↦ ∏ C ∈ t, blockMass mass ζ C]
  unfold pairProductSum
  ring

/-- The components of a nonnegative mass vector carry nonnegative masses. -/
theorem blockMass_nonneg {n : ℕ} {mass : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i) (ζ : ER n)
    (C : Quotient ζ) : 0 ≤ blockMass mass ζ C :=
  Finset.sum_nonneg fun i _ ↦ hmass i

/-- The uniformized kernel of `Z` is nonnegative once the masses are nonnegative with total at
most one. -/
theorem massStep_nonneg {n : ℕ} {mass : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (htotal : ∑ i, mass i ≤ 1) (ζ ζ' : ER n) : 0 ≤ massStep mass ζ ζ' := by
  have hhalf := pairProductSum_le_half_sq (blockMass mass ζ)
  rw [sum_blockMass] at hhalf
  have hnn : 0 ≤ ∑ i, mass i := Finset.sum_nonneg fun i _ ↦ hmass i
  unfold massStep
  refine add_nonneg
    (Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun C _ ↦ blockMass_nonneg hmass ζ C) ?_
  split_ifs
  · nlinarith
  · exact le_rfl

/-! ### The excess of two mass vectors -/

/-- **Merging classes does not increase the `ℓ¹` distance of two mass vectors.** -/
theorem sum_abs_blockMass_sub_le {w : ℕ} (p q : Fin w → ℝ) (ζ : ER w) :
    ∑ C, |blockMass p ζ C - blockMass q ζ C| ≤ ∑ i, |p i - q i| := by
  have hpoint : ∀ C, |blockMass p ζ C - blockMass q ζ C|
      ≤ ∑ i ∈ univ.filter (fun i ↦ Quotient.mk ζ i = C), |p i - q i| := by
    intro C
    rw [blockMass, blockMass, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  calc ∑ C, |blockMass p ζ C - blockMass q ζ C|
      ≤ ∑ C, ∑ i ∈ univ.filter (fun i ↦ Quotient.mk ζ i = C), |p i - q i| :=
        Finset.sum_le_sum fun C _ ↦ hpoint C
    _ = ∑ i, |p i - q i| := Finset.sum_fiberwise univ (Quotient.mk ζ) fun i ↦ |p i - q i|

/-- **The pair sum of the componentwise maximum exceeds that of the minimum by at most the `ℓ¹`
distance**, times the mean of the two totals. -/
theorem pairProductSum_max_sub_min_le {ι : Type*} [Fintype ι] {f g : ι → ℝ} (hf : ∀ a, 0 ≤ f a)
    (hg : ∀ a, 0 ≤ g a) :
    pairProductSum (fun a ↦ max (f a) (g a)) - pairProductSum (fun a ↦ min (f a) (g a))
      ≤ (∑ a, |f a - g a|) * ((∑ a, f a + ∑ a, g a) / 2) := by
  have hmax := two_mul_pairProductSum (fun a ↦ max (f a) (g a))
  have hmin := two_mul_pairProductSum (fun a ↦ min (f a) (g a))
  have hdiff : ∑ a, max (f a) (g a) - ∑ a, min (f a) (g a) = ∑ a, |f a - g a| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ max_sub_min_eq_abs' (f a) (g a)
  have hadd : ∑ a, min (f a) (g a) + ∑ a, max (f a) (g a) = ∑ a, f a + ∑ a, g a := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ min_add_max (f a) (g a)
  have hsq : ∑ a, min (f a) (g a) ^ 2 ≤ ∑ a, max (f a) (g a) ^ 2 :=
    Finset.sum_le_sum fun a _ ↦ by
      have h0 : 0 ≤ min (f a) (g a) := le_min (hf a) (hg a)
      have h1 : min (f a) (g a) ≤ max (f a) (g a) := min_le_max
      nlinarith
  have hprod : (∑ a, max (f a) (g a)) ^ 2 - (∑ a, min (f a) (g a)) ^ 2
      = (∑ a, |f a - g a|) * (∑ a, f a + ∑ a, g a) := by
    rw [← hdiff, ← hadd]
    ring
  linarith

/-- **The smaller of the two merge probabilities of a set of components.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A minimum of two finite products. -/
def pairMinMass {n : ℕ} (mass mass' : Fin n → ℝ) (ζ : ER n) (t : Finset (Quotient ζ)) : ℝ :=
  min (∏ C ∈ t, blockMass mass ζ C) (∏ C ∈ t, blockMass mass' ζ C)

/-- **The excess of the first merge probability of a set of components over the smaller one.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A difference of a finite product and a minimum. -/
def pairExcessMass {n : ℕ} (mass mass' : Fin n → ℝ) (ζ : ER n) (t : Finset (Quotient ζ)) : ℝ :=
  ∏ C ∈ t, blockMass mass ζ C - pairMinMass mass mass' ζ t

theorem pairMinMass_comm {n : ℕ} (mass mass' : Fin n → ℝ) (ζ : ER n) (t : Finset (Quotient ζ)) :
    pairMinMass mass' mass ζ t = pairMinMass mass mass' ζ t :=
  min_comm _ _

theorem pairMinMass_nonneg {n : ℕ} {mass mass' : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hmass' : ∀ i, 0 ≤ mass' i) (ζ : ER n) (t : Finset (Quotient ζ)) :
    0 ≤ pairMinMass mass mass' ζ t :=
  le_min (Finset.prod_nonneg fun C _ ↦ blockMass_nonneg hmass ζ C)
    (Finset.prod_nonneg fun C _ ↦ blockMass_nonneg hmass' ζ C)

theorem pairExcessMass_nonneg {n : ℕ} (mass mass' : Fin n → ℝ) (ζ : ER n)
    (t : Finset (Quotient ζ)) : 0 ≤ pairExcessMass mass mass' ζ t :=
  sub_nonneg.mpr (min_le_left _ _)

/-- **The two excesses of a set of components add up to at most the gap between the products of
the componentwise maximum and minimum.** -/
theorem pairExcessMass_add_le {n : ℕ} {mass mass' : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hmass' : ∀ i, 0 ≤ mass' i) (ζ : ER n) (t : Finset (Quotient ζ)) :
    pairExcessMass mass mass' ζ t + pairExcessMass mass' mass ζ t
      ≤ ∏ C ∈ t, max (blockMass mass ζ C) (blockMass mass' ζ C)
        - ∏ C ∈ t, min (blockMass mass ζ C) (blockMass mass' ζ C) := by
  have hmin : ∀ C, 0 ≤ min (blockMass mass ζ C) (blockMass mass' ζ C) :=
    fun C ↦ le_min (blockMass_nonneg hmass ζ C) (blockMass_nonneg hmass' ζ C)
  have hf1 : ∏ C ∈ t, min (blockMass mass ζ C) (blockMass mass' ζ C)
      ≤ ∏ C ∈ t, blockMass mass ζ C :=
    Finset.prod_le_prod (fun C _ ↦ hmin C) fun _ _ ↦ min_le_left _ _
  have hg1 : ∏ C ∈ t, min (blockMass mass ζ C) (blockMass mass' ζ C)
      ≤ ∏ C ∈ t, blockMass mass' ζ C :=
    Finset.prod_le_prod (fun C _ ↦ hmin C) fun _ _ ↦ min_le_right _ _
  have hf2 : ∏ C ∈ t, blockMass mass ζ C
      ≤ ∏ C ∈ t, max (blockMass mass ζ C) (blockMass mass' ζ C) :=
    Finset.prod_le_prod (fun C _ ↦ blockMass_nonneg hmass ζ C) fun _ _ ↦ le_max_left _ _
  have hg2 : ∏ C ∈ t, blockMass mass' ζ C
      ≤ ∏ C ∈ t, max (blockMass mass ζ C) (blockMass mass' ζ C) :=
    Finset.prod_le_prod (fun C _ ↦ blockMass_nonneg hmass' ζ C) fun _ _ ↦ le_max_right _ _
  unfold pairExcessMass pairMinMass
  rcases le_total (∏ C ∈ t, blockMass mass ζ C) (∏ C ∈ t, blockMass mass' ζ C) with h | h
  · rw [min_eq_left h, min_eq_right h]
    linarith
  · rw [min_eq_right h, min_eq_left h]
    linarith

/-! ### The coupled step of two mass vectors -/

/-- **The mass with which the agreeing coupled chain holds.**

Empirical status: NOT AN EMPIRICAL CLAIM.  One minus the probabilities of the moves. -/
def perturbedHold {n : ℕ} (mass mass' : Fin n → ℝ) (ζ : ER n) : ℝ :=
  1 - ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
    (pairMinMass mass mass' ζ t + pairExcessMass mass mass' ζ t + pairExcessMass mass' mass ζ t)

/-- **Separated**: the flag is raised, or the two copies disagree.

Empirical status: NOT AN EMPIRICAL CLAIM.  A predicate on coupled states. -/
def perturbedSep {n : ℕ} (X : CoupledState n) : Prop :=
  X.2.2 = true ∨ X.1 ≠ X.2.1

/-- **The coupled step of two mass vectors.**  Separated, the copies move independently and the
flag stays up.  Agreeing, each pair of components merges in both copies at the smaller of its two
merge probabilities, in the first copy alone at its excess and in the second copy alone at its
excess, both raising the flag, and otherwise nothing moves.

Empirical status: NOT AN EMPIRICAL CLAIM.  A stochastic matrix built from the two kernels. -/
def perturbedStep {n : ℕ} (mass mass' : Fin n → ℝ) (X Y : CoupledState n) : ℝ :=
  if perturbedSep X then
    massStep mass X.1 Y.1 * massStep mass' X.2.1 Y.2.1 * (if Y.2.2 = true then 1 else 0)
  else
    (∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
      (pairMinMass mass mass' X.1 t *
          (if Y = (mergePair X.1 t, mergePair X.1 t, false) then 1 else 0)
        + pairExcessMass mass mass' X.1 t * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
        + pairExcessMass mass' mass X.1 t * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0)))
      + perturbedHold mass mass' X.1 * (if Y = (X.1, X.1, false) then 1 else 0)

/-- While unseparated, the two copies agree. -/
theorem perturbedAgree {n : ℕ} {X : CoupledState n} (hX : ¬ perturbedSep X) : X.1 = X.2.1 := by
  unfold perturbedSep at hX
  push_neg at hX
  exact hX.2

/-- The agreeing holding mass is nonnegative. -/
theorem perturbedHold_nonneg {n : ℕ} {mass mass' : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hmass' : ∀ i, 0 ≤ mass' i) (htotal : ∑ i, mass i ≤ 1) (htotal' : ∑ i, mass' i ≤ 1)
    (ζ : ER n) : 0 ≤ perturbedHold mass mass' ζ := by
  have hle : ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
      (pairMinMass mass mass' ζ t + pairExcessMass mass mass' ζ t
        + pairExcessMass mass' mass ζ t)
      ≤ pairProductSum (blockMass mass ζ) + pairProductSum (blockMass mass' ζ) := by
    unfold pairProductSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    have hmin := pairMinMass_nonneg hmass hmass' ζ t
    have hcomm := pairMinMass_comm mass mass' ζ t
    unfold pairExcessMass
    linarith
  have hhalf := pairProductSum_le_half_sq (blockMass mass ζ)
  have hhalf' := pairProductSum_le_half_sq (blockMass mass' ζ)
  rw [sum_blockMass] at hhalf hhalf'
  have hnn : 0 ≤ ∑ i, mass i := Finset.sum_nonneg fun i _ ↦ hmass i
  have hnn' : 0 ≤ ∑ i, mass' i := Finset.sum_nonneg fun i _ ↦ hmass' i
  have hsq : (∑ i, mass i) ^ 2 ≤ 1 := by nlinarith
  have hsq' : (∑ i, mass' i) ^ 2 ≤ 1 := by nlinarith
  unfold perturbedHold
  linarith

theorem perturbedStep_nonneg {n : ℕ} {mass mass' : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hmass' : ∀ i, 0 ≤ mass' i) (htotal : ∑ i, mass i ≤ 1) (htotal' : ∑ i, mass' i ≤ 1)
    (X Y : CoupledState n) : 0 ≤ perturbedStep mass mass' X Y := by
  have hind : ∀ (c : Prop) [Decidable c], 0 ≤ (if c then (1 : ℝ) else 0) := fun _ _ ↦ by
    split_ifs <;> norm_num
  unfold perturbedStep
  by_cases hX : perturbedSep X
  · rw [if_pos hX]
    exact mul_nonneg (mul_nonneg (massStep_nonneg hmass htotal _ _)
      (massStep_nonneg hmass' htotal' _ _)) (hind _)
  · rw [if_neg hX]
    refine add_nonneg (Finset.sum_nonneg fun t _ ↦ ?_)
      (mul_nonneg (perturbedHold_nonneg hmass hmass' htotal htotal' _) (hind _))
    exact add_nonneg (add_nonneg (mul_nonneg (pairMinMass_nonneg hmass hmass' _ t) (hind _))
      (mul_nonneg (pairExcessMass_nonneg _ _ _ t) (hind _)))
      (mul_nonneg (pairExcessMass_nonneg _ _ _ t) (hind _))

/-- **The coupled step is stochastic.** -/
theorem sum_perturbedStep {n : ℕ} (mass mass' : Fin n → ℝ) (X : CoupledState n) :
    ∑ Y, perturbedStep mass mass' X Y = 1 := by
  by_cases hX : perturbedSep X
  · simp only [perturbedStep, if_pos hX]
    rw [sum_coupledState]
    simp only [if_true, Bool.false_eq_true, if_false, mul_one, mul_zero, add_zero]
    rw [← Finset.sum_mul_sum, sum_massStep, sum_massStep, one_mul]
  · simp only [perturbedStep, if_neg hX]
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    simp only [perturbedHold, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_one]
    ring

/-- **Separation is absorbing.** -/
theorem perturbedStep_absorb {n : ℕ} (mass mass' : Fin n → ℝ) (X Y : CoupledState n)
    (hX : perturbedSep X) (hY : ¬ perturbedSep Y) : perturbedStep mass mass' X Y = 0 := by
  have hflag : Y.2.2 ≠ true := fun h ↦ hY (Or.inl h)
  simp only [perturbedStep, if_pos hX, if_neg hflag, mul_zero]

/-- **The separation hazard of the coupled step is at most `‖mass - mass'‖₁`.** -/
theorem perturbedStep_hazard {n : ℕ} {mass mass' : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hmass' : ∀ i, 0 ≤ mass' i) (htotal : ∑ i, mass i ≤ 1) (htotal' : ∑ i, mass' i ≤ 1)
    (X : CoupledState n) (hX : ¬ perturbedSep X) :
    ∑ Y ∈ univ.filter perturbedSep, perturbedStep mass mass' X Y ≤ ∑ i, |mass i - mass' i| := by
  have hind : ∀ (c : Prop) [Decidable c], 0 ≤ (if c then (1 : ℝ) else 0) := fun _ _ ↦ by
    split_ifs <;> norm_num
  have hsum : ∑ i, mass i + ∑ i, mass' i ≤ 2 := by linarith
  have hpoint : ∀ Y ∈ univ.filter perturbedSep, perturbedStep mass mass' X Y
      = ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairExcessMass mass mass' X.1 t * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
            + pairExcessMass mass' mass X.1 t
              * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0)) := by
    intro Y hY
    have hYsep := (Finset.mem_filter.mp hY).2
    have hcommon : ∀ t : Finset (Quotient X.1),
        ¬ (Y = (mergePair X.1 t, mergePair X.1 t, false)) := by
      intro t heq
      rw [heq] at hYsep
      rcases hYsep with h | h
      · exact Bool.false_ne_true h
      · exact h rfl
    have hhold : ¬ (Y = (X.1, X.1, false)) := by
      intro heq
      rw [heq] at hYsep
      rcases hYsep with h | h
      · exact Bool.false_ne_true h
      · exact h rfl
    simp only [perturbedStep, if_neg hX, if_neg hhold, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [if_neg (hcommon t), mul_zero, zero_add]
  have hδ : 0 ≤ ∑ C, |blockMass mass X.1 C - blockMass mass' X.1 C| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  calc ∑ Y ∈ univ.filter perturbedSep, perturbedStep mass mass' X Y
      = ∑ Y ∈ univ.filter perturbedSep, ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairExcessMass mass mass' X.1 t * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
            + pairExcessMass mass' mass X.1 t
              * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0)) :=
        Finset.sum_congr rfl hpoint
    _ ≤ ∑ Y : CoupledState n, ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairExcessMass mass mass' X.1 t * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
            + pairExcessMass mass' mass X.1 t
              * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦
          Finset.sum_nonneg fun t _ ↦
            add_nonneg (mul_nonneg (pairExcessMass_nonneg _ _ _ t) (hind _))
              (mul_nonneg (pairExcessMass_nonneg _ _ _ t) (hind _))
    _ = ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairExcessMass mass mass' X.1 t + pairExcessMass mass' mass X.1 t) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, mul_one]
    _ ≤ ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (∏ C ∈ t, max (blockMass mass X.1 C) (blockMass mass' X.1 C)
            - ∏ C ∈ t, min (blockMass mass X.1 C) (blockMass mass' X.1 C)) :=
        Finset.sum_le_sum fun t _ ↦ pairExcessMass_add_le hmass hmass' X.1 t
    _ = pairProductSum (fun C ↦ max (blockMass mass X.1 C) (blockMass mass' X.1 C))
          - pairProductSum (fun C ↦ min (blockMass mass X.1 C) (blockMass mass' X.1 C)) := by
        unfold pairProductSum
        rw [Finset.sum_sub_distrib]
    _ ≤ (∑ C, |blockMass mass X.1 C - blockMass mass' X.1 C|)
          * ((∑ C, blockMass mass X.1 C + ∑ C, blockMass mass' X.1 C) / 2) :=
        pairProductSum_max_sub_min_le (blockMass_nonneg hmass X.1) (blockMass_nonneg hmass' X.1)
    _ ≤ ∑ C, |blockMass mass X.1 C - blockMass mass' X.1 C| := by
        rw [sum_blockMass, sum_blockMass]
        nlinarith
    _ ≤ ∑ i, |mass i - mass' i| := sum_abs_blockMass_sub_le mass mass' X.1

/-! ### Separation at a constant hazard -/

section ConstantHazard

variable {S : Type*} [Fintype S]

/-- **Separation at a constant hazard grows linearly.**  If from every unseparated state the
chance of separating in one step is at most `ε`, the chain has separated by step `k` with
probability at most `ε k`.

Assumes: the kernel is stochastic, the initial law is a probability vector with no separated
mass, and `0 ≤ ε`. -/
theorem separationMass_le_mul {P : S → S → ℝ} {μ₀ : S → ℝ} {sep : S → Prop} {ε : ℝ}
    (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1) (hμ : ∀ s, 0 ≤ μ₀ s)
    (hμ1 : ∑ s, μ₀ s = 1) (hε : 0 ≤ ε)
    (hhazard : ∀ s, ¬ sep s → ∑ t ∈ univ.filter sep, P s t ≤ ε)
    (hsep0 : separationMass P μ₀ sep 0 = 0) (k : ℕ) :
    separationMass P μ₀ sep k ≤ ε * k := by
  induction k with
  | zero => simp [hsep0]
  | succ k ih =>
    set G : S → ℝ := fun s ↦ ∑ t ∈ univ.filter sep, P s t with hG
    have hswap : separationMass P μ₀ sep (k + 1) = ∑ s, skeletonLaw P μ₀ k s * G s := by
      have h1 := sum_skeletonLaw_succ P μ₀ k (univ.filter sep) fun _ ↦ 1
      simp only [mul_one] at h1
      exact h1
    have hsplit := Finset.sum_filter_add_sum_filter_not univ sep
      fun s ↦ skeletonLaw P μ₀ k s * G s
    have hA : ∑ s ∈ univ.filter sep, skeletonLaw P μ₀ k s * G s
        ≤ separationMass P μ₀ sep k := by
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have hle1 : G s ≤ 1 := by
        rw [hG, ← hrow s]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun t _ _ ↦ hP s t
      calc skeletonLaw P μ₀ k s * G s ≤ skeletonLaw P μ₀ k s * 1 :=
            mul_le_mul_of_nonneg_left hle1 (skeletonLaw_nonneg hP hμ k s)
        _ = skeletonLaw P μ₀ k s := mul_one _
    have hB : ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s * G s
        ≤ ε * ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s hs ↦ ?_
      calc skeletonLaw P μ₀ k s * G s ≤ skeletonLaw P μ₀ k s * ε :=
            mul_le_mul_of_nonneg_left (hhazard s (Finset.mem_filter.mp hs).2)
              (skeletonLaw_nonneg hP hμ k s)
        _ = ε * skeletonLaw P μ₀ k s := by ring
    have hmass := sum_filter_not_skeletonLaw_le hP hrow hμ hμ1
      (univ.filter fun s ↦ ¬ sep s) k
    have hεmass := mul_le_mul_of_nonneg_left hmass hε
    push_cast
    linarith

/-- The skeleton path weights of a stochastic kernel carry the initial mass. -/
theorem sum_skeletonPathWeight {P : S → S → ℝ} {μ₀ : S → ℝ} (hrow : ∀ s, ∑ t, P s t = 1)
    (m : ℕ) : ∑ ω : Fin (m + 1) → S, skeletonPathWeight P μ₀ m ω = ∑ s, μ₀ s := by
  have h := sum_skeletonPathWeight_mul P μ₀ m fun _ ↦ 1
  simp only [mul_one] at h
  rw [h, sum_skeletonLaw hrow]

end ConstantHazard

/-! ### The Poisson mean -/

/-- The Poisson mass function against the index, one term. -/
theorem poissonPMFReal_succ_mul (U : NNReal) (j : ℕ) :
    poissonPMFReal U (j + 1) * ((j + 1 : ℕ) : ℝ) = (U : ℝ) * poissonPMFReal U j := by
  unfold poissonPMFReal
  rw [Nat.factorial_succ]
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The mean of a Poisson law is `U`.** -/
theorem hasSum_poissonPMFReal_mul_nat (U : NNReal) :
    HasSum (fun m : ℕ ↦ poissonPMFReal U m * (m : ℝ)) (U : ℝ) := by
  have hshift : HasSum (fun j : ℕ ↦ poissonPMFReal U (j + 1) * ((j + 1 : ℕ) : ℝ)) (U : ℝ) := by
    have h := (poissonPMFRealSum U).mul_left (U : ℝ)
    simp only [mul_one] at h
    have hfun : (fun j : ℕ ↦ poissonPMFReal U (j + 1) * ((j + 1 : ℕ) : ℝ))
        = fun j ↦ (U : ℝ) * poissonPMFReal U j :=
      funext (poissonPMFReal_succ_mul U)
    rw [hfun]
    exact h
  have h1 := (hasSum_nat_add_iff (f := fun m : ℕ ↦ poissonPMFReal U m * (m : ℝ)) 1).mp hshift
  simpa [Finset.sum_range_succ] using h1

/-! ### The two marginals and the path laws -/

/-- **The first copy of the coupled chain is `Z` with masses `mass`.** -/
theorem sum_perturbedStep_fst {n : ℕ} (mass mass' : Fin n → ℝ) (X : CoupledState n)
    (ζ₁ : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.1 = ζ₁), perturbedStep mass mass' X Y
      = massStep mass X.1 ζ₁ := by
  by_cases hX : perturbedSep X
  · rw [sum_filter_fst_coupledState]
    simp only [perturbedStep, if_pos hX, if_true, Bool.false_eq_true, if_false, mul_one,
      mul_zero, add_zero]
    rw [← Finset.mul_sum, sum_massStep, mul_one]
  · simp only [perturbedStep, if_neg hX]
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    have hinner : ∀ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
        ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.1 = ζ₁),
          (pairMinMass mass mass' X.1 t *
              (if Y = (mergePair X.1 t, mergePair X.1 t, false) then 1 else 0)
            + pairExcessMass mass mass' X.1 t
              * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
            + pairExcessMass mass' mass X.1 t
              * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0))
        = (if mergePair X.1 t = ζ₁ then ∏ C ∈ t, blockMass mass X.1 C else 0)
          + (if X.1 = ζ₁ then 1 else 0) * pairExcessMass mass' mass X.1 t := by
      intro _ _
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_filter,
        Finset.mem_univ, true_and]
      unfold pairExcessMass
      split_ifs <;> ring
    have hhold : ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.1 = ζ₁),
        (if Y = (X.1, X.1, false) then (1 : ℝ) else 0) = if X.1 = ζ₁ then 1 else 0 := by
      simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_congr rfl hinner, hhold, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_filter, massStep]
    by_cases hζ : X.1 = ζ₁
    · have hsum : ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairMinMass mass mass' X.1 t + pairExcessMass mass mass' X.1 t
            + pairExcessMass mass' mass X.1 t)
          = pairProductSum (blockMass mass X.1)
            + ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
              pairExcessMass mass' mass X.1 t := by
        unfold pairProductSum
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by
          unfold pairExcessMass
          ring
      rw [if_pos hζ, if_pos hζ.symm]
      unfold perturbedHold
      linarith
    · rw [if_neg hζ, if_neg fun h ↦ hζ h.symm]
      ring

/-- **The second copy of the coupled chain is `Z` with masses `mass'`.** -/
theorem sum_perturbedStep_snd {n : ℕ} (mass mass' : Fin n → ℝ) (X : CoupledState n)
    (ζ₂ : ER n) :
    ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.2.1 = ζ₂), perturbedStep mass mass' X Y
      = massStep mass' X.2.1 ζ₂ := by
  by_cases hX : perturbedSep X
  · rw [sum_filter_snd_coupledState]
    simp only [perturbedStep, if_pos hX, if_true, Bool.false_eq_true, if_false, mul_one,
      mul_zero, add_zero]
    rw [← Finset.sum_mul, sum_massStep, one_mul]
  · rw [← perturbedAgree hX]
    simp only [perturbedStep, if_neg hX]
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
    have hinner : ∀ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
        ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.2.1 = ζ₂),
          (pairMinMass mass mass' X.1 t *
              (if Y = (mergePair X.1 t, mergePair X.1 t, false) then 1 else 0)
            + pairExcessMass mass mass' X.1 t
              * (if Y = (mergePair X.1 t, X.1, true) then 1 else 0)
            + pairExcessMass mass' mass X.1 t
              * (if Y = (X.1, mergePair X.1 t, true) then 1 else 0))
        = (if mergePair X.1 t = ζ₂ then ∏ C ∈ t, blockMass mass' X.1 C else 0)
          + (if X.1 = ζ₂ then 1 else 0) * pairExcessMass mass mass' X.1 t := by
      intro t _
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hcomm := pairMinMass_comm mass mass' X.1 t
      unfold pairExcessMass
      split_ifs <;> linarith
    have hhold : ∑ Y ∈ univ.filter (fun Y : CoupledState n ↦ Y.2.1 = ζ₂),
        (if Y = (X.1, X.1, false) then (1 : ℝ) else 0) = if X.1 = ζ₂ then 1 else 0 := by
      simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_congr rfl hinner, hhold, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_filter, massStep]
    by_cases hζ : X.1 = ζ₂
    · have hsum : ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
          (pairMinMass mass mass' X.1 t + pairExcessMass mass mass' X.1 t
            + pairExcessMass mass' mass X.1 t)
          = pairProductSum (blockMass mass' X.1)
            + ∑ t ∈ (univ : Finset (Quotient X.1)).powersetCard 2,
              pairExcessMass mass mass' X.1 t := by
        unfold pairProductSum
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ ↦ by
          have hcomm := pairMinMass_comm mass mass' X.1 t
          unfold pairExcessMass
          linarith
      rw [if_pos hζ, if_pos hζ.symm]
      unfold perturbedHold
      linarith
    · rw [if_neg hζ, if_neg fun h ↦ hζ h.symm]
      ring

/-- **The coupled start**: both copies at the interface, the flag down.

Empirical status: NOT AN EMPIRICAL CLAIM.  A point mass. -/
def perturbedStartLaw {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) : ℝ :=
  if X = (graphKer s, graphKer s, false) then 1 else 0

theorem perturbedStartLaw_nonneg {n : ℕ} (s : Fin n → Fin n) (X : CoupledState n) :
    0 ≤ perturbedStartLaw s X := by
  unfold perturbedStartLaw
  split_ifs <;> norm_num

theorem sum_perturbedStartLaw {n : ℕ} (s : Fin n → Fin n) : ∑ X, perturbedStartLaw s X = 1 := by
  simp [perturbedStartLaw]

theorem separationMass_perturbedStart {n : ℕ} (s : Fin n → Fin n) (mass mass' : Fin n → ℝ) :
    separationMass (perturbedStep mass mass') (perturbedStartLaw s) perturbedSep 0 = 0 := by
  have hns : ¬ perturbedSep ((graphKer s, graphKer s, false) : CoupledState n) := by
    simp [perturbedSep]
  refine Finset.sum_eq_zero fun X hX ↦ ?_
  show perturbedStartLaw s X = 0
  refine if_neg fun h ↦ ?_
  rw [h] at hX
  exact hns (Finset.mem_filter.mp hX).2

theorem sum_filter_fst_perturbedStartLaw {n : ℕ} (s : Fin n → Fin n) (ζ : ER n) :
    ∑ X ∈ univ.filter (fun X : CoupledState n ↦ X.1 = ζ), perturbedStartLaw s X
      = if ζ = graphKer s then 1 else 0 := by
  rw [sum_filter_fst_coupledState]
  by_cases h : ζ = graphKer s <;> simp [perturbedStartLaw, h]

theorem sum_filter_snd_perturbedStartLaw {n : ℕ} (s : Fin n → Fin n) (ζ : ER n) :
    ∑ X ∈ univ.filter (fun X : CoupledState n ↦ X.2.1 = ζ), perturbedStartLaw s X
      = if ζ = graphKer s then 1 else 0 := by
  rw [sum_filter_snd_coupledState]
  by_cases h : ζ = graphKer s <;> simp [perturbedStartLaw, h]

/-- **The law of `Z`'s skeleton path with masses `mass`**, started at the interface.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite path law. -/
def massPathLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ)
    (y : Fin (m + 1) → ER n) : ℝ :=
  skeletonPathWeight (massStep mass) (fun ζ ↦ if ζ = graphKer s then 1 else 0) m y

/-- Unit masses give the path law of `MultiplicativeCoupling`. -/
theorem multiplicativePathLaw_eq_massPathLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ)
    (y : Fin (m + 1) → ER n) : multiplicativePathLaw s m y = massPathLaw s (unitMass n) m y :=
  rfl

/-- The coupled path law, read through the first copy, is `Z`'s path law with masses `mass`. -/
theorem sum_filter_perturbed_fst_eq {n : ℕ} (s : Fin n → Fin n) (mass mass' : Fin n → ℝ)
    (m : ℕ) (y : Fin (m + 1) → ER n) :
    ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → CoupledState n ↦ (fun k ↦ (ω k).1) = y),
      skeletonPathWeight (perturbedStep mass mass') (perturbedStartLaw s) m ω
      = massPathLaw s mass m y :=
  sum_filter_path_comp_eq (perturbedStep mass mass') (perturbedStartLaw s) (massStep mass)
    (fun ζ ↦ if ζ = graphKer s then 1 else 0) Prod.fst
    (fun X ζ₁ ↦ sum_perturbedStep_fst mass mass' X ζ₁) (sum_filter_fst_perturbedStartLaw s) m y

/-- The coupled path law, read through the second copy, is `Z`'s path law with masses
`mass'`. -/
theorem sum_filter_perturbed_snd_eq {n : ℕ} (s : Fin n → Fin n) (mass mass' : Fin n → ℝ)
    (m : ℕ) (y : Fin (m + 1) → ER n) :
    ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → CoupledState n ↦ (fun k ↦ (ω k).2.1) = y),
      skeletonPathWeight (perturbedStep mass mass') (perturbedStartLaw s) m ω
      = massPathLaw s mass' m y :=
  sum_filter_path_comp_eq (perturbedStep mass mass') (perturbedStartLaw s) (massStep mass')
    (fun ζ ↦ if ζ = graphKer s then 1 else 0) (fun X ↦ X.2.1)
    (fun X ζ₂ ↦ sum_perturbedStep_snd mass mass' X ζ₂) (sum_filter_snd_perturbedStartLaw s) m y

/-! ### (F2) -/

/-- **The mass perturbation at path level.**  After `m` steps the skeleton paths of `Z` from the
interface with masses `mass` and with masses `mass'` have total variation at most
`m ‖mass - mass'‖₁`.

Assumes: both mass vectors are nonnegative with total at most one. -/
theorem massPathTotalVariation_le {n : ℕ} (s : Fin n → Fin n) {mass mass' : Fin n → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hmass' : ∀ i, 0 ≤ mass' i) (htotal : ∑ i, mass i ≤ 1)
    (htotal' : ∑ i, mass' i ≤ 1) (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER n, |massPathLaw s mass m y - massPathLaw s mass' m y|
      ≤ (∑ i, |mass i - mass' i|) * m := by
  have htv := pathTotalVariation_le_separationMass
    (perturbedStep_nonneg hmass hmass' htotal htotal') (perturbedStartLaw_nonneg s)
    (fun X Y hX hY ↦ perturbedStep_absorb mass mass' X Y hX hY) (fun X ↦ X.1) (fun X ↦ X.2.1)
    (fun _ hX ↦ perturbedAgree hX) m
  simp only [sum_filter_perturbed_fst_eq, sum_filter_perturbed_snd_eq] at htv
  have hsep := separationMass_le_mul (perturbedStep_nonneg hmass hmass' htotal htotal')
    (sum_perturbedStep mass mass') (perturbedStartLaw_nonneg s) (sum_perturbedStartLaw s)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (perturbedStep_hazard hmass hmass' htotal htotal')
    (separationMass_perturbedStart s mass mass') m
  linarith

theorem reportPathLaw_nonneg {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (y : Fin (m + 1) → ER n) :
    0 ≤ reportPathLaw s m y :=
  Finset.sum_nonneg fun _ _ ↦ skeletonPathWeight_nonneg
    (fun ξ ξ' ↦ kingmanStep_nonneg (blocks_le_card ξ) ξ') (fun _ ↦ by split_ifs <;> norm_num) m _

theorem sum_reportPathLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ) :
    ∑ y, reportPathLaw s m y = 1 := by
  unfold reportPathLaw
  rw [Finset.sum_fiberwise univ (fun ξpath : Fin (m + 1) → ER n ↦ fun k ↦ observed s (ξpath k))
    (skeletonPathWeight (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m),
    sum_skeletonPathWeight (sum_kingmanStep (n := n))]
  simp

theorem massPathLaw_nonneg {n : ℕ} (s : Fin n → Fin n) {mass : Fin n → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (htotal : ∑ i, mass i ≤ 1) (m : ℕ) (y : Fin (m + 1) → ER n) :
    0 ≤ massPathLaw s mass m y :=
  skeletonPathWeight_nonneg (massStep_nonneg hmass htotal) (fun _ ↦ by split_ifs <;> norm_num)
    m y

theorem sum_massPathLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ) :
    ∑ y, massPathLaw s mass m y = 1 := by
  unfold massPathLaw
  rw [sum_skeletonPathWeight (sum_massStep mass)]
  simp

/-- **Theorem F, (F2), for the uniformized skeleton.**  After `m` rings of the uniformizing clock
the path of the graph's report and the path of `Z` with masses `mass'` from the interface have
total variation at most `m(m-1)/(4n) + m ‖unitMass n - mass'‖₁`.

Assumes: `0 < n`, and `mass'` is nonnegative with total at most one. -/
theorem report_mass_pathTotalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {mass' : Fin n → ℝ} (hmass' : ∀ i, 0 ≤ mass' i) (htotal' : ∑ i, mass' i ≤ 1) (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y|
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) + (∑ i, |unitMass n i - mass' i|) * m := by
  have h1 := report_multiplicative_pathTotalVariation_le hn s m
  have h2 := massPathTotalVariation_le s (unitMass_nonneg n) hmass' (sum_unitMass_le_one n)
    htotal' m
  have htri : ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y|
      ≤ ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - multiplicativePathLaw s m y|
        + ∑ y : Fin (m + 1) → ER n,
          |massPathLaw s (unitMass n) m y - massPathLaw s mass' m y| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ ↦ ?_
    rw [multiplicativePathLaw_eq_massPathLaw]
    exact abs_sub_le _ _ _
  linarith

/-- The total variation of the skeleton paths in (F2) is a probability. -/
theorem report_mass_pathTotalVariation_le_one {n : ℕ} (s : Fin n → Fin n) {mass' : Fin n → ℝ}
    (hmass' : ∀ i, 0 ≤ mass' i) (htotal' : ∑ i, mass' i ≤ 1) (m : ℕ) :
    1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y| ≤ 1 := by
  have hr := sum_reportPathLaw s m
  have hz := sum_massPathLaw s mass' m
  have hle : ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y|
      ≤ ∑ y : Fin (m + 1) → ER n, (reportPathLaw s m y + massPathLaw s mass' m y) :=
    Finset.sum_le_sum fun y _ ↦ by
      have h1 := reportPathLaw_nonneg s m y
      have h2 := massPathLaw_nonneg s hmass' htotal' m y
      rw [abs_le]
      constructor <;> linarith
  rw [Finset.sum_add_distrib, hr, hz] at hle
  linarith

/-- **Theorem F, (F2).**  Run both skeletons at the rings of a Poisson clock of rate one in scaled
time; by scaled time `U` the paths of the graph's report and of `Z` with masses `mass'` from the
interface have total variation at most `min {1, U²/(4n) + U ‖unitMass n - mass'‖₁}`.

Assumes: `0 < n`, and `mass'` is nonnegative with total at most one. -/
theorem report_mass_poissonTotalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {mass' : Fin n → ℝ} (hmass' : ∀ i, 0 ≤ mass' i) (htotal' : ∑ i, mass' i ≤ 1)
    (U : NNReal) :
    poissonMixture U (fun m ↦
        1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y|)
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n) + U * ∑ i, |unitMass n i - mass' i|) := by
  have ha0 : ∀ m : ℕ, 0 ≤ 1 / 2 * ∑ y : Fin (m + 1) → ER n,
      |reportPathLaw s m y - massPathLaw s mass' m y| :=
    fun m ↦ mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  refine le_min
    (poissonMixture_le_one ha0 (report_mass_pathTotalVariation_le_one s hmass' htotal')) ?_
  have hB : HasSum (fun m : ℕ ↦ poissonPMFReal U m
      * ((m : ℝ) * ((m : ℝ) - 1) / (4 * n) + (∑ i, |unitMass n i - mass' i|) * m))
      ((U : ℝ) ^ 2 / (4 * n) + (∑ i, |unitMass n i - mass' i|) * U) := by
    have h1 := (hasSum_poissonPMFReal_mul_descFactorial U).div_const (4 * n)
    have h2 := (hasSum_poissonPMFReal_mul_nat U).mul_left (∑ i, |unitMass n i - mass' i|)
    have hfun : (fun m : ℕ ↦ poissonPMFReal U m
        * ((m : ℝ) * ((m : ℝ) - 1) / (4 * n) + (∑ i, |unitMass n i - mass' i|) * m))
        = fun m ↦ poissonPMFReal U m * ((m : ℝ) * ((m : ℝ) - 1)) / (4 * n)
          + (∑ i, |unitMass n i - mass' i|) * (poissonPMFReal U m * m) :=
      funext fun m ↦ by ring
    rw [hfun]
    exact h1.add h2
  have hterm : ∀ m : ℕ, poissonPMFReal U m * (1 / 2 * ∑ y : Fin (m + 1) → ER n,
      |reportPathLaw s m y - massPathLaw s mass' m y|)
      ≤ poissonPMFReal U m
        * ((m : ℝ) * ((m : ℝ) - 1) / (4 * n) + (∑ i, |unitMass n i - mass' i|) * m) :=
    fun m ↦ mul_le_mul_of_nonneg_left (report_mass_pathTotalVariation_le hn s hmass' htotal' m)
      poissonPMFReal_nonneg
  have hA : Summable fun m : ℕ ↦ poissonPMFReal U m * (1 / 2 * ∑ y : Fin (m + 1) → ER n,
      |reportPathLaw s m y - massPathLaw s mass' m y|) :=
    Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (ha0 m)) hterm
      hB.summable
  have hle := hasSum_le hterm hA.hasSum hB
  calc poissonMixture U (fun m ↦
        1 / 2 * ∑ y : Fin (m + 1) → ER n, |reportPathLaw s m y - massPathLaw s mass' m y|)
      ≤ (U : ℝ) ^ 2 / (4 * n) + (∑ i, |unitMass n i - mass' i|) * U := hle
    _ = (U : ℝ) ^ 2 / (4 * n) + U * ∑ i, |unitMass n i - mass' i| := by ring

/-! ### Masses on the fibers -/

/-- **The number of individuals in a fiber of the interface**, `c_F`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A cardinality. -/
def fiberSize {n : ℕ} (s : Fin n → Fin n) (F : Quotient (graphKer s)) : ℕ :=
  (univ.filter fun i ↦ Quotient.mk (graphKer s) i = F).card

theorem fiberSize_pos {n : ℕ} (s : Fin n → Fin n) (F : Quotient (graphKer s)) :
    0 < fiberSize s F := by
  obtain ⟨i, rfl⟩ := quotient_mk_surjective (graphKer s) F
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

/-- **A mass vector on the fibers, spread evenly over each fiber's individuals.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A mass divided by a count. -/
def spreadMass {n : ℕ} (s : Fin n → Fin n) (p : Quotient (graphKer s) → ℝ) : Fin n → ℝ :=
  fun i ↦ p (Quotient.mk (graphKer s) i) / fiberSize s (Quotient.mk (graphKer s) i)

theorem spreadMass_nonneg {n : ℕ} (s : Fin n → Fin n) {p : Quotient (graphKer s) → ℝ}
    (hp : ∀ F, 0 ≤ p F) (i : Fin n) : 0 ≤ spreadMass s p i :=
  div_nonneg (hp _) (Nat.cast_nonneg _)

/-- **The components of the interface carry the fiber masses.** -/
theorem blockMass_spreadMass_graphKer {n : ℕ} (s : Fin n → Fin n)
    (p : Quotient (graphKer s) → ℝ) (F : Quotient (graphKer s)) :
    blockMass (spreadMass s p) (graphKer s) F = p F := by
  have hconst : ∀ i ∈ univ.filter (fun i ↦ Quotient.mk (graphKer s) i = F),
      spreadMass s p i = p F / fiberSize s F := by
    intro i hi
    simp only [spreadMass, (Finset.mem_filter.mp hi).2]
  have hne : (fiberSize s F : ℝ) ≠ 0 := by exact_mod_cast (fiberSize_pos s F).ne'
  unfold blockMass
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  show (fiberSize s F : ℝ) * (p F / fiberSize s F) = p F
  rw [mul_comm, div_mul_cancel₀ _ hne]

theorem sum_spreadMass {n : ℕ} (s : Fin n → Fin n) (p : Quotient (graphKer s) → ℝ) :
    ∑ i, spreadMass s p i = ∑ F, p F := by
  rw [← sum_blockMass (spreadMass s p) (graphKer s)]
  exact Finset.sum_congr rfl fun F _ ↦ blockMass_spreadMass_graphKer s p F

/-- **The `ℓ¹` distance of the spread masses to unit masses is `‖p^(n) - p‖₁`**,
`∑_F |c_F/n - p_F|`. -/
theorem sum_abs_unitMass_sub_spreadMass {n : ℕ} (s : Fin n → Fin n)
    (p : Quotient (graphKer s) → ℝ) :
    ∑ i, |unitMass n i - spreadMass s p i| = ∑ F, |(fiberSize s F : ℝ) / n - p F| := by
  rw [← Finset.sum_fiberwise univ (Quotient.mk (graphKer s))
    fun i ↦ |unitMass n i - spreadMass s p i|]
  refine Finset.sum_congr rfl fun F _ ↦ ?_
  have hconst : ∀ i ∈ univ.filter (fun i ↦ Quotient.mk (graphKer s) i = F),
      |unitMass n i - spreadMass s p i| = |1 / (n : ℝ) - p F / fiberSize s F| := by
    intro i hi
    simp only [unitMass, spreadMass, (Finset.mem_filter.mp hi).2]
  have hpos : (0 : ℝ) < fiberSize s F := by exact_mod_cast fiberSize_pos s F
  have hcancel : (fiberSize s F : ℝ) * (p F / fiberSize s F) = p F := by
    rw [mul_comm, div_mul_cancel₀ _ hpos.ne']
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  show (fiberSize s F : ℝ) * |1 / (n : ℝ) - p F / fiberSize s F|
    = |(fiberSize s F : ℝ) / n - p F|
  calc (fiberSize s F : ℝ) * |1 / (n : ℝ) - p F / fiberSize s F|
      = |(fiberSize s F : ℝ) * (1 / (n : ℝ) - p F / fiberSize s F)| := by
        rw [abs_mul, abs_of_pos hpos]
    _ = |(fiberSize s F : ℝ) / n - p F| := by
        rw [mul_sub, hcancel, mul_one_div]

/-- **Theorem F, (F2), in the note's form.**  For a mass vector `p` on the fibers, nonnegative
with total at most one, by scaled time `U` the paths of the graph's report and of `Z_p` from the
interface have total variation at most `min {1, U²/(4n) + U ∑_F |c_F/n - p_F|}`.

Assumes: `0 < n`, and `p` is nonnegative with total at most one. -/
theorem report_spread_poissonTotalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {p : Quotient (graphKer s) → ℝ} (hp : ∀ F, 0 ≤ p F) (hptotal : ∑ F, p F ≤ 1)
    (U : NNReal) :
    poissonMixture U (fun m ↦ 1 / 2 * ∑ y : Fin (m + 1) → ER n,
        |reportPathLaw s m y - massPathLaw s (spreadMass s p) m y|)
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n) + U * ∑ F, |(fiberSize s F : ℝ) / n - p F|) := by
  have h := report_mass_poissonTotalVariation_le hn s (spreadMass_nonneg s hp)
    ((sum_spreadMass s p).trans_le hptotal) U
  rwa [sum_abs_unitMass_sub_spreadMass] at h

end

end Descent.Pangenome.GraphCoalescent

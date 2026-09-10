/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservableClosureLaw

assert_below Descent.Decision Descent.Program

/-!
A Boolean-cube selection counterexample at every moment order. Laws differing
only in the full interaction have identical proper-subset moments, while a
strictly positive fitness function turns that interaction into a first moment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LowMomentObstruction

variable {I : Type*} [Fintype I] [DecidableEq I]

def sign (bit : Bool) : ℝ := if bit then -1 else 1

def factor (subset : Finset I) (index : I) (bit : Bool) : ℝ :=
  if index ∈ subset then sign bit else 1

noncomputable def character (subset : Finset I) (point : I → Bool) : ℝ :=
  ∏ index, factor subset index (point index)

@[simp] theorem sign_sq (bit : Bool) : sign bit * sign bit = 1 := by
  cases bit <;> norm_num [sign]

@[simp] theorem character_empty (point : I → Bool) : character ∅ point = 1 := by
  simp [character, factor]

theorem character_abs (subset : Finset I) (point : I → Bool) : |character subset point| = 1 := by
  rw [character, Finset.abs_prod]
  have heach (index : I) : |factor subset index (point index)| = 1 := by
    by_cases hmem : index ∈ subset <;> cases point index <;> simp [factor, sign, hmem]
  simp [heach]

omit [Fintype I] in
private theorem factor_product_sum (first second : Finset I) (index : I) :
    ∑ bit : Bool, factor first index bit * factor second index bit =
      if (index ∈ first ↔ index ∈ second) then 2 else 0 := by
  by_cases hfirst : index ∈ first <;> by_cases hsecond : index ∈ second <;>
    norm_num [factor, sign, hfirst, hsecond, Fintype.sum_bool]

/-- Exact Walsh orthogonality, with no asymptotic or moment approximation. -/
theorem character_orthogonality (first second : Finset I) :
    ∑ point : I → Bool, character first point * character second point =
      if first = second then (2 : ℝ) ^ Fintype.card I else 0 := by
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (index : I) (bit : Bool) ↦
    factor first index bit * factor second index bit)]
  simp only [factor_product_sum]
  by_cases heq : first = second
  · subst second
    simp
  · rw [if_neg heq]
    have hexists : ∃ index, ¬(index ∈ first ↔ index ∈ second) := by
      by_contra hnone
      push_neg at hnone
      exact heq (Finset.ext hnone)
    obtain ⟨index, hindex⟩ := hexists
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    simp [hindex]

noncomputable def cubeAverage (metric : (I → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ Fintype.card I)⁻¹ * ∑ point, metric point

theorem average_character_product (first second : Finset I) :
    cubeAverage (fun point ↦ character first point * character second point) =
      if first = second then 1 else 0 := by
  rw [cubeAverage, character_orthogonality]
  split_ifs <;> simp

theorem average_character (subset : Finset I) :
    cubeAverage (character subset) = if subset = ∅ then 1 else 0 := by
  simpa using average_character_product subset ∅

/-- The full-interaction perturbation of the uniform cube law. -/
noncomputable def perturbation [Nonempty I] (amplitude : ℝ) (hbound : |amplitude| ≤ 1) :
    FiniteReportLaw (I → Bool) where
  mass point := ((2 : ℝ) ^ Fintype.card I)⁻¹ *
    (1 + amplitude * character Finset.univ point)
  mass_nonneg point := by
    apply mul_nonneg (by positivity)
    have habs : |amplitude * character Finset.univ point| ≤ 1 := by
      rw [abs_mul, character_abs, mul_one]
      exact hbound
    linarith [(abs_le.mp habs).1]
  mass_sum := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
    have hchar : ((2 : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ point : I → Bool, character Finset.univ point = 0 := by
      have hc := average_character (Finset.univ : Finset I)
      rw [if_neg Finset.univ_nonempty.ne_empty] at hc
      exact hc
    have hcount : (Fintype.card (I → Bool) : ℝ) = (2 : ℝ) ^ Fintype.card I := by
      simp
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hcount, inv_mul_cancel₀ (by positivity)]
    rw [show ((2 : ℝ) ^ Fintype.card I)⁻¹ *
      (amplitude * ∑ point : I → Bool, character Finset.univ point) = 0 by
        rw [mul_left_comm, hchar, mul_zero]]
    simp

theorem perturbation_moment [Nonempty I] (amplitude : ℝ) (hbound : |amplitude| ≤ 1)
    (subset : Finset I) :
    (perturbation amplitude hbound).expectation (character subset) =
      (if subset = ∅ then 1 else 0) + amplitude * (if subset = Finset.univ then 1 else 0) := by
  have hfirst := average_character subset
  have hsecond := average_character_product (Finset.univ : Finset I) subset
  unfold cubeAverage at hfirst hsecond
  unfold FiniteReportLaw.expectation perturbation
  simp only
  simp_rw [mul_assoc, add_mul, one_mul, mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst]
  rw [show (∑ point : I → Bool,
      ((2 : ℝ) ^ Fintype.card I)⁻¹ * amplitude *
        character Finset.univ point * character subset point) =
      amplitude * (((2 : ℝ) ^ Fintype.card I)⁻¹ *
        ∑ point : I → Bool, character Finset.univ point * character subset point) by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point _
    ring]
  rw [hsecond]
  simp only [eq_comm]

theorem proper_moments_equal [Nonempty I] (amplitude : ℝ) (hbound : |amplitude| ≤ 1)
    (subset : Finset I) (hproper : subset ≠ Finset.univ) :
    (perturbation amplitude hbound).expectation (character subset) =
      (perturbation (-amplitude) (by simpa using hbound)).expectation (character subset) := by
  rw [perturbation_moment, perturbation_moment, if_neg hproper]
  ring


/-- The complement interaction and the omitted locus multiply to the full interaction. -/
theorem complement_mul_singleton (distinguished : I) (point : I → Bool) :
    character (Finset.univ.erase distinguished) point * character {distinguished} point =
      character Finset.univ point := by
  simp only [character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  by_cases heq : index = distinguished <;> simp [factor, heq]

theorem selection_fitness_pos (selection : ℝ) (hselection : |selection| < 1)
    (distinguished : I) (point : I → Bool) :
    0 < 1 + selection * character (Finset.univ.erase distinguished) point := by
  have habs : |selection * character (Finset.univ.erase distinguished) point| < 1 := by
    rw [abs_mul, character_abs, mul_one]
    exact hselection
  linarith [(abs_lt.mp habs).1]

variable [Nontrivial I]

private theorem complement_nonempty (distinguished : I) :
    Finset.univ.erase distinguished ≠ (∅ : Finset I) := by
  obtain ⟨other, hother⟩ := exists_ne distinguished
  apply Finset.ne_empty_of_mem
  exact Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩

omit [DecidableEq I] in
private theorem singleton_proper (distinguished : I) :
    ({distinguished} : Finset I) ≠ Finset.univ := by
  obtain ⟨other, hother⟩ := exists_ne distinguished
  intro heq
  have hm : other ∈ ({distinguished} : Finset I) := heq.symm ▸ Finset.mem_univ other
  exact hother (Finset.mem_singleton.mp hm)

theorem mean_fitness_one (amplitude : ℝ) (hbound : |amplitude| ≤ 1)
    (selection : ℝ) (distinguished : I) :
    (perturbation amplitude hbound).expectation
      (fun point ↦ 1 + selection * character (Finset.univ.erase distinguished) point) = 1 := by
  have hm := perturbation_moment amplitude hbound (Finset.univ.erase distinguished)
  have hproper : Finset.univ.erase distinguished ≠ (Finset.univ : Finset I) := by
    intro heq
    have := heq.symm ▸ Finset.mem_univ distinguished
    exact Finset.notMem_erase distinguished Finset.univ this
  rw [if_neg (complement_nonempty distinguished), if_neg hproper] at hm
  simp only [mul_zero, add_zero] at hm
  unfold FiniteReportLaw.expectation at hm ⊢
  simp_rw [mul_add, mul_one, mul_left_comm _ selection]
  rw [Finset.sum_add_distrib, FiniteReportLaw.mass_sum, ← Finset.mul_sum, hm]
  ring

noncomputable def selectedLaw (amplitude : ℝ) (hbound : |amplitude| ≤ 1)
    (selection : ℝ) (hselection : |selection| < 1) (distinguished : I) :
    FiniteReportLaw (I → Bool) where
  mass point := (perturbation amplitude hbound).mass point *
    (1 + selection * character (Finset.univ.erase distinguished) point)
  mass_nonneg point := mul_nonneg ((perturbation amplitude hbound).mass_nonneg point)
    (le_of_lt (selection_fitness_pos selection hselection distinguished point))
  mass_sum := mean_fitness_one amplitude hbound selection distinguished

theorem selected_first_moment (amplitude : ℝ) (hbound : |amplitude| ≤ 1)
    (selection : ℝ) (hselection : |selection| < 1) (distinguished : I) :
    (selectedLaw amplitude hbound selection hselection distinguished).expectation
      (character {distinguished}) = selection * amplitude := by
  have hfirst := perturbation_moment amplitude hbound ({distinguished} : Finset I)
  have hfull := perturbation_moment amplitude hbound (Finset.univ : Finset I)
  rw [if_neg (Finset.singleton_nonempty distinguished).ne_empty,
    if_neg (singleton_proper distinguished)] at hfirst
  simp only [mul_zero, add_zero] at hfirst
  rw [if_neg Finset.univ_nonempty.ne_empty, if_pos rfl] at hfull
  simp only [zero_add, mul_one] at hfull
  change (∑ point, ((perturbation amplitude hbound).mass point *
    (1 + selection * character (Finset.univ.erase distinguished) point)) *
      character {distinguished} point) = selection * amplitude
  calc
    _ = (perturbation amplitude hbound).expectation (character {distinguished}) +
        selection * (perturbation amplitude hbound).expectation (character Finset.univ) := by
      unfold FiniteReportLaw.expectation
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro point _
      rw [← complement_mul_singleton distinguished point]
      ring
    _ = selection * amplitude := by rw [hfirst, hfull, zero_add]

/-- Every moment order has two valid genetic laws with identical moments up
to that order, but distinct next-generation first moments under the same
strictly positive selection rule. This rules out an autonomous low-moment law
for the unrestricted selection model class. -/
theorem every_order_obstruction (order : ℕ)
    (amplitude : ℝ) (hamplitude : 0 < amplitude) (hbound : amplitude ≤ 1)
    (selection : ℝ) (hselection : |selection| < 1) (hnonzero : selection ≠ 0) :
    ∃ (first second selectedFirst selectedSecond : FiniteReportLaw (Fin (order + 2) → Bool)),
      first = perturbation amplitude (by rwa [abs_of_pos hamplitude]) ∧
      second = perturbation (-amplitude) (by rwa [abs_neg, abs_of_pos hamplitude]) ∧
      (∀ subset : Finset (Fin (order + 2)), subset.card ≤ order + 1 →
        first.expectation (character subset) = second.expectation (character subset)) ∧
      selectedFirst = selectedLaw amplitude (by rwa [abs_of_pos hamplitude])
        selection hselection (0 : Fin (order + 2)) ∧
      selectedSecond = selectedLaw (-amplitude) (by rwa [abs_neg, abs_of_pos hamplitude])
        selection hselection (0 : Fin (order + 2)) ∧
      selectedFirst.expectation (character {0}) = selection * amplitude ∧
      selectedSecond.expectation (character {0}) = -(selection * amplitude) ∧
      selectedFirst.expectation (character {0}) ≠
        selectedSecond.expectation (character {0}) := by
  have habs : |amplitude| ≤ 1 := by rwa [abs_of_pos hamplitude]
  have hneg : |-amplitude| ≤ 1 := by simpa using habs
  refine ⟨perturbation amplitude habs, perturbation (-amplitude) hneg,
    selectedLaw amplitude habs selection hselection 0,
    selectedLaw (-amplitude) hneg selection hselection 0, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro subset hcard
    apply proper_moments_equal
    intro heq
    rw [heq, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  · exact selected_first_moment _ _ _ _ _
  · rw [selected_first_moment]
    ring
  · rw [selected_first_moment, selected_first_moment]
    have hprod : selection * amplitude ≠ 0 := mul_ne_zero hnonzero (ne_of_gt hamplitude)
    intro heq
    apply hprod
    linarith

end Descent.Portability.LowMomentObstruction

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Jump approximations of the forward generator on sampling observables

The forward generator (7.1) of the research note "Ancestral locality" is a diffusion on the laws of
a finite state space `H`, and it is reached as a limit of pure jump processes. Two jumps are used.
A resampling jump moves a law `p` to `ε δ_x + (1 - ε) p` with `x` drawn from `p`: a fraction `ε`
of the population is replaced by the offspring of one individual. A decision jump moves `p` to
`ε R_{K_T}(p) + (1 - ε) p`: a fraction `ε` of the population is replaced by children of the rule
`T`. This module computes both jumps on sampling observables exactly and bounds their deviation
from the backward generator of `SamplingDuality`.

The expansion. Sampling `n` genomes from `ε v + (1 - ε) q` chooses the component `v`
independently for every argument with probability `ε`, so
`H_f(ε v + (1 - ε) q) = ∑_S ε^{|S|} (1 - ε)^{n - |S|} M_f(S; v, q)` over the sets `S` of arguments
(`samplingObservable_mix`), where the mixed observable `M_f(S; v, q)` samples the arguments in `S`
from `v` and the others from `q` (`mixedObservable`). It is at most `‖f‖` when `v` and `q` are laws
(`abs_mixedObservable_le`), the weights sum to one (`sum_powerset_weight`), and the weight of the
sets of at least `j` arguments is at most `C(n, j) ε^j` (`sum_choose_mul_tail_le`).

The resampling jump. Averaged over `x ~ p`, the mixed observable `resampleTerm f S p` is `H_f(p)`
when `S` has at most one argument (`resampleTerm_empty`, `resampleTerm_singleton`), and the
coalesced observable `H_{C_ab f}(p)` when `S = {a, b}` (`resampleTerm_pair`); the sets of two
arguments are the pairs `a < b` (`sum_powersetCard_two`). Hence
`|E_x H_f(ε δ_x + (1 - ε) p) - H_f(p) - ε² ∑_{a<b} (H_{C_ab f} - H_f)(p)| ≤ 4 ε³ n³ ‖f‖`
(`abs_resample_sub_le`): at rate `c / ε²` the resampling jump has the coalescence part of the
backward generator, up to `4 c ε n³ ‖f‖`.

The decision jump. The child law `R_{K_T}(p)` is a law (`reproduce_ruleKernel_mem_stdSimplex`), and
the mixed observable with one argument from it is the branched observable `H_{B_{a,T} f}(p)`
(`mixedObservable_singleton_reproduce`), so
`|H_f(ε R_{K_T}(p) + (1 - ε) p) - H_f(p) - ε ∑_a (H_{B_{a,T} f} - H_f)(p)| ≤ 4 ε² n² ‖f‖`
(`abs_decision_sub_le`): at rate `r / ε` the decision jump has the branching part, up to
`4 r ε n² ‖f‖`.

Scope. The estimates are at one law `p` and one arity `n`; the jump operators on continuous
functions, their semigroups and the passage `ε → 0` are not in this module.

## Empirical status

None. The bodies here are finite sums over sets of arguments and sampled genomes, with binomial
bounds, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.DecisionJumpExpansion

open Finset

variable {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}

/-! ## Mixed sampling observables -/

/-- **The mixed sampling observable** `M_f(S; v, q)`: the arguments in `S` are sampled from `v`
and the others from `q`. -/
def mixedObservable (f : (Fin n → H) → ℝ) (S : Finset (Fin n)) (v q : H → ℝ) : ℝ :=
  ∑ w, f w * ∏ a, if a ∈ S then v (w a) else q (w a)

/-- With no argument from `v`, the mixed observable is the sampling observable of `q`. -/
theorem mixedObservable_empty (f : (Fin n → H) → ℝ) (v q : H → ℝ) :
    mixedObservable f ∅ v q = samplingObservable f q := by
  simp [mixedObservable, samplingObservable]

/-- The mixed product splits over `S` and its complement. -/
theorem prod_ite_mem_eq (S : Finset (Fin n)) (v q : H → ℝ) (w : Fin n → H) :
    ∏ a, (if a ∈ S then v (w a) else q (w a)) = (∏ a ∈ S, v (w a)) * ∏ a ∈ Sᶜ, q (w a) := by
  rw [prod_ite]
  congr 1 <;> refine prod_congr ?_ fun _ _ ↦ rfl <;> ext a <;> simp

/-- **The expansion of a mixture**:
`H_f(ε v + (1 - ε) q) = ∑_S ε^{|S|} (1 - ε)^{n - |S|} M_f(S; v, q)`. -/
theorem samplingObservable_mix (f : (Fin n → H) → ℝ) (v q : H → ℝ) (ε : ℝ) :
    samplingObservable f (ε • v + (1 - ε) • q) =
      ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ε ^ S.card * (1 - ε) ^ (n - S.card) * mixedObservable f S v q := by
  unfold samplingObservable mixedObservable
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun w _ ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [prod_add, mul_sum]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, ← compl_eq_univ_sdiff,
    card_compl, Fintype.card_fin, prod_ite_mem_eq]
  ring

/-- A point mass is a law. -/
theorem pointMass_mem_stdSimplex (x : H) : (Pi.single x 1 : H → ℝ) ∈ stdSimplex ℝ H := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply]

/-- **Sampling from laws, the mixed observable is at most `‖f‖`.** -/
theorem abs_mixedObservable_le (f : (Fin n → H) → ℝ) (S : Finset (Fin n)) {v q : H → ℝ}
    (hv : v ∈ stdSimplex ℝ H) (hq : q ∈ stdSimplex ℝ H) : |mixedObservable f S v q| ≤ ‖f‖ := by
  have hnonneg : ∀ w : Fin n → H, 0 ≤ ∏ a, (if a ∈ S then v (w a) else q (w a)) :=
    fun w ↦ prod_nonneg fun a _ ↦ by
      split_ifs
      · exact hv.1 _
      · exact hq.1 _
  have htotal : ∑ w : Fin n → H, ∏ a, (if a ∈ S then v (w a) else q (w a)) = 1 := by
    have h := prod_univ_sum (fun _ : Fin n ↦ (univ : Finset H))
      (fun a h ↦ if a ∈ S then v h else q h)
    rw [Fintype.piFinset_univ] at h
    calc ∑ w : Fin n → H, ∏ a, (if a ∈ S then v (w a) else q (w a))
        = ∏ a : Fin n, ∑ h, (if a ∈ S then v h else q h) := h.symm
      _ = 1 := prod_eq_one fun a _ ↦ by
          split_ifs
          · exact hv.2
          · exact hq.2
  unfold mixedObservable
  calc |∑ w, f w * ∏ a, (if a ∈ S then v (w a) else q (w a))|
      ≤ ∑ w, |f w * ∏ a, (if a ∈ S then v (w a) else q (w a))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, ‖f‖ * ∏ a, (if a ∈ S then v (w a) else q (w a)) := by
        refine sum_le_sum fun w _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hnonneg w)]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm f w) (hnonneg w)
    _ = ‖f‖ := by rw [← mul_sum, htotal, mul_one]

/-- A sampling observable of a law is at most `‖f‖`. -/
theorem abs_samplingObservable_le (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : p ∈ stdSimplex ℝ H) : |samplingObservable f p| ≤ ‖f‖ := by
  rw [← mixedObservable_empty f p p]
  exact abs_mixedObservable_le f ∅ hp hp

/-! ## Binomial weights of the sets of arguments -/

/-- **The weights of the sets of arguments sum to one.** -/
theorem sum_powerset_weight (n : ℕ) (ε : ℝ) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, ε ^ S.card * (1 - ε) ^ (n - S.card) = 1 := by
  calc ∑ S ∈ (univ : Finset (Fin n)).powerset, ε ^ S.card * (1 - ε) ^ (n - S.card)
      = ∑ k ∈ range ((univ : Finset (Fin n)).card + 1),
          ((univ : Finset (Fin n)).card.choose k) • (ε ^ k * (1 - ε) ^ (n - k)) :=
        sum_powerset_apply_card (fun k ↦ ε ^ k * (1 - ε) ^ (n - k))
    _ = (ε + (1 - ε)) ^ n := by
        rw [add_pow, card_univ, Fintype.card_fin]
        exact sum_congr rfl fun k _ ↦ by rw [nsmul_eq_mul]; ring
    _ = 1 := by rw [show ε + (1 - ε) = 1 by ring, one_pow]

/-- **The binomial tail.** The weight of at least `j` successes among `n` trials of probability
`x` is at most `C(n, j) x^j`. -/
theorem sum_choose_mul_tail_le (n j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (if j ≤ k then x ^ k * (1 - x) ^ (n - k) else 0) ≤
      (n.choose j : ℝ) * x ^ j := by
  rcases le_or_gt j n with hj | hj
  · obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
    rw [show j + m + 1 = j + (m + 1) by ring, sum_range_add]
    have hfirst : ∑ k ∈ range j, ((j + m).choose k : ℝ) *
        (if j ≤ k then x ^ k * (1 - x) ^ (j + m - k) else 0) = 0 :=
      sum_eq_zero fun k hk ↦ by
        rw [if_neg (by rw [mem_range] at hk; omega), mul_zero]
    rw [hfirst, zero_add]
    have hbinom : ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (x ^ i * (1 - x) ^ (m - i)) = 1 := by
      have h := add_pow x (1 - x) m
      rw [show x + (1 - x) = 1 by ring, one_pow] at h
      rw [h]
      exact sum_congr rfl fun i _ ↦ by ring
    calc ∑ i ∈ range (m + 1), ((j + m).choose (j + i) : ℝ) *
          (if j ≤ j + i then x ^ (j + i) * (1 - x) ^ (j + m - (j + i)) else 0)
        ≤ ∑ i ∈ range (m + 1), ((j + m).choose j : ℝ) * x ^ j *
            ((m.choose i : ℝ) * (x ^ i * (1 - x) ^ (m - i))) := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [if_pos (Nat.le_add_right j i), Nat.add_sub_add_left, pow_add]
          have hchoose :
              ((j + m).choose (j + i) : ℝ) ≤ ((j + m).choose j : ℝ) * (m.choose i : ℝ) := by
            have hmul := Nat.choose_mul (n := j + m) (k := j + i) (s := j) (Nat.le_add_right j i)
            rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hmul
            have hpos : 0 < (j + i).choose j := Nat.choose_pos (Nat.le_add_right j i)
            exact_mod_cast (Nat.le_mul_of_pos_right _ hpos).trans hmul.le
          have hterm : 0 ≤ x ^ j * (x ^ i * (1 - x) ^ (m - i)) :=
            mul_nonneg (pow_nonneg hx0 j)
              (mul_nonneg (pow_nonneg hx0 i) (pow_nonneg (sub_nonneg.mpr hx1) _))
          nlinarith [mul_le_mul_of_nonneg_right hchoose hterm]
      _ = ((j + m).choose j : ℝ) * x ^ j := by rw [← mul_sum, hbinom, mul_one]
  · have hzero : ∀ k ∈ range (n + 1), (n.choose k : ℝ) *
        (if j ≤ k then x ^ k * (1 - x) ^ (n - k) else 0) = 0 := fun k hk ↦ by
      rw [if_neg (by rw [mem_range] at hk; omega), mul_zero]
    rw [sum_eq_zero hzero, Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]

/-- The weight of the sets of at least `j` arguments, as a binomial tail. -/
theorem sum_powerset_tail_eq (n j : ℕ) (ε : ℝ) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset,
        (if j ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0) =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (if j ≤ k then ε ^ k * (1 - ε) ^ (n - k) else 0) := by
  calc ∑ S ∈ (univ : Finset (Fin n)).powerset,
        (if j ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0)
      = ∑ k ∈ range ((univ : Finset (Fin n)).card + 1), ((univ : Finset (Fin n)).card.choose k) •
          (if j ≤ k then ε ^ k * (1 - ε) ^ (n - k) else 0) :=
        sum_powerset_apply_card (fun k ↦ if j ≤ k then ε ^ k * (1 - ε) ^ (n - k) else 0)
    _ = _ := by
        rw [card_univ, Fintype.card_fin]
        exact sum_congr rfl fun k _ ↦ nsmul_eq_mul _ _

/-- **Bernoulli's bound on the untouched arguments**: `0 ≤ 1 - (1 - ε)^k ≤ n ε` for `k ≤ n`. -/
theorem one_sub_pow_bounds {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {k n : ℕ} (hk : k ≤ n) :
    0 ≤ 1 - (1 - ε) ^ k ∧ 1 - (1 - ε) ^ k ≤ n * ε := by
  refine ⟨sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hε1) (by linarith)), ?_⟩
  have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -ε) k
  rw [← sub_eq_add_neg] at h
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_right hkn hε0]

/-! ## The resampling jump -/

/-- **The resampling term** of a set `S` of arguments: the arguments in `S` share one genome `x`
drawn from `p`, and the others are sampled from `p`. -/
def resampleTerm (f : (Fin n → H) → ℝ) (S : Finset (Fin n)) (p : H → ℝ) : ℝ :=
  ∑ x, p x * mixedObservable f S (Pi.single x 1) p

/-- A resampling term of a law is at most `‖f‖`. -/
theorem abs_resampleTerm_le (f : (Fin n → H) → ℝ) (S : Finset (Fin n)) {p : H → ℝ}
    (hp : p ∈ stdSimplex ℝ H) : |resampleTerm f S p| ≤ ‖f‖ := by
  unfold resampleTerm
  calc |∑ x, p x * mixedObservable f S (Pi.single x 1) p|
      ≤ ∑ x, |p x * mixedObservable f S (Pi.single x 1) p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p x * ‖f‖ := by
        refine sum_le_sum fun x _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hp.1 x)]
        exact mul_le_mul_of_nonneg_left
          (abs_mixedObservable_le f S (pointMass_mem_stdSimplex x) hp) (hp.1 x)
    _ = ‖f‖ := by rw [← sum_mul, hp.2, one_mul]

/-- With no argument resampled, the resampling term is the sampling observable. -/
theorem resampleTerm_empty (f : (Fin n → H) → ℝ) {p : H → ℝ} (hp : ∑ h, p h = 1) :
    resampleTerm f ∅ p = samplingObservable f p := by
  simp only [resampleTerm, mixedObservable_empty, ← sum_mul, hp, one_mul]

/-- **One resampled argument is a sample from `p`.** -/
theorem resampleTerm_singleton (f : (Fin n → H) → ℝ) (a : Fin n) (p : H → ℝ) :
    resampleTerm f {a} p = samplingObservable f p := by
  unfold resampleTerm mixedObservable samplingObservable
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun w _ ↦ ?_
  have hprod : ∀ x : H, ∏ c, (if c ∈ ({a} : Finset (Fin n)) then (Pi.single x 1 : H → ℝ) (w c)
      else p (w c)) = (Pi.single x 1 : H → ℝ) (w a) * ∏ c ∈ univ.erase a, p (w c) := by
    intro x
    rw [← mul_prod_erase univ _ (mem_univ a), if_pos (mem_singleton_self a)]
    congr 1
    exact prod_congr rfl fun c hc ↦ if_neg (by simpa using ne_of_mem_erase hc)
  simp only [hprod]
  have hx : ∀ x : H, p x * (f w * ((Pi.single x 1 : H → ℝ) (w a) *
      ∏ c ∈ univ.erase a, p (w c))) =
        if w a = x then p (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) else 0 := by
    intro x
    by_cases hwx : w a = x
    · rw [if_pos hwx, hwx, Pi.single_eq_same]
      ring
    · rw [if_neg hwx, Pi.single_eq_of_ne hwx]
      ring
  rw [sum_congr rfl fun x _ ↦ hx x, sum_ite_eq, if_pos (mem_univ _),
    ← mul_prod_erase univ (fun c ↦ p (w c)) (mem_univ a)]
  ring

/-- **Two resampled arguments coalesce.** On a vector of total mass one, the resampling term of
`{a, b}` is the coalesced observable `H_{C_ab f}(p)`. -/
theorem resampleTerm_pair {a b : Fin n} (hab : a ≠ b) (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : ∑ h, p h = 1) :
    resampleTerm f {a, b} p = samplingObservable (coalesceArguments a b f) p := by
  rw [samplingObservable_coalesceArguments hab f hp]
  unfold resampleTerm mixedObservable
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun w _ ↦ ?_
  have hb : b ∈ univ.erase a := mem_erase.mpr ⟨hab.symm, mem_univ b⟩
  have hprod : ∀ x : H, ∏ c, (if c ∈ ({a, b} : Finset (Fin n)) then (Pi.single x 1 : H → ℝ) (w c)
      else p (w c)) = (Pi.single x 1 : H → ℝ) (w a) *
        ((Pi.single x 1 : H → ℝ) (w b) * ∏ c ∈ (univ.erase a).erase b, p (w c)) := by
    intro x
    rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase (univ.erase a) _ hb,
      if_pos (mem_insert_self a {b}), if_pos (mem_insert_of_mem (mem_singleton_self b))]
    congr 2
    refine prod_congr rfl fun c hc ↦ if_neg ?_
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨ne_of_mem_erase (mem_of_mem_erase hc), ne_of_mem_erase hc⟩
  simp only [hprod]
  have herase : ∏ c ∈ univ.erase a, p (w c) = p (w b) * ∏ c ∈ (univ.erase a).erase b, p (w c) :=
    (mul_prod_erase _ (fun c ↦ p (w c)) hb).symm
  rw [herase]
  by_cases hw : w a = w b
  · rw [if_pos hw, ← hw]
    have hx : ∀ x : H, p x * (f w * ((Pi.single x 1 : H → ℝ) (w a) *
        ((Pi.single x 1 : H → ℝ) (w a) * ∏ c ∈ (univ.erase a).erase b, p (w c)))) =
          if w a = x then p (w a) * (f w * ∏ c ∈ (univ.erase a).erase b, p (w c)) else 0 := by
      intro x
      by_cases hwx : w a = x
      · rw [if_pos hwx, hwx, Pi.single_eq_same]
        ring
      · rw [if_neg hwx, Pi.single_eq_of_ne hwx]
        ring
    rw [sum_congr rfl fun x _ ↦ hx x, sum_ite_eq, if_pos (mem_univ _)]
    ring
  · rw [if_neg hw]
    refine sum_eq_zero fun x _ ↦ ?_
    by_cases hwx : w a = x
    · have hwb : w b ≠ x := fun h ↦ hw (hwx.trans h.symm)
      rw [Pi.single_eq_of_ne hwb]
      ring
    · rw [Pi.single_eq_of_ne hwx]
      ring

/-- **The sets of two arguments are the pairs `a < b`.** -/
theorem sum_powersetCard_two (F : Finset (Fin n) → ℝ) :
    ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)), F S = ∑ b, ∑ a ∈ Iio b, F {a, b} := by
  have himage : powersetCard 2 (univ : Finset (Fin n)) =
      (univ.sigma fun b : Fin n ↦ Iio b).image fun q ↦ ({q.2, q.1} : Finset (Fin n)) := by
    ext S
    rw [mem_powersetCard, mem_image]
    constructor
    · rintro ⟨-, hS⟩
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hS
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨⟨y, x⟩, mem_sigma.mpr ⟨mem_univ _, mem_Iio.mpr h⟩, rfl⟩
      · exact ⟨⟨x, y⟩, mem_sigma.mpr ⟨mem_univ _, mem_Iio.mpr h⟩, pair_comm y x⟩
    · rintro ⟨⟨b, a⟩, hq, rfl⟩
      exact ⟨subset_univ _, card_pair (ne_of_lt (mem_Iio.mp (mem_sigma.mp hq).2))⟩
  rw [himage]
  refine (sum_image ?_).trans (sum_sigma _ _ _)
  rintro ⟨b, a⟩ hq ⟨b', a'⟩ hq' hpair
  have hab : a < b := mem_Iio.mp (mem_sigma.mp hq).2
  have hab' : a' < b' := mem_Iio.mp (mem_sigma.mp hq').2
  have hset : ({a, b} : Finset (Fin n)) = {a', b'} := hpair
  have ha : a ∈ ({a', b'} : Finset (Fin n)) := hset ▸ mem_insert_self a {b}
  have hb : b ∈ ({a', b'} : Finset (Fin n)) := hset ▸ mem_insert_of_mem (mem_singleton_self b)
  simp only [mem_insert, mem_singleton] at ha hb
  have hboth : a = a' ∧ b = b' := by
    rcases ha with h1 | h1 <;> rcases hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab.ne
    · exact ⟨h1, h2⟩
    · rw [h1, h2] at hab
      exact absurd hab' (lt_asymm hab)
    · exact absurd (h1.trans h2.symm) hab.ne
  obtain ⟨rfl, rfl⟩ := hboth
  rfl

/-- **The resampling jump against the coalescence generator.** For a law `p` and `0 ≤ ε ≤ 1`,
`|E_x H_f(ε δ_x + (1 - ε) p) - H_f(p) - ε² ∑_{a<b} (H_{C_ab f} - H_f)(p)| ≤ 4 ε³ n³ ‖f‖`. -/
theorem abs_resample_sub_le (f : (Fin n → H) → ℝ) {p : H → ℝ} (hp : p ∈ stdSimplex ℝ H) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |∑ x, p x * samplingObservable f (ε • Pi.single x 1 + (1 - ε) • p) -
        samplingObservable f p - ε ^ 2 * ∑ b, ∑ a ∈ Iio b,
          (samplingObservable (coalesceArguments a b f) p - samplingObservable f p)| ≤
      4 * ε ^ 3 * (n : ℝ) ^ 3 * ‖f‖ := by
  have hexp : ∑ x, p x * samplingObservable f (ε • Pi.single x 1 + (1 - ε) • p) -
      samplingObservable f p = ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p) := by
    have hsum : ∑ x, p x * samplingObservable f (ε • Pi.single x 1 + (1 - ε) • p) =
        ∑ S ∈ (univ : Finset (Fin n)).powerset,
          ε ^ S.card * (1 - ε) ^ (n - S.card) * resampleTerm f S p := by
      simp only [samplingObservable_mix, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun S _ ↦ ?_
      rw [resampleTerm, mul_sum]
      exact sum_congr rfl fun x _ ↦ by ring
    rw [hsum]
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, sum_powerset_weight, one_mul]
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin n)).powerset
    (fun S ↦ S.card = 2)
    (fun S ↦ ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p))
  rw [← powersetCard_eq_filter] at hsplit
  have hpairs : ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
      ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p) =
        ε ^ 2 * (1 - ε) ^ (n - 2) *
          ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
            (resampleTerm f S p - samplingObservable f p) := by
    rw [mul_sum]
    exact sum_congr rfl fun S hS ↦ by rw [(mem_powersetCard.mp hS).2]
  have hG : ∑ b, ∑ a ∈ Iio b,
      (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) =
        ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
          (resampleTerm f S p - samplingObservable f p) := by
    rw [sum_powersetCard_two]
    exact sum_congr rfl fun b _ ↦ sum_congr rfl fun a ha ↦ by
      rw [resampleTerm_pair (ne_of_lt (mem_Iio.mp ha)) f hp.2]
  have hGbound : |∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
      (resampleTerm f S p - samplingObservable f p)| ≤ (n : ℝ) ^ 2 * (2 * ‖f‖) := by
    calc |∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
          (resampleTerm f S p - samplingObservable f p)|
        ≤ ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
            |resampleTerm f S p - samplingObservable f p| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)), 2 * ‖f‖ := by
          refine sum_le_sum fun S _ ↦ ?_
          have h1 := abs_le.mp (abs_resampleTerm_le f S hp)
          have h2 := abs_le.mp (abs_samplingObservable_le f hp)
          exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      _ = (n.choose 2 : ℝ) * (2 * ‖f‖) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ 2 * (2 * ‖f‖) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n 2) (by positivity)
  have hrest : |∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
      ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p)| ≤
        (n : ℝ) ^ 3 * ε ^ 3 * (2 * ‖f‖) := by
    have hf2 : (0 : ℝ) ≤ 2 * ‖f‖ := by positivity
    calc |∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
          ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p)|
        ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
            |ε ^ S.card * (1 - ε) ^ (n - S.card) *
              (resampleTerm f S p - samplingObservable f p)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
            (if 3 ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0) * (2 * ‖f‖) := by
          refine sum_le_sum fun S hS ↦ ?_
          have hcard : S.card ≠ 2 := (mem_filter.mp hS).2
          have hw : 0 ≤ ε ^ S.card * (1 - ε) ^ (n - S.card) :=
            mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (sub_nonneg.mpr hε1) _)
          rcases lt_or_ge S.card 3 with h3 | h3
          · have hD : resampleTerm f S p - samplingObservable f p = 0 := by
              rcases Nat.lt_or_ge S.card 1 with h0 | h1
              · rw [card_eq_zero.mp (by omega), resampleTerm_empty f hp.2, sub_self]
              · obtain ⟨a, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
                rw [resampleTerm_singleton, sub_self]
            rw [hD, mul_zero, abs_zero, if_neg (by omega), zero_mul]
          · rw [if_pos h3, abs_mul, abs_of_nonneg hw]
            refine mul_le_mul_of_nonneg_left ?_ hw
            have h1 := abs_le.mp (abs_resampleTerm_le f S hp)
            have h2 := abs_le.mp (abs_samplingObservable_le f hp)
            exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset,
            (if 3 ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0) * (2 * ‖f‖) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ ↦ ?_
          refine mul_nonneg ?_ hf2
          split_ifs
          · exact mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (sub_nonneg.mpr hε1) _)
          · exact le_rfl
      _ = (∑ k ∈ range (n + 1), (n.choose k : ℝ) *
            (if 3 ≤ k then ε ^ k * (1 - ε) ^ (n - k) else 0)) * (2 * ‖f‖) := by
          rw [← sum_mul, sum_powerset_tail_eq]
      _ ≤ ((n.choose 3 : ℝ) * ε ^ 3) * (2 * ‖f‖) :=
          mul_le_mul_of_nonneg_right (sum_choose_mul_tail_le n 3 hε0 hε1) hf2
      _ ≤ (n : ℝ) ^ 3 * ε ^ 3 * (2 * ‖f‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.choose_le_pow n 3) (pow_nonneg hε0 3)) hf2
  obtain ⟨hb1, hb2⟩ := one_sub_pow_bounds hε0 hε1 (Nat.sub_le n 2)
  rw [hexp, ← hsplit, hpairs, hG]
  have hKG : |ε ^ 2 * (1 - (1 - ε) ^ (n - 2)) *
      ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
        (resampleTerm f S p - samplingObservable f p)| ≤ ε ^ 3 * (n : ℝ) ^ 3 * (2 * ‖f‖) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (pow_nonneg hε0 2) hb1)]
    calc ε ^ 2 * (1 - (1 - ε) ^ (n - 2)) *
          |∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
            (resampleTerm f S p - samplingObservable f p)|
        ≤ ε ^ 2 * ((n : ℝ) * ε) * ((n : ℝ) ^ 2 * (2 * ‖f‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hb2 (pow_nonneg hε0 2)) hGbound (abs_nonneg _)
            (mul_nonneg (pow_nonneg hε0 2) (mul_nonneg (Nat.cast_nonneg n) hε0))
      _ = ε ^ 3 * (n : ℝ) ^ 3 * (2 * ‖f‖) := by ring
  have hsum : ε ^ 2 * (1 - ε) ^ (n - 2) *
        ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
          (resampleTerm f S p - samplingObservable f p) +
      ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
        ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p) -
      ε ^ 2 * ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
        (resampleTerm f S p - samplingObservable f p) =
        ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 2,
          ε ^ S.card * (1 - ε) ^ (n - S.card) * (resampleTerm f S p - samplingObservable f p) -
        ε ^ 2 * (1 - (1 - ε) ^ (n - 2)) *
          ∑ S ∈ powersetCard 2 (univ : Finset (Fin n)),
            (resampleTerm f S p - samplingObservable f p) := by
    ring
  rw [hsum]
  have h1 := abs_le.mp hrest
  have h2 := abs_le.mp hKG
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-! ## The decision jump -/

/-- **The child law of a rule is a law.** -/
theorem reproduce_ruleKernel_mem_stdSimplex (T : H → H → H) {p : H → ℝ}
    (hp : p ∈ stdSimplex ℝ H) : reproduce (ruleKernel T) p ∈ stdSimplex ℝ H := by
  have hK : ∀ x y, ∑ z, ruleKernel T x y z = 1 := by
    intro x y
    simp only [ruleKernel, halfMix]
    rw [sum_add_distrib, ← sum_div, ← sum_div, sum_ite_eq, sum_ite_eq, if_pos (mem_univ _),
      if_pos (mem_univ _)]
    norm_num
  refine ⟨fun z ↦ sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦
    mul_nonneg (mul_nonneg (hp.1 x) (hp.1 y)) (halfMix_nonneg _ _ _), ?_⟩
  rw [sum_reproduce (ruleKernel T) p hK, hp.2, one_pow]

/-- **One argument from the child law is a branched argument.** -/
theorem mixedObservable_singleton_reproduce (T : H → H → H) (a : Fin n)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    mixedObservable f {a} (reproduce (ruleKernel T) p) p =
      samplingObservable (decisionBranch T a f) p := by
  rw [samplingObservable_decisionBranch_eq_sum]
  unfold mixedObservable
  refine sum_congr rfl fun w _ ↦ ?_
  have hrest : ∏ c ∈ univ.erase a, (if c ∈ ({a} : Finset (Fin n))
      then reproduce (ruleKernel T) p (w c) else p (w c)) = ∏ c ∈ univ.erase a, p (w c) :=
    prod_congr rfl fun c hc ↦ if_neg (by simpa using ne_of_mem_erase hc)
  rw [← mul_prod_erase univ _ (mem_univ a), if_pos (mem_singleton_self a), hrest]
  ring

/-- **The decision jump against the branching generator.** For a law `p` and `0 ≤ ε ≤ 1`,
`|H_f(ε R_{K_T}(p) + (1 - ε) p) - H_f(p) - ε ∑_a (H_{B_{a,T} f} - H_f)(p)| ≤ 4 ε² n² ‖f‖`. -/
theorem abs_decision_sub_le (T : H → H → H) (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : p ∈ stdSimplex ℝ H) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |samplingObservable f (ε • reproduce (ruleKernel T) p + (1 - ε) • p) -
        samplingObservable f p - ε * ∑ a,
          (samplingObservable (decisionBranch T a f) p - samplingObservable f p)| ≤
      4 * ε ^ 2 * (n : ℝ) ^ 2 * ‖f‖ := by
  have hv := reproduce_ruleKernel_mem_stdSimplex T hp
  have hexp : samplingObservable f (ε • reproduce (ruleKernel T) p + (1 - ε) • p) -
      samplingObservable f p = ∑ S ∈ (univ : Finset (Fin n)).powerset,
        ε ^ S.card * (1 - ε) ^ (n - S.card) *
          (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p) := by
    rw [samplingObservable_mix]
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, sum_powerset_weight, one_mul]
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin n)).powerset
    (fun S ↦ S.card = 1)
    (fun S ↦ ε ^ S.card * (1 - ε) ^ (n - S.card) *
      (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p))
  rw [← powersetCard_eq_filter] at hsplit
  have hsingles : ∑ S ∈ powersetCard 1 (univ : Finset (Fin n)),
      ε ^ S.card * (1 - ε) ^ (n - S.card) *
        (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p) =
      ε * (1 - ε) ^ (n - 1) *
        ∑ a, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) := by
    rw [powersetCard_one, sum_map, mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Function.Embedding.coeFn_mk, card_singleton, pow_one,
      mixedObservable_singleton_reproduce]
  have hGbound : |∑ a : Fin n,
      (samplingObservable (decisionBranch T a f) p - samplingObservable f p)| ≤
        (n : ℝ) * (2 * ‖f‖) := by
    calc |∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p)|
        ≤ ∑ a : Fin n,
            |samplingObservable (decisionBranch T a f) p - samplingObservable f p| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, 2 * ‖f‖ := by
          refine sum_le_sum fun a _ ↦ ?_
          have h1 := abs_le.mp (abs_mixedObservable_le f {a} hv hp)
          rw [mixedObservable_singleton_reproduce] at h1
          have h2 := abs_le.mp (abs_samplingObservable_le f hp)
          exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      _ = (n : ℝ) * (2 * ‖f‖) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hrest : |∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
      ε ^ S.card * (1 - ε) ^ (n - S.card) *
        (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p)| ≤
        (n : ℝ) ^ 2 * ε ^ 2 * (2 * ‖f‖) := by
    have hf2 : (0 : ℝ) ≤ 2 * ‖f‖ := by positivity
    calc |∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
          ε ^ S.card * (1 - ε) ^ (n - S.card) *
            (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p)|
        ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
            |ε ^ S.card * (1 - ε) ^ (n - S.card) *
              (mixedObservable f S (reproduce (ruleKernel T) p) p -
                samplingObservable f p)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
            (if 2 ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0) * (2 * ‖f‖) := by
          refine sum_le_sum fun S hS ↦ ?_
          have hcard : S.card ≠ 1 := (mem_filter.mp hS).2
          have hw : 0 ≤ ε ^ S.card * (1 - ε) ^ (n - S.card) :=
            mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (sub_nonneg.mpr hε1) _)
          rcases lt_or_ge S.card 2 with h2 | h2
          · have hD : mixedObservable f S (reproduce (ruleKernel T) p) p -
                samplingObservable f p = 0 := by
              rw [card_eq_zero.mp (by omega), mixedObservable_empty, sub_self]
            rw [hD, mul_zero, abs_zero, if_neg (by omega), zero_mul]
          · rw [if_pos h2, abs_mul, abs_of_nonneg hw]
            refine mul_le_mul_of_nonneg_left ?_ hw
            have h1 := abs_le.mp (abs_mixedObservable_le f S hv hp)
            have h3 := abs_le.mp (abs_samplingObservable_le f hp)
            exact abs_le.mpr ⟨by linarith [h1.1, h3.2], by linarith [h1.2, h3.1]⟩
      _ ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset,
            (if 2 ≤ S.card then ε ^ S.card * (1 - ε) ^ (n - S.card) else 0) * (2 * ‖f‖) := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ ↦ ?_
          refine mul_nonneg ?_ hf2
          split_ifs
          · exact mul_nonneg (pow_nonneg hε0 _) (pow_nonneg (sub_nonneg.mpr hε1) _)
          · exact le_rfl
      _ = (∑ k ∈ range (n + 1), (n.choose k : ℝ) *
            (if 2 ≤ k then ε ^ k * (1 - ε) ^ (n - k) else 0)) * (2 * ‖f‖) := by
          rw [← sum_mul, sum_powerset_tail_eq]
      _ ≤ ((n.choose 2 : ℝ) * ε ^ 2) * (2 * ‖f‖) :=
          mul_le_mul_of_nonneg_right (sum_choose_mul_tail_le n 2 hε0 hε1) hf2
      _ ≤ (n : ℝ) ^ 2 * ε ^ 2 * (2 * ‖f‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.choose_le_pow n 2) (pow_nonneg hε0 2)) hf2
  obtain ⟨hb1, hb2⟩ := one_sub_pow_bounds hε0 hε1 (Nat.sub_le n 1)
  rw [hexp, ← hsplit, hsingles]
  have hKG : |ε * (1 - (1 - ε) ^ (n - 1)) *
      ∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p)| ≤
        ε ^ 2 * (n : ℝ) ^ 2 * (2 * ‖f‖) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hε0 hb1)]
    calc ε * (1 - (1 - ε) ^ (n - 1)) *
          |∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p)|
        ≤ ε * ((n : ℝ) * ε) * ((n : ℝ) * (2 * ‖f‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hb2 hε0) hGbound (abs_nonneg _)
            (mul_nonneg hε0 (mul_nonneg (Nat.cast_nonneg n) hε0))
      _ = ε ^ 2 * (n : ℝ) ^ 2 * (2 * ‖f‖) := by ring
  have hsum : ε * (1 - ε) ^ (n - 1) *
        ∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) +
      ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
        ε ^ S.card * (1 - ε) ^ (n - S.card) *
          (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p) -
      ε * ∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) =
        ∑ S ∈ (univ : Finset (Fin n)).powerset with ¬S.card = 1,
          ε ^ S.card * (1 - ε) ^ (n - S.card) *
            (mixedObservable f S (reproduce (ruleKernel T) p) p - samplingObservable f p) -
        ε * (1 - (1 - ε) ^ (n - 1)) *
          ∑ a : Fin n, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) := by
    ring
  rw [hsum]
  have h1 := abs_le.mp hrest
  have h2 := abs_le.mp hKG
  refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

end Descent.Pangenome.AncestralLocality.DecisionJumpExpansion

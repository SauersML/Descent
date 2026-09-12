/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Descent.Coalescent.Duality

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# One allele: the sampling duality is Kingman's moment duality

The generator identity of `Descent.Pangenome.AncestralLocality.SamplingDuality` holds for every
finite state space and every observation. This file reads it at the smallest case the corpus
already knows, as a check that the two calculations agree.

The state space is `Bool`, the genome carrying or not carrying one allele, and `x = p true` is the
allele frequency of a vector `p` of total mass one. The observation `allCarriers n` says that all
`n` sampled genomes carry the allele. Its sampling observable is `x^n`
(`samplingObservable_allCarriers`), and after coalescing two arguments it is `x^{n-1}`
(`samplingObservable_coalesceArguments_allCarriers`). The resampling term of Theorem 6 is
therefore `c d_n (x^{n-1} - x^n)`. This is Kingman's block-count generator on the monomial
`x^n` in `Descent.Coalescent.Duality`, and by `Descent.Coalescent.duality_identity` it equals the
Wright-Fisher diffusion generator applied to `x^n`
(`resamplingGenerator_allCarriers`). So the multi-type forward generator (7.1) on `P(Bool)`,
with its line-derivative partials, agrees with the one-dimensional diffusion `½x(1-x)f''` on this
moment.

Scope. Only the all-carriers observation of a single allele is treated, with no decisions; the
other moments of `P(Bool)` and the identification of `P(Bool)` with the interval `[0, 1]` are not
formalized here.

## Empirical status

None. The bodies here are products of indicators and finite sums over a supplied vector, so no
measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

variable {n : ℕ}

/-- **The all-carriers observation**: every one of the `n` sampled genomes carries the allele. -/
def allCarriers (n : ℕ) (w : Fin n → Bool) : ℝ :=
  ∏ a, if w a = true then 1 else 0

/-- **The all-carriers moment is `x^n`**: `n` independent draws from `p` all carry the allele with
probability `p(true)^n`. -/
theorem samplingObservable_allCarriers (p : Bool → ℝ) :
    samplingObservable (allCarriers n) p = p true ^ n := by
  have hterm : ∀ w : Fin n → Bool, allCarriers n w * ∏ a, p (w a) =
      ∏ a, (if w a = true then p (w a) else 0) := fun w ↦ by
    rw [allCarriers, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ ↦ ?_
    split_ifs <;> simp
  calc samplingObservable (allCarriers n) p
      = ∑ w : Fin n → Bool, ∏ a, (if w a = true then p (w a) else 0) :=
        sum_congr rfl fun w _ ↦ hterm w
    _ = ∏ _a : Fin n, ∑ h : Bool, (if h = true then p h else 0) :=
        (Fintype.prod_sum fun (_ : Fin n) (h : Bool) ↦ if h = true then p h else 0).symm
    _ = p true ^ n := by simp [Fintype.sum_bool]

/-- **The coalesced all-carriers moment is `x^{n-1}`**: after two arguments share one genome, the
sample carries the allele exactly when `n - 1` independent draws do. Needs total mass one. -/
theorem samplingObservable_coalesceArguments_allCarriers {a b : Fin n} (hab : a ≠ b)
    {p : Bool → ℝ} (hp : p true + p false = 1) :
    samplingObservable (coalesceArguments a b (allCarriers n)) p = p true ^ (n - 1) := by
  have hmass : ∑ h, p h = 1 := by
    rw [Fintype.sum_bool]
    exact hp
  have herase : ∀ g : Fin n → ℝ,
      ∏ c, (if c = a then (1 : ℝ) else g c) = ∏ c ∈ univ.erase a, g c := fun g ↦
    calc ∏ c, (if c = a then (1 : ℝ) else g c)
        = ∏ c ∈ univ.erase a, (if c = a then (1 : ℝ) else g c) :=
          (prod_erase univ (f := fun c ↦ if c = a then (1 : ℝ) else g c) (a := a)
            (if_pos rfl)).symm
      _ = ∏ c ∈ univ.erase a, g c := prod_congr rfl fun c hc ↦ if_neg (ne_of_mem_erase hc)
  have hterm : ∀ w : Fin n → Bool,
      (if w a = w b then allCarriers n w * ∏ c ∈ univ.erase a, p (w c) else 0) =
        ∏ c, (if w c = true then (if c = a then 1 else p (w c)) else 0) := by
    intro w
    by_cases hall : ∀ c, w c = true
    · have hf : allCarriers n w = 1 := prod_eq_one fun c _ ↦ if_pos (hall c)
      have hrhs : ∏ c, (if w c = true then (if c = a then (1 : ℝ) else p (w c)) else 0) =
          ∏ c, (if c = a then (1 : ℝ) else p (w c)) :=
        prod_congr rfl fun c _ ↦ if_pos (hall c)
      rw [if_pos ((hall a).trans (hall b).symm), hf, one_mul, hrhs, herase fun c ↦ p (w c)]
    · push_neg at hall
      obtain ⟨c₀, hc₀⟩ := hall
      have hzero : ∀ g : Fin n → ℝ, g c₀ = 0 → ∏ c, g c = 0 := fun g hg ↦ by
        rw [← mul_prod_erase univ g (mem_univ c₀), hg, zero_mul]
      have hf : allCarriers n w = 0 := hzero (fun c ↦ if w c = true then 1 else 0) (if_neg hc₀)
      rw [hzero (fun c ↦ if w c = true then (if c = a then 1 else p (w c)) else 0) (if_neg hc₀),
        hf, zero_mul, ite_self]
  rw [samplingObservable_coalesceArguments hab _ hmass]
  calc ∑ w, (if w a = w b then allCarriers n w * ∏ c ∈ univ.erase a, p (w c) else 0)
      = ∑ w : Fin n → Bool, ∏ c, (if w c = true then (if c = a then 1 else p (w c)) else 0) :=
        sum_congr rfl fun w _ ↦ hterm w
    _ = ∏ c : Fin n, ∑ h : Bool, (if h = true then (if c = a then 1 else p h) else 0) :=
        (Fintype.prod_sum fun (c : Fin n) (h : Bool) ↦
          if h = true then (if c = a then 1 else p h) else 0).symm
    _ = ∏ c : Fin n, (if c = a then 1 else p true) := by simp [Fintype.sum_bool]
    _ = p true ^ (n - 1) := by
        rw [herase fun _ ↦ p true]
        simp [card_erase_of_mem]

/-- **Theorem 6 at one allele is Kingman's moment duality.** On a vector of total mass one, the
resampling part of the forward generator (7.1), applied to the all-carriers moment of `m + 2`
genomes, is `c` times the Wright-Fisher diffusion generator applied to `x^{m+2}`,
`Descent.Coalescent.diffusionOnPow`, at the allele frequency `x = p true`. -/
theorem resamplingGenerator_allCarriers (c : ℝ) (m : ℕ) {p : Bool → ℝ}
    (hp : p true + p false = 1) :
    resamplingGenerator c (samplingObservable (allCarriers (m + 2))) p =
      c * Coalescent.diffusionOnPow m (p true) := by
  have hmass : ∑ h, p h = 1 := by
    rw [Fintype.sum_bool]
    exact hp
  rw [resamplingGenerator_samplingObservable c _ hmass, Coalescent.duality_identity,
    Coalescent.coalescentOnPow, ← sum_card_Iio_eq_deathRate, sum_mul]
  congr 1
  refine sum_congr rfl fun b _ ↦ ?_
  have hpair : ∀ a ∈ Iio b,
      samplingObservable (coalesceArguments a b (allCarriers (m + 2))) p -
        samplingObservable (allCarriers (m + 2)) p = p true ^ (m + 1) - p true ^ (m + 2) :=
    fun a ha ↦ by
      rw [samplingObservable_coalesceArguments_allCarriers (ne_of_lt (mem_Iio.mp ha)) hp,
        samplingObservable_allCarriers]
      rfl
  rw [sum_congr rfl hpair, sum_const, nsmul_eq_mul]

end Descent.Pangenome.AncestralLocality

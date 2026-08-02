import Calibrator.Condensation
import Calibrator.ObservationalCeiling
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Cumulant blindness: no cumulant criterion decides chaos universality

Two independent obstructions to characterizing Gaussian universality of low-influence
chaos by cumulant data, formalized at their combinatorial cores.

## Statement of force, up front

Both results below are **negative** results whose force is deliberately understated.

* The hidden-tilt construction (Section 1) is, under centering, a *mean-shift*
  artifact: a centered reformulation must renormalize by the conditional variance, and
  the detecting polynomial survives only in drifted form. The theorem's letter stands
  — cumulants of every order `≤ K` are exactly Gaussian while universality fails —
  but it is the weakest of the negative results and should not be presented as more.
* The diagonal-contraction bound (Section 2) is close to tautological *relative to the
  class of criteria it quantifies over*, which we define ourselves. Its value is
  decisiveness against the exact question asked ("does vanishing of a family of
  normalized cumulant contractions characterize universality?"), not depth.

The load-bearing negative result of the arc is not here; it is the condensation
mechanism in `Calibrator.Condensation` and the completeness statement in
`Calibrator.JetBarrier`.

## Genetics reading

A "cumulant criterion" on a genotype matrix is any diagnostic built from joint moments
of bounded order along low-influence (polygenic) directions: LD-score style second
moments, score skewness and kurtosis, moment-matching goodness-of-fit for a polygenic
score, third- and fourth-order interaction summaries. Section 1 says such a diagnostic
can be made *exactly* Gaussian to any prescribed order while the aggregate's law is
not Gaussian at all; Section 2 says that pushing to *all* orders does not help, because
the normalization forced by polygenicity (`max_i Influence_i → 0`) crushes every
diagonal cumulant by `tau ^ ((r - 2) / 2)`. Diagnostics of this family cannot certify
the score-distribution assumptions they are usually used to certify.

## Applicability to genotypes: unrestricted

Unlike the sign-erasure results of `Calibrator.EpistaticChaos` and the completeness
results of `Calibrator.JetBarrier`, **nothing in this file assumes the coordinate law is
sign-symmetric.** Section 1 is a pigeonhole about multi-index supports and the oddness
of the *tilt* function `s`, not of the coordinate law; Section 2 quantifies over every
i.i.d. law, explicitly including the ones that fail universality.

This matters because a standardized Hardy-Weinberg genotype is sign-symmetric at
exactly one allele frequency, `q = 1/2`
(`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff`), so results carrying
that hypothesis say nothing about a real allele frequency spectrum. The results here
carry no such restriction: the cumulant-blindness conclusions apply to hard-called
genotypes, to imputed dosages, and to every allele frequency, without an applicability
caveat. Together with the drift theory of `Calibrator.Condensation`, this file is the
part of the arc that transfers to genotype data unconditionally.
-/

open scoped BigOperators
open Finset

/-!
## 1. Hidden higher-order tilts: matching all cumulants up to order `K`

The construction tilts the standard Gaussian on `R ^ d` by
`∏_j (1 + delta * ∏_{i ∈ B_j} s(x_i))` over disjoint blocks `B_j` of size `K + 1`,
where `s` is odd and bounded (`s = tanh`), so that each factor is a density and blocks
stay independent.

The reason every joint moment of total order `≤ K` is *exactly* Gaussian is a
pigeonhole, and that pigeonhole is what we prove: a multi-index of total order at most
`K` supported on a block of size `K + 1` must leave some coordinate of the block
untouched, and that coordinate contributes the factor `E[s(g)] = 0`.
-/

section HiddenTilt

variable {ι : Type*} [DecidableEq ι]

/-- **The pigeonhole behind exact cumulant matching.** If a multi-index `a` has total
order at most `K` on a block of `K + 1` coordinates, some coordinate of the block has
exponent zero. -/
theorem exists_zero_exponent_of_sum_lt_card
    (B : Finset ι) (a : ι → ℕ) (K : ℕ)
    (hcard : B.card = K + 1) (hsum : ∑ i ∈ B, a i ≤ K) :
    ∃ i ∈ B, a i = 0 := by
  by_contra hcon
  push_neg at hcon
  have hge : ∀ i ∈ B, 1 ≤ a i := by
    intro i hi
    exact Nat.one_le_iff_ne_zero.mpr (hcon i hi)
  have hle : B.card ≤ ∑ i ∈ B, a i := by
    simpa using Finset.card_nsmul_le_sum B a 1 hge
  rw [hcard] at hle
  omega

/-- **Exact vanishing of the tilt contribution.** The tilt's contribution to a joint
moment of total order `≤ K` is the product, over the block, of `E[g ^ (a i) * s(g)]`.
Whenever `s` is odd and centered, the factor at an untouched coordinate is
`E[s(g)] = 0`, so the whole product vanishes.

Here `tiltMoment n = E[g ^ n * s(g)]` and the hypothesis `htilt0 : tiltMoment 0 = 0`
is exactly `E[s(g)] = 0`. -/
theorem tilt_contribution_eq_zero
    (B : Finset ι) (a : ι → ℕ) (K : ℕ) (tiltMoment : ℕ → ℝ)
    (htilt0 : tiltMoment 0 = 0)
    (hcard : B.card = K + 1) (hsum : ∑ i ∈ B, a i ≤ K) :
    ∏ i ∈ B, tiltMoment (a i) = 0 := by
  obtain ⟨i, hiB, hai⟩ := exists_zero_exponent_of_sum_lt_card B a K hcard hsum
  refine Finset.prod_eq_zero hiB ?_
  rw [hai, htilt0]

/-- **Theorem 1 (hidden-tilt cumulant matching), abstract form.** Package the two
facts a decision rule sees: all joint moments up to order `K` agree with the Gaussian
(hence all cumulants up to order `K` agree, being polynomial in those moments), while
the models differ in universality status.

The conclusion is stated in the form that refutes the problem's request: *no function
of the order-`≤ K` cumulant tensors, with no continuity or computability assumption
whatsoever, decides covariance universality.*

The logic is `Calibrator.ObservationalCeiling.ProbeBlindness.no_criterion_of_factors`;
all this theorem contributes is the witness pair. -/
theorem no_fixed_order_cumulant_criterion
    {Model Cumulants Decision : Type*}
    (cumulantsUpTo : Model → Cumulants)
    (universal : Model → Prop)
    (m₀ m₁ : Model)
    (hmatch : cumulantsUpTo m₀ = cumulantsUpTo m₁)
    (h₀ : universal m₀) (h₁ : ¬ universal m₁) :
    ¬ ∃ decide : Cumulants → Decision, ∃ accept : Decision → Prop,
        ∀ m : Model, universal m ↔ accept (decide (cumulantsUpTo m)) := by
  rintro ⟨decide, accept, hdec⟩
  exact
    ({ positive := m₀, negative := m₁, same_data := hmatch, holds := h₀, fails := h₁ } :
        ProbeBlindness cumulantsUpTo universal).no_criterion_of_factors decide
      ⟨accept, hdec⟩

end HiddenTilt

/-!
## 2. Normalized contractions of every order: the diagonal collapse

For an i.i.d. law the joint cumulant tensor is supported on the diagonal (independence
kills mixed cumulants), so an `r`-th order normalized contraction against unit-norm,
low-influence test vectors reduces to `kappa_r * ∑_i a¹_i ⋯ aʳ_i`. Two of the vectors
are absorbed by Cauchy-Schwarz; the remaining `r - 2` are each bounded by
`sqrt tau` in the sup norm, where `tau` is the influence budget. So the contraction is
`O(tau ^ ((r - 2) / 2))` and vanishes for every fixed `r ≥ 3`.

The Gaussian's cumulants of order `≥ 3` vanish identically. Hence *every* fixed-order
normalized contraction agrees asymptotically between the i.i.d. law and the Gaussian,
whatever the i.i.d. law is — and by `Calibrator.Condensation` the two can nonetheless
differ in universality.
-/

section DiagonalContraction

variable {ι : Type*}

/-- Cauchy-Schwarz with a uniform bound on the remaining factors: the shape in which
the contraction estimate is used. -/
theorem abs_sum_mul_mul_le
    (s : Finset ι) (a b w : ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, |w i| ≤ M) :
    |∑ i ∈ s, a i * b i * w i|
      ≤ M * (Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2)) := by
  have step1 : |∑ i ∈ s, a i * b i * w i| ≤ ∑ i ∈ s, |a i| * |b i| * M := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM i hi) (by positivity)
  have step2 : ∑ i ∈ s, |a i| * |b i| * M = M * ∑ i ∈ s, |a i| * |b i| := by
    rw [← Finset.sum_mul, mul_comm]
  have step3 : ∑ i ∈ s, |a i| * |b i|
      ≤ Real.sqrt (∑ i ∈ s, |a i| ^ 2) * Real.sqrt (∑ i ∈ s, |b i| ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt s (fun i => |a i|) (fun i => |b i|)
  have hsq : ∀ f : ι → ℝ, ∑ i ∈ s, |f i| ^ 2 = ∑ i ∈ s, f i ^ 2 := by
    intro f
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [sq_abs]
  rw [hsq a, hsq b] at step3
  calc |∑ i ∈ s, a i * b i * w i|
      ≤ ∑ i ∈ s, |a i| * |b i| * M := step1
    _ = M * ∑ i ∈ s, |a i| * |b i| := step2
    _ ≤ M * (Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2)) :=
        mul_le_mul_of_nonneg_left step3 hM0

/-- **Theorem 3 (diagonal contraction bound).** For a diagonal cumulant tensor with
common diagonal entry `kappa`, the `r`-th order normalized contraction against
unit-`L2` test vectors `a`, `b` and `r - 2` further vectors each bounded by
`sqrt tau` in the sup norm satisfies

`|contraction| ≤ |kappa| * M`,

where `M` bounds the product of the remaining factors, i.e. `M = tau ^ ((r-2)/2)`.

Since `tau → 0` under the problem's low-influence hypothesis, every fixed-order
normalized contraction vanishes — for **every** i.i.d. coordinate law, including
those which fail universality. -/
theorem diagonal_contraction_bound
    (s : Finset ι) (κ : ℝ) (a b w : ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ s, |w i| ≤ M)
    (ha : ∑ i ∈ s, a i ^ 2 ≤ 1) (hb : ∑ i ∈ s, b i ^ 2 ≤ 1) :
    |κ * ∑ i ∈ s, a i * b i * w i| ≤ |κ| * M := by
  have hbound := abs_sum_mul_mul_le s a b w M hM0 hM
  have hsa : Real.sqrt (∑ i ∈ s, a i ^ 2) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt (∑ i ∈ s, b i ^ 2) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hb
  have hprod : Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (∑ i ∈ s, a i ^ 2), Real.sqrt_nonneg (∑ i ∈ s, b i ^ 2)]
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg κ)
  calc |∑ i ∈ s, a i * b i * w i|
      ≤ M * (Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2)) := hbound
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hprod hM0
    _ = M := mul_one M

/-- The sup-norm bound on the remaining `k` factors: each is bounded by `sqrt tau`,
so their product is bounded by `tau ^ (k / 2)`. Stated with `Real.sqrt tau ^ k` to
avoid real exponents. -/
theorem prod_sup_bound {k : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (e : Fin k → ℝ)
    (he : ∀ l, |e l| ≤ Real.sqrt τ) :
    |∏ l : Fin k, e l| ≤ Real.sqrt τ ^ k := by
  rw [Finset.abs_prod]
  calc ∏ l : Fin k, |e l|
      ≤ ∏ _l : Fin k, Real.sqrt τ := by
        refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => he i)
    _ = Real.sqrt τ ^ k := by simp

/-- **Every fixed-order normalized contraction vanishes in the low-influence limit.**
The bound `|kappa| * sqrt tau ^ k` tends to zero as `tau → 0` for every `k ≥ 1`, i.e.
for every contraction order `r = k + 2 ≥ 3`. -/
theorem contraction_bound_tendsto_zero {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) :
    Filter.Tendsto (fun τ : ℝ => |κ| * Real.sqrt τ ^ k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hk0 : k ≠ 0 := by omega
  -- `Continuous.const_mul` does not exist in mathlib; the constant factor goes in
  -- through `continuous_const.mul` instead.
  have hmul : Continuous fun τ : ℝ => |κ| * Real.sqrt τ ^ k :=
    continuous_const.mul (Real.continuous_sqrt.pow k)
  have hcont : Filter.Tendsto (fun τ : ℝ => |κ| * Real.sqrt τ ^ k)
      (nhds 0) (nhds (|κ| * Real.sqrt 0 ^ k)) := hmul.tendsto 0
  simp only [Real.sqrt_zero, zero_pow hk0, mul_zero] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

end DiagonalContraction

/-!
## 3. What survives

Put together with `Calibrator.Condensation`:

* fixed-order cumulant data can be made exactly Gaussian while universality fails
  (Section 1), so no fixed-order criterion decides the property;
* all-orders normalized contraction data is asymptotically *identical* for every
  i.i.d. law and the Gaussian (Section 2), so no contraction criterion of any order
  decides it either;
* the obstruction is therefore not in the cumulant category at all. It is in the
  Mellin data `theta ↦ E |x| ^ (2 * theta)` at the interior point `theta = 1`, which
  no jet at the origin determines.

`Calibrator.JetBarrier` computes exactly what *is* observable there.
-/

end Calibrator

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

**The load-bearing negative result of the arc is not here, and it is not anywhere.** This
paragraph used to send the reader to `Calibrator.Condensation` for the condensation
mechanism and to `Calibrator.JetBarrier` for the completeness statement. Both files
disclaim exactly those results in their own headers: Condensation says "THAT PROPOSAL IS
NOT PROVED IN THIS FILE" and "NOT ONE THEOREM HERE MENTIONS CHAOS, UNIVERSALITY, OR A LIMIT
LAW", and JetBarrier says its nonlattice completeness theorem "is not formalized here" and
that nothing replaces the removed barrier.

What those files do contain is real and much smaller: Condensation has rigorous two-sided
bounds on `condensationConstant = 2 - gamma - log 2` and on `gaussianJetVariance`, from
Mathlib's Euler-Mascheroni and `log 2` brackets, plus the window algebra; JetBarrier has the
lattice-inflation arithmetic `h / (1 - exp (-h)) > 1` and its bracket. Neither carries a
mechanism, and a citation chain that ends at a disclaimer is worse than no citation, because
it reads as a discharged obligation.

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

Section 2b makes that reading a theorem rather than a gloss. It defines the influence
of a locus as its share `β_j² h_j / ∑_i β_i² h_i` of the score variance, proves the
shares sum to one, proves that per-locus shares bounded between `d > 0` and `c` force
every influence below `c / (m · d)`, and concludes that the Section 2 bound therefore
tends to zero as the score spreads over more loci. Before that section the file
contained no locus, no effect size and no score, and the genetics reading was carried
entirely by this paragraph.

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

variable {ι : Type*}

/-- **The pigeonhole behind exact cumulant matching.** If a multi-index `a` has total
order at most `K` on a block of `K + 1` coordinates, some coordinate of the block has
exponent zero. -/
theorem exists_zero_exponent_of_sum_lt_card
    (B : Finset ι) (a : ι → ℕ) (K : ℕ)
    (hcard : B.card = K + 1) (hsum : ∑ i ∈ B, a i ≤ K) :
    ∃ i ∈ B, a i = 0 := by
  classical
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

/-- **The witness pair exists**, so the blindness theorem above is about something.

    `no_fixed_order_cumulant_criterion` takes `m₀ m₁` and their matching as hypotheses,
    and its docstring says "all this theorem contributes is the witness pair". It did not
    contribute one: with no instance the statement is a conditional nobody had discharged,
    and a blindness claim with no witnessing pair is vacuous in the direction that matters.

    Here is one. Models are tilt-moment sequences, `universal` means untilted, and the data
    a decision rule sees is the sequence truncated at order `K`. The tilted model agrees
    with the Gaussian at every order it is allowed to see and differs at order `K + 1`. -/
theorem exists_cumulantBlind_pair (K : ℕ) :
    ∃ (Model Cumulants : Type) (cumulantsUpTo : Model → Cumulants)
      (universal : Model → Prop) (m₀ m₁ : Model),
      cumulantsUpTo m₀ = cumulantsUpTo m₁ ∧ universal m₀ ∧ ¬ universal m₁ := by
  classical
  refine ⟨ℕ → ℝ, ℕ → ℝ, fun m n ↦ if n ≤ K then m n else 0, fun m ↦ m = 0,
    (fun _ ↦ 0), (fun n ↦ if n = K + 1 then 1 else 0), ?_, rfl, ?_⟩
  · funext n
    by_cases hn : n ≤ K
    · have hne : n ≠ K + 1 := by omega
      simp [hn, hne]
    · simp [hn]
  · intro hzero
    have := congrFun hzero (K + 1)
    simp at this

/-- **The blindness is realized**: at every fixed order there is a genuine pair no
    order-`≤ K` cumulant criterion can separate. This is the previous theorem applied to the
    witness, so the negative result no longer rests on an undischarged hypothesis. -/
theorem cumulant_criterion_blind (K : ℕ) :
    ∃ (Model Cumulants : Type) (cumulantsUpTo : Model → Cumulants)
      (universal : Model → Prop),
      ¬ ∃ decide : Cumulants → Prop, ∃ accept : Prop → Prop,
          ∀ m : Model, universal m ↔ accept (decide (cumulantsUpTo m)) := by
  obtain ⟨Model, Cumulants, cumulantsUpTo, universal, m₀, m₁, hmatch, h₀, h₁⟩ :=
    exists_cumulantBlind_pair K
  exact ⟨Model, Cumulants, cumulantsUpTo, universal,
    no_fixed_order_cumulant_criterion cumulantsUpTo universal m₀ m₁ hmatch h₀ h₁⟩

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
    Real.sum_mul_le_sqrt_mul_sqrt s (fun i ↦ |a i|) (fun i ↦ |b i|)
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
theorem prod_sup_bound {k : ℕ} (τ : ℝ) (e : Fin k → ℝ)
    (he : ∀ l, |e l| ≤ Real.sqrt τ) :
    |∏ l : Fin k, e l| ≤ Real.sqrt τ ^ k := by
  rw [Finset.abs_prod]
  calc ∏ l : Fin k, |e l|
      ≤ ∏ _l : Fin k, Real.sqrt τ := by
        refine Finset.prod_le_prod (fun i _ ↦ abs_nonneg _) (fun i _ ↦ he i)
    _ = Real.sqrt τ ^ k := by simp

/-- **Every fixed-order normalized contraction vanishes in the low-influence limit.**
The bound `|kappa| * sqrt tau ^ k` tends to zero as `tau → 0` for every `k ≥ 1`, i.e.
for every contraction order `r = k + 2 ≥ 3`. -/
theorem contraction_bound_tendsto_zero {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) :
    Filter.Tendsto (fun τ : ℝ ↦ |κ| * Real.sqrt τ ^ k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hk0 : k ≠ 0 := by omega
  -- `Continuous.const_mul` does not exist in mathlib; the constant factor goes in
  -- through `continuous_const.mul` instead.
  have hmul : Continuous fun τ : ℝ ↦ |κ| * Real.sqrt τ ^ k :=
    continuous_const.mul (Real.continuous_sqrt.pow k)
  have hcont : Filter.Tendsto (fun τ : ℝ ↦ |κ| * Real.sqrt τ ^ k)
      (nhds 0) (nhds (|κ| * Real.sqrt 0 ^ k)) := hmul.tendsto 0
  simp only [Real.sqrt_zero, zero_pow hk0, mul_zero] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

end DiagonalContraction

/-!
## 2b. The low-influence parameter, in score units

Section 2 bounds a normalized contraction by `|κ| · τ^(k/2)` where `τ` bounds the
remaining factors, and observes that `τ → 0` "under the problem's low-influence
hypothesis". That hypothesis was stated about an abstract index set. Nothing above
named a locus, an effect size or an allele frequency, so the genetics reading in the
header was carried entirely by prose.

This section supplies the missing object. For an additive score `∑_j β_j g_j` at
linkage equilibrium, locus `j` contributes `β_j² · h_j` to the score variance, where
`h_j` is the genotype variance at that locus — `2 p_j (1 - p_j)` for a Hardy--Weinberg
locus, but nothing here needs that form. The **influence** of locus `j` is its share of
the total, and polygenicity is the statement that no share is large.

What is proved: the shares are nonnegative and sum to one, and if every share lies
between `d > 0` and `c` then no influence exceeds `c / (m · d)`. Composing that with
Section 2 gives the bound in score units — as a score is spread over more loci, the
fixed-order normalized contraction bound tends to zero, whatever the per-locus law is.

The direction of the conclusion is worth stating plainly, because it is the reverse of
how such diagnostics are normally used. A vanishing bound is not evidence that the score
is Gaussian. It says the diagnostic cannot tell, because it is driven to zero by
polygenicity alone and would report the same value for a law that is not Gaussian at all.
-/

section PolygenicScoreInfluence

variable {m : ℕ}

/-- Variance contributed by locus `j` to an additive score: squared effect times
genotype variance.  At linkage equilibrium the score variance is the sum of these. -/
noncomputable def locusVarianceShare (β h : Fin m → ℝ) (j : Fin m) : ℝ :=
  β j ^ 2 * h j

/-- Additive score variance at linkage equilibrium. -/
noncomputable def scoreVariance (β h : Fin m → ℝ) : ℝ :=
  ∑ j, locusVarianceShare β h j

/-- **The influence of a locus**: its share of the score variance.  This is the
quantity Section 2's `τ` bounds, and polygenicity is the statement that it is small
for every locus. -/
noncomputable def locusInfluence (β h : Fin m → ℝ) (j : Fin m) : ℝ :=
  locusVarianceShare β h j / scoreVariance β h

theorem locusVarianceShare_nonneg (β h : Fin m → ℝ) (hh : ∀ j, 0 ≤ h j) (j : Fin m) :
    0 ≤ locusVarianceShare β h j :=
  mul_nonneg (sq_nonneg _) (hh j)

theorem scoreVariance_nonneg (β h : Fin m → ℝ) (hh : ∀ j, 0 ≤ h j) :
    0 ≤ scoreVariance β h :=
  Finset.sum_nonneg fun j _ ↦ locusVarianceShare_nonneg β h hh j

theorem locusInfluence_nonneg (β h : Fin m → ℝ) (hh : ∀ j, 0 ≤ h j) (j : Fin m) :
    0 ≤ locusInfluence β h j :=
  div_nonneg (locusVarianceShare_nonneg β h hh j) (scoreVariance_nonneg β h hh)

/-- **The influences are shares**: they sum to one whenever the score has positive
variance.  Without this the word "influence" would be decoration. -/
theorem sum_locusInfluence (β h : Fin m → ℝ) (hpos : 0 < scoreVariance β h) :
    ∑ j, locusInfluence β h j = 1 := by
  unfold locusInfluence
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

/-- **Polygenicity bounds every influence by `c / (m · d)`.**

If each locus contributes at most `c` and at least `d > 0` to the score variance, then
the total is at least `m · d` and no single share exceeds `c`, so no influence exceeds
`c / (m · d)`.  This is the hypothesis Section 2 needs, now expressed in effect sizes
and genotype variances rather than assumed about an abstract index. -/
theorem locusInfluence_le_of_shares_bounded
    (β h : Fin m → ℝ) (c d : ℝ) (hd : 0 < d) (hm : 0 < m)
    (hupper : ∀ j, locusVarianceShare β h j ≤ c)
    (hlower : ∀ j, d ≤ locusVarianceShare β h j) (j : Fin m) :
    locusInfluence β h j ≤ c / (m * d) := by
  have hmd : (0 : ℝ) < m * d := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have htotal : (m : ℝ) * d ≤ scoreVariance β h := by
    unfold scoreVariance
    calc (m : ℝ) * d = ∑ _j : Fin m, d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j, locusVarianceShare β h j := Finset.sum_le_sum fun j _ ↦ hlower j
  have hposV : 0 < scoreVariance β h := lt_of_lt_of_le hmd htotal
  unfold locusInfluence
  rw [div_le_div_iff₀ hposV hmd]
  calc locusVarianceShare β h j * ((m : ℝ) * d)
      ≤ c * ((m : ℝ) * d) := mul_le_mul_of_nonneg_right (hupper j) (le_of_lt hmd)
    _ ≤ c * scoreVariance β h := by
        refine mul_le_mul_of_nonneg_left htotal ?_
        exact le_trans (le_trans (le_of_lt hd) (hlower j)) (hupper j)

/-- **Cumulant blindness in score units.**  As a score is spread over more loci with
per-locus variance shares between `d > 0` and `c`, the fixed-order normalized
contraction bound of Section 2 tends to zero.

The conclusion runs the opposite way from how such a diagnostic is normally read. A
vanishing contraction is not evidence that the score's law is Gaussian: the bound is
driven to zero by polygenicity alone, and `diagonal_contraction_bound` holds for every
coordinate law, including the ones that fail universality. So the diagnostic reports the
same vanishing value whether or not the score is asymptotically Gaussian, and therefore
cannot certify the score-distribution assumption it is usually invoked to certify. -/
theorem pgs_contraction_bound_tendsto_zero {k : ℕ} (hk : 1 ≤ k) (κ c d : ℝ) (hd : 0 < d) :
    Filter.Tendsto (fun m : ℕ ↦ |κ| * Real.sqrt (c / (m * d)) ^ k)
      Filter.atTop (nhds 0) := by
  have hk0 : k ≠ 0 := by omega
  have hshape : ∀ m : ℕ, c / ((m : ℝ) * d) = (c / d) / (m : ℝ) := by
    intro m; rw [mul_comm, ← div_div]
  have hzero : Filter.Tendsto (fun m : ℕ ↦ c / ((m : ℝ) * d)) Filter.atTop (nhds 0) := by
    simp only [hshape]
    exact tendsto_const_div_atTop_nhds_zero_nat (c / d)
  have hcont : Continuous fun τ : ℝ ↦ |κ| * Real.sqrt τ ^ k :=
    continuous_const.mul (Real.continuous_sqrt.pow k)
  have := (hcont.tendsto 0).comp hzero
  simpa [Function.comp, Real.sqrt_zero, zero_pow hk0] using this

end PolygenicScoreInfluence

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

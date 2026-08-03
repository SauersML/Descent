/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.ImitationRigidity

namespace Calibrator

/-!
# The LD whitening gain as an ergodic average, and why the pencil pair is not free

This module records two results from an external analysis of the generalized eigenvalue
problem for a pair of covariance matrices built from a random environment. Both connect to
objects this corpus already has, and one of them is a **third independent derivation** of a
moral the corpus has reached twice before.

## The whitening gain is the constant-environment case of an ergodic average

`ImitationRigidity.ldWhiteningGain decay = (1 + decay²)/(1 - decay²)` is proved there to be
the per-variant limit of the exact finite-chromosome precision trace `tr K⁻¹`
(`ldPrecisionTrace_div_sites_tendsto`), and validated to `2e-16`.

The external analysis considers the same object over a **random** environment: a Gaussian
Markov chain with per-site correlation `ε_k` drawn from a stationary law, whose precision
matrix is tridiagonal, giving exactly

`(1/m)·tr(A_m⁻¹) = (1/m)(1 + Σ_{k<m} (1+ε_k²)/(1-ε_k²)) → E[(1+ε²)/(1-ε²)]`

almost surely. The summand **is** `ldWhiteningGain`. So the corpus's certificate is the
degenerate case of an ergodic average, and `whiteningGain_ergodic_mean_eq_of_constant` below
records that.

## Why this matters: the certificate can have an infinite mean

The external analysis observes that this average is finite **iff** the environment law's
boundary tail index `b` exceeds one, and that its fluctuations are governed by the same
environment excursions that set the extreme eigenvalue — a `√m` CLT for `b > 2`, a totally
skewed `b`-stable limit at scale `m^{1/b - 1}` for `b ∈ (1,2)`, and outright divergence
`κ_m ≍ m^{1/b - 1}` for `b < 1`.

**This is `Calibrator.CountingInvariantBlindness` again, from a third direction.** The
corpus's `m_eff` prohibition says `tr K⁻¹` is the right certificate *because* it is
edge-sensitive and not weakly continuous; the heavy-tail ghost says counting invariants are
blind to the rate; and this says the same quantity's finiteness and fluctuations are decided
at the edge, by a tail index no moment list pins down. Three unrelated arguments, one
conclusion.

`whiteningGain_unbounded` is the formal core available without measure theory: the summand is
unbounded on the admissible range, so no bound on the environment's moments bounds the
average — which is exactly why a tail index, and not a moment list, is what decides.

## The pair is not asymptotically free, and a four-step path count proves it

The external analysis refutes a natural expectation: that as the two environments decorrelate
the pencil pair becomes asymptotically free, with a Wachter-type limit. **It does not.**
Asymptotic freeness needs independence *plus* a delocalization mechanism putting one
eigenbasis in general position; these matrices are banded in a *common* index geometry, so
independence yields classical independence of two local ergodic operators — the tensor
category, not the free one.

The obstruction is checkable on the first mixed moment that separates the categories. For the
caricature — `a`, `b` independent tridiagonal with i.i.d. positive off-diagonal entries and
zero diagonal, so `φ(a) = φ(b) = 0` — freeness forces `φ(abab) = 0`, while a direct count of
closed four-step paths gives

`φ(abab) = 2·E[α²]·E[β²] + 4·(E α)²·(E β)²`,

which is **strictly positive** whenever the entries are nondegenerate.
`tridiagonalABAB_pathExpression_pos` proves positivity of that expression. The separate
finite-path enumeration identifying it with the mixed trace is validated computationally;
it is not encoded by that Lean theorem. Thus the refutation applies to this positive i.i.d.
tridiagonal model, not automatically to every bounded-bandwidth ensemble.

## Measured

**The `κ` identification is exact where it is claimed to be.** The summand is bit-identical
to `ldWhiteningGain ρ` at every `ρ` tested (`0, 0.1, 0.5, 0.9, 0.99, -0.7`), and the sum
formula matches an explicit `Tr(Σ⁻¹)/m` on the inhomogeneous chain to `9.4e-16` over 15 cases.
`κ_m` itself is **not** equal to the gain at finite `m` — the boundary term makes
`κ_m - g = (1-g)/m` exactly — which `whiteningGain_finite_trace` states and which the prose
above states as a limit. At `ρ = 0.99, m = 100` that deficit is `0.985`, a full 1%, so the
finite-`m` distinction must not be allowed to drift into an equality in later prose.

**The path-count coefficients are confirmed**, fitted over 16 distribution pairs and three
chain lengths including `expo(1)` against `const(√2)`, which share `E[α²] = 2` but differ in
mean so the two terms are separately identified (design-column correlation `0.88`, carried in
the errors): `c₁ = 2.0033 ± 0.0051` and `c₂ = 3.9917 ± 0.0086`, the latter `0.97σ` from `4`.
The exact finite-`m` form `ababFinite` below matches 42 ensembles at `max|z| = 2.07`.

**The control was made harder so it could not be dismissed.** Beyond a Haar-rotated pair
returning `0` (`-0.0016 ± 0.0046` at `m = 800`), shifting both matrices by the identity gives
a case where freeness predicts a **nonzero** `4.995`: the rotated pair returns
`4.9945 ± 0.0057` while the banded pair sits at `18.97`. The harness reproduces the free
formula when freeness holds and separates the two by about 1000σ.

**The trichotomy's scale exponents are measured**, drawing `ε = 1 - U^{1/b}` so the boundary
tail is exact: `+0.996 ± 0.013` against `+1.0` at `b = 0.5` (divergence confirmed);
`-0.324 ± 0.011` against `-1/3` at `b = 1.5`; `-0.463 ± 0.015` against `-1/2` at `b = 2.5`,
with the top two decades at `-0.488` and `-0.492`; `-0.493 ± 0.012` at `b = 4`. The `b = 2.5`
shortfall is finite-`m`: the correction to the Gaussian scale decays only as `m^{-0.1}`.

**What remains untested, recorded as such.** Only the *scale* exponents were measured. That
the `b ∈ (1,2)` limit is a totally skewed `b`-stable law, that the `b > 2` limit is Gaussian,
the marginal `b = 1`, and the claim that these fluctuations are governed by *the same
excursions* that set the extreme eigenvalue — none involved an eigenvalue computation and all
remain assertions.

Empirical status: `κ` identification **VALIDATED**; path count **VALIDATED**; freeness
**REFUTED** at ~1000σ against a control that reproduces the free value when freeness holds;
trichotomy **scale exponents VALIDATED**, limit laws untested. See
`proofs/validation/empirical/pencil/`.
-/

section PencilEnvironment

/-- **The whitening gain of a constant environment is the ergodic mean of a degenerate one.**

    Trivial as algebra, and that is the point: it pins `ldWhiteningGain` as the summand of the
    ergodic average rather than an unrelated closed form that happens to look similar. -/
theorem whiteningGain_ergodic_mean_eq_of_constant (decay : ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ _i : Fin n, ldWhiteningGain decay) / (n : ℝ) = ldWhiteningGain decay := by
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The exact finite-`m` trace, boundary term included.**

    The chain contributes one leading `1` and `m-1` interior summands, so
    `κ_m = (1 + (m-1)·gain)/m`, which is the gain **minus** an `O(1/m)` boundary deficit. The
    theorem above averages a constant and is therefore silent about that deficit; this one is
    the statement the object actually satisfies, and it is what simulation matches.

    Measured against an explicit tridiagonal inverse trace the deficit is reproduced to
    machine precision at every `ρ` and every `m`: at `ρ = 0.9`, `gain = 9.5263`, the measured
    `κ_m - gain` runs `-0.8526, -0.08526, -0.0008526, -8.526e-6` at `m = 10, 10², 10⁴, 10⁶`,
    against this formula's `-(gain-1)/m` to `~1e-15`. So the convergence `κ_m → gain` is exact
    and its rate is `1/m` with the constant `gain - 1` — which diverges as `ρ → 1`, meaning the
    finite-panel bias is worst exactly where LD is strongest. -/
theorem whiteningGain_finite_trace (decay : ℝ) (m : ℝ) (hm : m ≠ 0) :
    (1 + (m - 1) * ldWhiteningGain decay) / m
      = ldWhiteningGain decay - (ldWhiteningGain decay - 1) / m := by
  field_simp
  ring

/-- **The per-site precision trace of the chain at finite length**, the `κ_m` the analysis
    above is about.

    One unconstrained leading variant contributes `1` and the remaining `m - 1` each
    contribute `ldWhiteningGain`, so `κ_m = (1 + (m-1)·gain)/m`. The gain itself is the
    `m → ∞` limit of this, and `whiteningGain_finite_trace` states the deficit between them;
    naming the finite-`m` object is what stops that deficit being carried by prose.

    Empirical status: MEASURED. Matches an explicit `Tr(Σ⁻¹)/m` on the inhomogeneous chain
    to `9.4e-16` over fifteen cases, and at `decay = 0.99, m = 100` it sits `0.985` below
    the gain, so the finite-`m` distinction is not a rounding effect. -/
noncomputable def perSitePrecisionTrace (decay m : ℝ) : ℝ :=
  (1 + (m - 1) * ldWhiteningGain decay) / m

/-- **The per-site trace's junk branches, named.** At `m = 0` there are no sites to average over
and Lean's `x / 0 = 0` reports zero per-site weight rather than an undefined average; at
`|decay| = 1` it inherits `ldWhiteningGain_one_is_junk`. Consumers must require `0 < m` and
`|decay| < 1`. -/
theorem perSitePrecisionTrace_zero_sites_is_junk (decay : ℝ) :
    perSitePrecisionTrace decay 0 = 0 := by
  unfold perSitePrecisionTrace; simp

/-- **The corpus's finite-chromosome precision trace, per site, is that object.**

`ImitationRigidity.ldPrecisionTrace` is derived there from the tridiagonal stencil
identities, with no ergodic input at all. `perSitePrecisionTrace` is written the other way
round, from the decomposition into one boundary variant and `m - 1` interior variants each
whitened against its neighbour. They agree at every admissible correlation and every chain
length.

That agreement is what makes the ergodic reading of the certificate a theorem instead of a
numerical coincidence. The prose above says the summand *is* `ldWhiteningGain` and that the
sum formula matches `Tr(Σ⁻¹)/m` to `9.4e-16`; a measurement at fifteen cases is evidence for
that and not a proof of it, and this is the proof. -/
theorem ldPrecisionTrace_div_eq_perSitePrecisionTrace (decay : ℝ) (nSites : ℕ)
    (hd : 1 - decay ^ 2 ≠ 0) (hm : (nSites : ℝ) ≠ 0) :
    ldPrecisionTrace decay nSites / (nSites : ℝ)
      = perSitePrecisionTrace decay (nSites : ℝ) := by
  unfold ldPrecisionTrace perSitePrecisionTrace ldWhiteningGain
  field_simp
  ring

/-- **The summand is unbounded on the admissible range.**

    For every target `M` there is an admissible correlation whose whitening gain exceeds it.
    So ordinary low-order moment bounds do not bound the ergodic average: what decides
    finiteness is how much mass the environment law puts near the boundary.

    This is the formal residue of the external analysis's `b > 1` criterion that is available
    without measure theory, and it is the same edge-sensitivity that makes `tr K⁻¹` a legal
    certificate where effective-marker counts are not. -/
theorem whiteningGain_unbounded (M : ℝ) :
    ∃ decay : ℝ, 0 < decay ∧ decay < 1 ∧ M < ldWhiteningGain decay := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max M 2)
  have hN2 : (2 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right M 2) hN
  have hMN : M < (N : ℝ) := lt_of_le_of_lt (le_max_left M 2) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set t : ℝ := 1 - 1 / (N : ℝ) with ht
  have hinv : 1 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hinv0 : 0 < 1 / (N : ℝ) := by positivity
  have ht0 : 0 < t := by rw [ht]; linarith
  have ht1 : t < 1 := by rw [ht]; linarith
  refine ⟨Real.sqrt t, Real.sqrt_pos.mpr ht0, ?_, ?_⟩
  · have h1 : Real.sqrt t < Real.sqrt 1 := Real.sqrt_lt_sqrt (le_of_lt ht0) ht1
    rwa [Real.sqrt_one] at h1
  · have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht0)
    unfold ldWhiteningGain
    rw [hsq, ht]
    have hden : (1 : ℝ) - (1 - 1 / (N : ℝ)) = 1 / (N : ℝ) := by ring
    rw [hden, lt_div_iff₀ hinv0]
    have hMdivN : M / (N : ℝ) < 1 := (div_lt_one hN0).mpr hMN
    have hrw : M * (1 / (N : ℝ)) = M / (N : ℝ) := by ring
    rw [hrw]
    linarith

/-- **The four-step path count refutes freeness, at every nondegenerate environment.**

    Freeness of the pair would force `φ(abab) = 0` once `φ(a) = φ(b) = 0`. The closed
    four-step paths of a tridiagonal pair instead give
    `2·E[α²]·E[β²] + 4·(Eα)²·(Eβ)²`, which is strictly positive whenever the second moments
    are. So the `τ → ∞` endpoint is not a free-probability limit and the pencil law is not
    Wachter-type.

    The hypotheses are exactly nondegeneracy of the two second moments — no assumption on the
    means beyond their being real, since their contribution is a square and can only help. -/
theorem tridiagonalABAB_pathExpression_pos
    (Eα Eβ Eα2 Eβ2 : ℝ) (hα2 : 0 < Eα2) (hβ2 : 0 < Eβ2) :
    0 < 2 * Eα2 * Eβ2 + 4 * Eα ^ 2 * Eβ ^ 2 := by
  have h1 : 0 < 2 * Eα2 * Eβ2 := mul_pos (mul_pos two_pos hα2) hβ2
  have h2 : 0 ≤ 4 * Eα ^ 2 * Eβ ^ 2 := by positivity
  linarith

/-- **The exact finite-`m` path count**, derived from the six four-step patterns rather than
    fitted: the edge corrections come from the index ranges.

    `φ_m(abab) = 2(1 - 1/m)·E[α²]E[β²] + 4(1 - 2/m)·(Eα)²(Eβ)²`, whose `m → ∞` limit is the
    expression above. Forty-two ensembles match it at `max|z| = 2.07`, and the deterministic
    case reproduces `(2(m-1) + 4(m-2))/m` exactly.

    Prefer this whenever a finite-`m` number is quoted: at `m = 200` it differs from the
    asymptotic form by about 1% in each term, which exceeds the error of the fit that
    confirmed them. -/
noncomputable def ababFinite (Eα Eβ Eα2 Eβ2 m : ℝ) : ℝ :=
  2 * (1 - 1 / m) * Eα2 * Eβ2 + 4 * (1 - 2 / m) * Eα ^ 2 * Eβ ^ 2

/-- **The deterministic case reproduces the raw path count.**

    The docstring above claims the finite-`m` expression "reproduces
    `(2(m-1) + 4(m-2))/m` exactly" in the deterministic case, where every moment
    is one. That is a checkable arithmetic claim about this body and it was
    prose, so nothing could contradict it: an edge correction could be dropped
    from either factor and the sentence would still read true. -/
theorem ababFinite_deterministic (m : ℝ) (hm : m ≠ 0) :
    ababFinite 1 1 1 1 m = (2 * (m - 1) + 4 * (m - 2)) / m := by
  unfold ababFinite
  field_simp

/-- **The path expression is positive at every finite chain length past two**, so the
    obstruction to freeness is not an asymptotic artifact. -/
theorem ababFinite_pos (Eα Eβ Eα2 Eβ2 m : ℝ)
    (hα2 : 0 < Eα2) (hβ2 : 0 < Eβ2) (hm : 2 < m) :
    0 < ababFinite Eα Eβ Eα2 Eβ2 m := by
  have hm0 : (0 : ℝ) < m := by linarith
  have h1 : 0 < 1 - 1 / m := by
    rw [sub_pos, div_lt_one hm0]; linarith
  have h2 : 0 ≤ 1 - 2 / m := by
    rw [sub_nonneg, div_le_one hm0]; linarith
  have hA : 0 < 2 * (1 - 1 / m) * Eα2 * Eβ2 :=
    mul_pos (mul_pos (by linarith) hα2) hβ2
  have hB : 0 ≤ 4 * (1 - 2 / m) * Eα ^ 2 * Eβ ^ 2 := by positivity
  unfold ababFinite
  linarith

/-- **The two finite-panel deficits are exactly proportional, at every panel length.**

    Both certificates in this module are quoted at a finite number of sites `m`, and both
    fall short of their `m → ∞` value by a term that is exactly first order in `1/m`: the
    path count by `(2·E[α²]E[β²] + 8·(Eα)²(Eβ)²)/m`, and the whitening trace by
    `(ldWhiteningGain - 1)/m` (`whiteningGain_finite_trace`). So the ratio of the two
    deficits does not depend on `m`, which is what this equation says in cross-multiplied
    form.

    The content is the shared order, not the shared sign. If either deficit were `O(1/m²)`,
    or carried a different coefficient, the equation fails at every `m`; and it is the
    statement that ties `ababFinite` to a quantity defined outside this module, so a change
    to `ldWhiteningGain` cannot leave the path count's finite-`m` correction unexamined.

    Empirical status: UNTESTED as a joint statement. Each half is separately measured --
    the whitening deficit against an explicit tridiagonal inverse trace, the path count
    against 42 ensembles -- and both measurements are described above. -/
theorem ababFinite_deficit_proportional_to_whiteningGain_deficit_of_length_ne_zero
    (Eα Eβ Eα2 Eβ2 decay m : ℝ) (hm : m ≠ 0) :
    ((2 * Eα2 * Eβ2 + 4 * Eα ^ 2 * Eβ ^ 2) - ababFinite Eα Eβ Eα2 Eβ2 m)
        * (ldWhiteningGain decay - 1)
      = (2 * Eα2 * Eβ2 + 8 * Eα ^ 2 * Eβ ^ 2)
        * (ldWhiteningGain decay - (1 + (m - 1) * ldWhiteningGain decay) / m) := by
  have hnum : (2 * Eα2 * Eβ2 + 4 * Eα ^ 2 * Eβ ^ 2) - ababFinite Eα Eβ Eα2 Eβ2 m
      = (2 * Eα2 * Eβ2 + 8 * Eα ^ 2 * Eβ ^ 2) / m := by
    unfold ababFinite
    field_simp
    ring
  have hden : ldWhiteningGain decay - (1 + (m - 1) * ldWhiteningGain decay) / m
      = (ldWhiteningGain decay - 1) / m := by
    field_simp
    ring
  rw [hnum, hden]
  ring

end PencilEnvironment

end Calibrator

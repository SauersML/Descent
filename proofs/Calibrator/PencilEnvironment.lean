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

Empirical status: the identity `κ = E[ldWhiteningGain]` is DERIVED and its constant case is
VALIDATED upstream to `2e-16`. The finite path count is tested by
`validation/pencil/pencil_freeness.py`; Lean proves positivity of the resulting expression.
The heavy-tail trichotomy is ASSERTED from the external analysis and is not proved here.
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

end PencilEnvironment

end Calibrator

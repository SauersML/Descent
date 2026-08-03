import Calibrator.CountingInvariantBlindness
import Calibrator.PCCorrectability.ImitationCapacity

namespace Calibrator

open Calibrator.CountingInvariantBlindness

/-!
# The `m_eff` prohibition as an instance of counting-invariant blindness

`Calibrator.CountingInvariantBlindness` states the general phenomenon; this module supplies
the instance that makes it a dependency rather than a parallel statement. Delete the
general module and this one stops compiling.

## What is gained by routing the prohibition through the general theorem

`ImitationCapacity.certificate_not_momentContinuous` proves `False` from the *equality* of a
moment-continuous functional with the inverse-trace certificate. That is the sharpest form
of a qualitative statement, and it is silent about a functional that merely approximates the
certificate — which is what an effective-marker count is actually used as.

`lipschitz_predictor_error_ge` gives the quantitative form instead: **every** Lipschitz
function of the moments, whether or not it claims to equal the certificate, is off by at
least `(n − L) / (2(n+1))` at one of the two spectra, where `L` is its own Lipschitz
constant. Nothing is assumed about the functional's intent. So the result below is strictly
stronger than "no such functional equals the certificate": no such functional comes within
that error of it, and the bound degrades gracefully in `L` rather than collapsing to a
contradiction.

## The metric

Continuity of an effective-marker count is continuity in the *moment* metric, so the
invariant here is a spectrum's sequence of normalized moments and the distance is the
largest disagreement among the moments the functional consults. That is `momentDist`, a
finite supremum over `Finset.range (o+1)`.

Empirical status: UNTESTED here. The underlying witness is SIMULATED — see
`proofs/validation/meff_prohibition/`.
-/

noncomputable section

/-- The distance between two moment sequences, up to order `o`: the largest disagreement
    among the moments a functional of order `o` consults. -/
def momentDist (o : ℕ) (mu nu : ℕ → ℝ) : ℝ :=
  (Finset.range (o + 1)).sup' (by simp) fun p => |mu p - nu p|

theorem momentDist_nonneg (o : ℕ) (mu nu : ℕ → ℝ) : 0 ≤ momentDist o mu nu := by
  unfold momentDist
  refine Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.succ_pos o)) ?_
  exact abs_nonneg _

theorem momentDist_self (o : ℕ) (mu : ℕ → ℝ) : momentDist o mu mu = 0 := by
  unfold momentDist
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro p _
    simp
  · refine Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.succ_pos o)) ?_
    simp

/-- Each individual moment disagreement is bounded by the distance. -/
theorem abs_moment_sub_le_momentDist (o : ℕ) (mu nu : ℕ → ℝ) {p : ℕ} (hp : p ≤ o) :
    |mu p - nu p| ≤ momentDist o mu nu := by
  unfold momentDist
  exact Finset.le_sup'_of_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hp)) (le_refl _)

/-- The moment sequence of a spectrum, as the counting invariant. -/
def momentInvariant (m : ℕ) (lam : ℕ → ℝ) : ℕ → ℝ := fun p => normalizedMoment m lam p

/-- **The `m_eff` witness, as an approximate blindness witness.**

    Two spectra on `n + n²` markers whose moments agree to within `1/(n+1)` and whose
    inverse-trace certificates differ by exactly `n/(n+1)`. Both bounds are theorems in
    `ImitationCapacity`; this packages them into the general structure. -/
def meffApproxWitness (n o : ℕ) (hn : 0 < n) : ApproxWitness (ℕ → ℝ) (ℕ → ℝ) where
  count := momentInvariant (meffSize n)
  dist := momentDist o
  rate := inverseTraceCertificate (meffSize n)
  left := meffPerturbed n
  right := meffFlat n
  countGap := 1 / ((n : ℝ) + 1)
  count_close := by
    refine Finset.sup'_le _ _ ?_
    intro p _
    simpa [momentInvariant] using meff_moment_gap_le n p hn
  rateGap := (n : ℝ) / ((n : ℝ) + 1)
  rate_sep := by
    rw [meff_certificate_gap n hn]
    exact le_abs_self _

/-- **Every Lipschitz function of the moments misses the certificate.**

    Not merely "no such function equals it": at one of the two spectra the error is at least
    `(n − L)/(2(n+1))`, where `L` is the function's own Lipschitz constant in the moment
    metric. Once the marker count exceeds the modulus the bound is positive, and it rises to
    `1/2` as `n` grows.

    This is `ImitationCapacity.certificate_not_momentContinuous` with the equality hypothesis
    removed and a number put in its place. The biological reading is unchanged and now
    quantitative: an effective-marker count — Cheverud–Nyholt, Li–Ji, or any other
    moment-continuous summary — does not merely fail to *be* a detection threshold, it fails
    to *approximate* one, by an amount that does not shrink as the panel grows. -/
theorem meff_lipschitz_predictor_error_ge (n o : ℕ) (hn : 0 < n)
    (f : (ℕ → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ mu nu : ℕ → ℝ, |f mu - f nu| ≤ L * momentDist o mu nu) :
    ((n : ℝ) / ((n : ℝ) + 1) - L * (1 / ((n : ℝ) + 1))) / 2
      ≤ max |f (momentInvariant (meffSize n) (meffPerturbed n)) -
              inverseTraceCertificate (meffSize n) (meffPerturbed n)|
            |f (momentInvariant (meffSize n) (meffFlat n)) -
              inverseTraceCertificate (meffSize n) (meffFlat n)| := by
  have h := lipschitz_predictor_error_ge (meffApproxWitness n o hn) f L hL hf
  simpa [meffApproxWitness] using h

/-- The error floor is positive as soon as the marker count exceeds the modulus of
    continuity — the same crossing that drives the qualitative prohibition, now as a
    threshold on a number a practitioner has. -/
theorem meff_error_floor_pos (n : ℕ) (L : ℝ) (hn : 0 < n) (hL : L < (n : ℝ)) :
    0 < ((n : ℝ) / ((n : ℝ) + 1) - L * (1 / ((n : ℝ) + 1))) / 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  rw [div_pos_iff]
  left
  constructor
  · rw [sub_pos, mul_one_div, div_lt_div_iff₀ hn1 hn1]
    nlinarith
  · norm_num

end

end Calibrator

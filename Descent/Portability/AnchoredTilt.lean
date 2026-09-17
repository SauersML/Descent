/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarginalAnchor
import Descent.Foundations.TransportIdentities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

assert_below Descent.Decision Descent.Program

/-!
# Tilting a calibrated base by the residual features: the proper-loss view

`ResidualGeneticRepair` measures what a linear read of the residual features removes
from squared risk.  A fitted binary model is trained on a proper loss, not on squared
error, so the design also needs the canonical statement: at a base probability
`p₀ = σ(η₀)` whose probabilities are orthogonal to the residual read, the derivative of
population log loss along the logistic tilt `σ(η₀ + t·wᵀr)` at `t = 0` is `−wᵀc_r`,
with `c_r = E_p[r y]` the same residual cross-moment.  A nonzero cross-moment is
therefore a genuine descent direction of the proper loss, not a squared-error artefact.

Its companion is about the anchor.  When the tilt is marginally anchored the intercept
moves too, `σ(η₀ + a(t) + t·wᵀr)` with `a(0) = 0`; at a base calibrated in the large,
`E_p[σ(η₀)] = E_p[y]`, that motion contributes nothing at first order, whatever `a'(0)`
is.  So the anchor lets the predictor shape be learned against the proper loss while the
baseline channel is stationary -- the loss-side face of
`MarginalAnchor.crossInformation_baseline_shape_zero`.

Both are finite-sum derivatives on a declared law, with the outcome `y` any real
function of the predictor value (a `{0,1}` outcome or a conditional probability).

## Empirical status

None.  These are derivatives of a finite sum; nothing here names a cohort.
-/

namespace Descent.Portability.AnchoredTilt

open Filter Topology MarginalAnchor

noncomputable section

variable {V : Type*} [Fintype V]
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Bernoulli log loss of probability `p` against outcome `y`. -/
def logLoss (y p : ℝ) : ℝ := -(y * Real.log p + (1 - y) * Real.log (1 - p))

/-- **The canonical score.**  `d/dη ℓ(y, σ(η)) = σ(η) − y`. -/
theorem hasDerivAt_logLoss_sigmoid (y η : ℝ) :
    HasDerivAt (fun η ↦ logLoss y (Real.sigmoid η)) (Real.sigmoid η - y) η := by
  have hs := Real.hasDerivAt_sigmoid η
  have hpos := Real.sigmoid_pos η
  have hlt := Real.sigmoid_lt_one η
  have hne : (1 - Real.sigmoid η) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x ↦ Real.log (Real.sigmoid x))
      (Real.sigmoid η * (1 - Real.sigmoid η) / Real.sigmoid η) η := hs.log hpos.ne'
  have h2 : HasDerivAt (fun x ↦ Real.log (1 - Real.sigmoid x))
      ((0 - Real.sigmoid η * (1 - Real.sigmoid η)) / (1 - Real.sigmoid η)) η :=
    ((hasDerivAt_const η (1 : ℝ)).sub hs).log hne
  have h := ((h1.const_mul y).add (h2.const_mul (1 - y))).neg
  convert h using 1
  field_simp
  ring

/-- Population log loss of the tilted model `σ(η₀ + t·g)` under the declared law. -/
def tiltedLogLoss (p : FiniteReportLaw V) (y η₀ g : V → ℝ) (t : ℝ) : ℝ :=
  ∑ v, p.mass v * logLoss (y v) (Real.sigmoid (η₀ v + t * g v))

theorem hasDerivAt_tiltedLogLoss (p : FiniteReportLaw V) (y η₀ g : V → ℝ) (t : ℝ) :
    HasDerivAt (tiltedLogLoss p y η₀ g)
      (∑ v, p.mass v * ((Real.sigmoid (η₀ v + t * g v) - y v) * g v)) t := by
  have hterm : ∀ v ∈ (Finset.univ : Finset V),
      HasDerivAt (fun t ↦ p.mass v * logLoss (y v) (Real.sigmoid (η₀ v + t * g v)))
        (p.mass v * ((Real.sigmoid (η₀ v + t * g v) - y v) * g v)) t := by
    intro v _
    have hin : HasDerivAt (fun t ↦ η₀ v + t * g v) (g v) t := by
      simpa using ((hasDerivAt_id t).mul_const (g v)).const_add (η₀ v)
    exact ((hasDerivAt_logLoss_sigmoid (y v) (η₀ v + t * g v)).comp t hin).const_mul (p.mass v)
  have hderiv := HasDerivAt.sum hterm
  convert hderiv using 1
  funext s
  simp [tiltedLogLoss, Finset.sum_apply]

/-- The residual cross-moment `c_r = E_p[r y]` on the declared law. -/
def residualCrossMoment (p : FiniteReportLaw V) (r : V → J → ℝ) (y : V → ℝ) : J → ℝ :=
  fun i ↦ ∑ v, p.mass v * (r v i * y v)

omit [DecidableEq J] in
/-- **The residual cross-moment is a proper-loss descent direction.**  When the base
probabilities `σ(η₀)` are orthogonal to every residual feature, the derivative of
population log loss along the tilt `wᵀr` at zero tilt is `−wᵀc_r`. -/
theorem tiltedLogLoss_deriv_zero (p : FiniteReportLaw V) (y η₀ : V → ℝ) (r : V → J → ℝ)
    (w : J → ℝ) (horth : ∀ i, ∑ v, p.mass v * (r v i * Real.sigmoid (η₀ v)) = 0) :
    HasDerivAt (tiltedLogLoss p y η₀ (fun v ↦ Foundations.dot w (r v)))
      (-(Foundations.dot w (residualCrossMoment p r y))) 0 := by
  have h := hasDerivAt_tiltedLogLoss p y η₀ (fun v ↦ Foundations.dot w (r v)) 0
  convert h using 1
  simp only [zero_mul, add_zero]
  unfold Foundations.dot Descent.Core.innerSum residualCrossMoment
  have hpt : ∀ v, p.mass v * ((Real.sigmoid (η₀ v) - y v) * ∑ i, w i * r v i)
      = ∑ i, (w i * (p.mass v * (r v i * Real.sigmoid (η₀ v)))
          - w i * (p.mass v * (r v i * y v))) := by
    intro v
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [Finset.sum_congr rfl fun v _ ↦ hpt v, Finset.sum_comm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, horth, mul_zero, zero_sub,
    Finset.sum_neg_distrib]

/-- Population log loss of the anchored tilt `σ(η₀ + a(t) + t·g)`: the intercept moves
with the tilt. -/
def anchoredTiltLogLoss (p : FiniteReportLaw V) (y η₀ g : V → ℝ) (a : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  ∑ v, p.mass v * logLoss (y v) (Real.sigmoid (η₀ v + a t + t * g v))

/-- **The anchor's motion is loss-stationary at a calibrated base.**  If the base is
calibrated in the large, `E_p[σ(η₀)] = E_p[y]`, and the intercept path starts at zero,
then however the anchor moves the intercept, the derivative of the anchored tilt's
log loss at zero tilt is the same as the unanchored one. -/
theorem anchoredTiltLogLoss_deriv_zero (p : FiniteReportLaw V) (y η₀ g : V → ℝ)
    (a : ℝ → ℝ) {a' : ℝ} (ha : HasDerivAt a a' 0) (ha0 : a 0 = 0)
    (hcal : ∑ v, p.mass v * Real.sigmoid (η₀ v) = ∑ v, p.mass v * y v) :
    HasDerivAt (anchoredTiltLogLoss p y η₀ g a)
      (∑ v, p.mass v * ((Real.sigmoid (η₀ v) - y v) * g v)) 0 := by
  have hterm : ∀ v ∈ (Finset.univ : Finset V),
      HasDerivAt (fun t ↦ p.mass v * logLoss (y v) (Real.sigmoid (η₀ v + a t + t * g v)))
        (p.mass v * ((Real.sigmoid (η₀ v) - y v) * (a' + g v))) 0 := by
    intro v _
    have hin : HasDerivAt (fun t ↦ η₀ v + a t + t * g v) (a' + g v) 0 := by
      have h1 : HasDerivAt (fun t ↦ η₀ v + a t) a' 0 := ha.const_add (η₀ v)
      have h2 : HasDerivAt (fun t : ℝ ↦ t * g v) (g v) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const (g v)
      exact h1.add h2
    have hval : η₀ v + a 0 + 0 * g v = η₀ v := by rw [ha0]; ring
    have hcomp := (hasDerivAt_logLoss_sigmoid (y v) (η₀ v + a 0 + 0 * g v)).comp 0 hin
    rw [hval] at hcomp
    exact hcomp.const_mul (p.mass v)
  have hderiv := HasDerivAt.sum hterm
  have hfun : anchoredTiltLogLoss p y η₀ g a
      = ∑ v ∈ (Finset.univ : Finset V),
          fun t ↦ p.mass v * logLoss (y v) (Real.sigmoid (η₀ v + a t + t * g v)) := by
    funext s
    simp [anchoredTiltLogLoss, Finset.sum_apply]
  rw [hfun]
  convert hderiv using 1
  have hsplit : ∑ v, p.mass v * ((Real.sigmoid (η₀ v) - y v) * (a' + g v))
      = a' * (∑ v, p.mass v * Real.sigmoid (η₀ v) - ∑ v, p.mass v * y v)
        + ∑ v, p.mass v * ((Real.sigmoid (η₀ v) - y v) * g v) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  rw [hsplit, hcal, sub_self, mul_zero, zero_add]

end

end Descent.Portability.AnchoredTilt

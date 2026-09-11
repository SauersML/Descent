/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricResponseEllipsoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

assert_below Descent.Decision Descent.Program

/-!
# Information-preserving paths and explicit metric influence functions

TQ Section 5.1 and Proposition 5.1 on a finite report space. `perturbedLaw` is
the path `P (1 + ε f)` of equation (5.1). `perturbed_preserves_constraint` is the
manuscript's exactness claim: a retained feature orthogonal to the direction has
its expectation preserved for every `ε`, not only to first order, and
`perturbed_total_mass` is the same statement for normalisation.
`perturbed_positive` is the manuscript's realisability remark: the path consists
of genuine positive probability laws for `ε ^ 2` below the smallest atom, which
is `|ε| < sqrt p_min`. `mse_influence` is equation (5.3). `ratio_influence` is the
single quotient rule behind equations (5.5) and (5.6), specialised to
`precision_influence`, `recall_influence` and `f1_influence`. The geometry these
feed is `Descent.Portability.MetricResponseEllipsoid`, whose `wInner` is the
inner product used throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MetricInfluenceFunctions

open Foundations MetricResponseEllipsoid

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- Expectation of an observable against an arbitrary finite weight vector. -/
def lawExp (Q h : Ω → ℝ) : ℝ := ∑ ω, Q ω * h ω

/-- The perturbed law `P (1 + ε f)` of TQ equation (5.1). -/
def perturbedLaw (P f : Ω → ℝ) (ε : ℝ) : Ω → ℝ := fun ω ↦ P ω * (1 + ε * f ω)

omit [Fintype Ω] in
/-- The path passes through the base law at `ε = 0`. -/
theorem perturbedLaw_zero (P f : Ω → ℝ) : perturbedLaw P f 0 = P := by
  funext ω
  simp [perturbedLaw]

/-- Every expectation along the path is affine in the path parameter, with slope
the inner product of the observable with the direction. -/
theorem lawExp_perturbed (P f h : Ω → ℝ) (ε : ℝ) :
    lawExp (perturbedLaw P f ε) h = lawExp P h + ε * wInner P h f := by
  simp only [lawExp, perturbedLaw, wInner]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- **TQ Section 5.1, exactness.** A retained feature orthogonal to the direction
has its expectation preserved for every `ε`, not merely to first order. -/
theorem perturbed_preserves_constraint (P f a : Ω → ℝ) (ha : wInner P a f = 0)
    (ε : ℝ) : lawExp (perturbedLaw P f ε) a = lawExp P a := by
  rw [lawExp_perturbed, ha, mul_zero, add_zero]

/-- **TQ Section 5.1, normalisation.** A direction orthogonal to the constant
function keeps total mass one along the whole path. -/
theorem perturbed_total_mass (P f : Ω → ℝ) (hsum : ∑ ω, P ω = 1)
    (hf : wInner P (fun _ ↦ (1 : ℝ)) f = 0) (ε : ℝ) :
    ∑ ω, perturbedLaw P f ε ω = 1 := by
  have hone : ∀ Q : Ω → ℝ, lawExp Q (fun _ ↦ (1 : ℝ)) = ∑ ω, Q ω := by
    intro Q
    simp [lawExp]
  rw [← hone, perturbed_preserves_constraint P f (fun _ ↦ (1 : ℝ)) hf, hone, hsum]

/-- **TQ Section 5.1, realisability.** If every atom of the base law has mass at
least `pmin` and the direction has norm at most one, then the whole path consists
of strictly positive laws whenever `ε ^ 2 < pmin`, which is `|ε| < sqrt pmin`.
These are genuine probability laws, not formal signed measures. -/
theorem perturbed_positive (P f : Ω → ℝ) (pmin : ℝ) (hpmin : 0 < pmin)
    (hP : ∀ ω, pmin ≤ P ω) (hnorm : wInner P f f ≤ 1) (ε : ℝ) (heps : ε ^ 2 < pmin)
    (ω : Ω) : 0 < perturbedLaw P f ε ω := by
  have hPpos : 0 < P ω := lt_of_lt_of_le hpmin (hP ω)
  have hterm : P ω * f ω * f ω ≤ wInner P f f :=
    Finset.single_le_sum (f := fun ν ↦ P ν * f ν * f ν)
      (fun ν _ ↦ by
        have hν : (0 : ℝ) ≤ P ν := le_trans hpmin.le (hP ν)
        nlinarith [sq_nonneg (f ν)])
      (Finset.mem_univ ω)
  have hbound : pmin * f ω ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (f ω), hP ω, hterm, hnorm]
  have hlin : 0 < 1 + ε * f ω := by
    by_cases hf0 : f ω = 0
    · rw [hf0, mul_zero]
      norm_num
    · have hfsq : 0 < f ω ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hf0))
      have h1 : (ε * f ω) ^ 2 < 1 := by nlinarith
      nlinarith [sq_nonneg (1 + ε * f ω)]
  exact mul_pos hPpos hlin

/-- Three-term linear expansion of the inner product in the left slot. -/
theorem wInner_three_term (P f A B C : Ω → ℝ) (p q r : ℝ) :
    wInner P (fun ω ↦ p * A ω - q * B ω - r * C ω) f =
      p * wInner P A f - q * wInner P B f - r * wInner P C f := by
  rw [wInner_sub_left, wInner_sub_left, wInner_smul_left, wInner_smul_left,
    wInner_smul_left]

/-- Every expectation has the observable itself as a derivative direction. -/
theorem hasDerivAt_perturbed_exp (P f h : Ω → ℝ) :
    HasDerivAt (fun ε ↦ lawExp (perturbedLaw P f ε) h) (wInner P h f) 0 := by
  have hfun : (fun ε ↦ lawExp (perturbedLaw P f ε) h) =
      fun ε ↦ lawExp P h + ε * wInner P h f := funext (lawExp_perturbed P f h)
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (wInner P h f)).const_add (lawExp P h)

/-- **TQ equation (5.3).** The centred observable is a valid influence function
for its own expectation, the mean-squared error being one such expectation. -/
theorem mse_influence (P f L : Ω → ℝ) (hf : wInner P (fun _ ↦ (1 : ℝ)) f = 0) :
    HasDerivAt (fun ε ↦ lawExp (perturbedLaw P f ε) L)
      (wInner P (fun ω ↦ L ω - lawExp P L) f) 0 := by
  have h1 : (fun ω ↦ L ω - lawExp P L) =
      fun ω ↦ L ω - lawExp P L * (fun _ : Ω ↦ (1 : ℝ)) ω := by
    funext ω
    ring
  rw [h1, wInner_sub_left, wInner_smul_left, hf, mul_zero, sub_zero]
  exact hasDerivAt_perturbed_exp P f L

/-- **The quotient rule behind TQ (5.5) and (5.6).** For a metric that is a ratio
of two expectations, a centred influence function is the numerator observable
minus the metric times the denominator observable, divided by the denominator. -/
theorem ratio_influence (P f u v : Ω → ℝ) (hv : lawExp P v ≠ 0) :
    HasDerivAt
      (fun ε ↦ lawExp (perturbedLaw P f ε) u / lawExp (perturbedLaw P f ε) v)
      (wInner P
        (fun ω ↦ (u ω - lawExp P u / lawExp P v * v ω) / lawExp P v) f) 0 := by
  have hz := perturbedLaw_zero P f
  have hu := hasDerivAt_perturbed_exp P f u
  have hvd := hasDerivAt_perturbed_exp P f v
  have hdiv := hu.div hvd (by rw [hz]; exact hv)
  rw [hz] at hdiv
  have hpsi : (fun ω ↦ (u ω - lawExp P u / lawExp P v * v ω) / lawExp P v) =
      fun ω ↦ (lawExp P v)⁻¹ * u ω -
        (lawExp P u / lawExp P v * (lawExp P v)⁻¹) * v ω -
        (0 : ℝ) * u ω := by
    funext ω
    ring
  rw [hpsi, wInner_three_term]
  have hval : (lawExp P v)⁻¹ * wInner P u f -
      lawExp P u / lawExp P v * (lawExp P v)⁻¹ * wInner P v f - 0 * wInner P u f =
      (wInner P u f * lawExp P v - lawExp P u * wInner P v f) / lawExp P v ^ 2 := by
    field_simp
    ring
  rw [hval]
  exact hdiv

/-- **TQ equation (5.5), precision.** With `A` the decision indicator and `Y` the
outcome, precision is the ratio of the true-positive mass to the
predicted-positive mass, and its centred influence function is `A (Y - p) / s`. -/
theorem precision_influence (P f A Y : Ω → ℝ) (hs : lawExp P A ≠ 0) :
    HasDerivAt
      (fun ε ↦ lawExp (perturbedLaw P f ε) (fun ω ↦ A ω * Y ω) /
        lawExp (perturbedLaw P f ε) A)
      (wInner P
        (fun ω ↦ A ω *
          (Y ω - lawExp P (fun ν ↦ A ν * Y ν) / lawExp P A) / lawExp P A) f) 0 := by
  have h := ratio_influence P f (fun ω ↦ A ω * Y ω) A hs
  have hfun : (fun ω ↦ (A ω * Y ω -
        lawExp P (fun ν ↦ A ν * Y ν) / lawExp P A * A ω) / lawExp P A) =
      fun ω ↦ A ω *
        (Y ω - lawExp P (fun ν ↦ A ν * Y ν) / lawExp P A) / lawExp P A := by
    funext ω
    ring
  rwa [hfun] at h

/-- **TQ equation (5.5), recall.** Recall is the ratio of the true-positive mass
to the prevalence, and its centred influence function is `Y (A - r) / pi`. -/
theorem recall_influence (P f A Y : Ω → ℝ) (hpi : lawExp P Y ≠ 0) :
    HasDerivAt
      (fun ε ↦ lawExp (perturbedLaw P f ε) (fun ω ↦ A ω * Y ω) /
        lawExp (perturbedLaw P f ε) Y)
      (wInner P
        (fun ω ↦ Y ω *
          (A ω - lawExp P (fun ν ↦ A ν * Y ν) / lawExp P Y) / lawExp P Y) f) 0 := by
  have h := ratio_influence P f (fun ω ↦ A ω * Y ω) Y hpi
  have hfun : (fun ω ↦ (A ω * Y ω -
        lawExp P (fun ν ↦ A ν * Y ν) / lawExp P Y * Y ω) / lawExp P Y) =
      fun ω ↦ Y ω *
        (A ω - lawExp P (fun ν ↦ A ν * Y ν) / lawExp P Y) / lawExp P Y := by
    funext ω
    ring
  rwa [hfun] at h

/-- **TQ equation (5.6).** The `F1` score is twice the true-positive mass over
the sum of the predicted-positive mass and the prevalence, and its centred
influence function is `(2 A Y - F1 (A + Y)) / (s + pi)`. -/
theorem f1_influence (P f A Y : Ω → ℝ)
    (hsum : lawExp P (fun ν ↦ A ν + Y ν) ≠ 0) :
    HasDerivAt
      (fun ε ↦ lawExp (perturbedLaw P f ε) (fun ω ↦ 2 * (A ω * Y ω)) /
        lawExp (perturbedLaw P f ε) (fun ω ↦ A ω + Y ω))
      (wInner P
        (fun ω ↦ (2 * (A ω * Y ω) -
          lawExp P (fun ν ↦ 2 * (A ν * Y ν)) / lawExp P (fun ν ↦ A ν + Y ν) *
            (A ω + Y ω)) / lawExp P (fun ν ↦ A ν + Y ν)) f) 0 :=
  ratio_influence P f (fun ω ↦ 2 * (A ω * Y ω)) (fun ω ↦ A ω + Y ω) hsum

/-- Four-term linear expansion of the inner product in the left slot. -/
theorem wInner_four_term (P f A B C D : Ω → ℝ) (p q r t : ℝ) :
    wInner P (fun ω ↦ p * A ω - q * B ω - r * C ω + t * D ω) f =
      p * wInner P A f - q * wInner P B f - r * wInner P C f + t * wInner P D f := by
  rw [wInner_add_left, wInner_sub_left, wInner_sub_left, wInner_smul_left,
    wInner_smul_left, wInner_smul_left, wInner_smul_left]

/-- The covariance of two observables under an arbitrary finite weight vector. -/
def lawCov (Q S Y : Ω → ℝ) : ℝ :=
  lawExp Q (fun ω ↦ S ω * Y ω) - lawExp Q S * lawExp Q Y

/-- **The covariance influence function.** Differentiating the centred
covariance along an information-preserving path gives the centred product, which
is the intermediate influence function the manuscript's proof of (5.4) uses. -/
theorem lawCov_influence (P f S Y : Ω → ℝ)
    (hf : wInner P (fun _ ↦ (1 : ℝ)) f = 0) :
    HasDerivAt (fun ε ↦ lawCov (perturbedLaw P f ε) S Y)
      (wInner P (fun ω ↦ (S ω - lawExp P S) * (Y ω - lawExp P Y)) f) 0 := by
  have hz := perturbedLaw_zero P f
  have hSY := hasDerivAt_perturbed_exp P f (fun ω ↦ S ω * Y ω)
  have hS := hasDerivAt_perturbed_exp P f S
  have hY := hasDerivAt_perturbed_exp P f Y
  have hsub := hSY.sub (hS.mul hY)
  rw [hz] at hsub
  have hpsi : (fun ω ↦ (S ω - lawExp P S) * (Y ω - lawExp P Y)) =
      fun ω ↦ (1 : ℝ) * (S ω * Y ω) - lawExp P Y * S ω - lawExp P S * Y ω +
        lawExp P S * lawExp P Y * (1 : ℝ) := by
    funext ω
    ring
  rw [hpsi, wInner_four_term, hf]
  have hval : (1 : ℝ) * wInner P (fun ω ↦ S ω * Y ω) f -
      lawExp P Y * wInner P S f - lawExp P S * wInner P Y f +
        lawExp P S * lawExp P Y * 0 =
      wInner P (fun ω ↦ S ω * Y ω) f -
        (wInner P S f * lawExp P Y + lawExp P S * wInner P Y f) := by
    ring
  rw [hval]
  exact hsub

/-- **The variance influence function.** The squared centred observable is a
valid influence function for the variance. -/
theorem lawVar_influence (P f S : Ω → ℝ) (hf : wInner P (fun _ ↦ (1 : ℝ)) f = 0) :
    HasDerivAt (fun ε ↦ lawCov (perturbedLaw P f ε) S S)
      (wInner P (fun ω ↦ (S ω - lawExp P S) ^ 2) f) 0 := by
  have h := lawCov_influence P f S S hf
  have hpsi : (fun ω ↦ (S ω - lawExp P S) * (S ω - lawExp P S)) =
      fun ω ↦ (S ω - lawExp P S) ^ 2 := by
    funext ω
    ring
  rwa [hpsi] at h

/-- **TQ equation (5.4).** The log squared correlation is `2 log |c| - log u -
log v`, and its centred influence function is the manuscript's boxed formula.
The hypotheses are exactly the manuscript's nondegeneracy conditions: a nonzero
covariance and two nonzero variances. -/
theorem log_squared_correlation_influence (P f S Y : Ω → ℝ)
    (hf : wInner P (fun _ ↦ (1 : ℝ)) f = 0) (hc : lawCov P S Y ≠ 0)
    (hu : lawCov P S S ≠ 0) (hv : lawCov P Y Y ≠ 0) :
    HasDerivAt
      (fun ε ↦ 2 * Real.log (lawCov (perturbedLaw P f ε) S Y) -
        Real.log (lawCov (perturbedLaw P f ε) S S) -
        Real.log (lawCov (perturbedLaw P f ε) Y Y))
      (wInner P
        (fun ω ↦ 2 * ((S ω - lawExp P S) * (Y ω - lawExp P Y)) / lawCov P S Y -
          (S ω - lawExp P S) ^ 2 / lawCov P S S -
          (Y ω - lawExp P Y) ^ 2 / lawCov P Y Y) f) 0 := by
  have hz := perturbedLaw_zero P f
  have hcov := lawCov_influence P f S Y hf
  have hvS := lawVar_influence P f S hf
  have hvY := lawVar_influence P f Y hf
  have hlogc := hcov.log (by rw [hz]; exact hc)
  have hlogu := hvS.log (by rw [hz]; exact hu)
  have hlogv := hvY.log (by rw [hz]; exact hv)
  rw [hz] at hlogc hlogu hlogv
  have hchain := ((HasDerivAt.const_mul (2 : ℝ) hlogc).sub hlogu).sub hlogv
  have hpsi :
      (fun ω ↦ 2 * ((S ω - lawExp P S) * (Y ω - lawExp P Y)) / lawCov P S Y -
        (S ω - lawExp P S) ^ 2 / lawCov P S S -
        (Y ω - lawExp P Y) ^ 2 / lawCov P Y Y) =
      fun ω ↦ 2 / lawCov P S Y * ((S ω - lawExp P S) * (Y ω - lawExp P Y)) -
        (lawCov P S S)⁻¹ * (S ω - lawExp P S) ^ 2 -
        (lawCov P Y Y)⁻¹ * (Y ω - lawExp P Y) ^ 2 := by
    funext ω
    ring
  rw [hpsi, wInner_three_term]
  have hval : 2 / lawCov P S Y *
        wInner P (fun ω ↦ (S ω - lawExp P S) * (Y ω - lawExp P Y)) f -
      (lawCov P S S)⁻¹ * wInner P (fun ω ↦ (S ω - lawExp P S) ^ 2) f -
      (lawCov P Y Y)⁻¹ * wInner P (fun ω ↦ (Y ω - lawExp P Y) ^ 2) f =
      2 * (wInner P (fun ω ↦ (S ω - lawExp P S) * (Y ω - lawExp P Y)) f /
          lawCov P S Y) -
        wInner P (fun ω ↦ (S ω - lawExp P S) ^ 2) f / lawCov P S S -
        wInner P (fun ω ↦ (Y ω - lawExp P Y) ^ 2) f / lawCov P Y Y := by
    ring
  rw [hval]
  exact hchain

end

end Descent.Portability.MetricInfluenceFunctions

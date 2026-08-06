/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Duality
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Fixation probabilities: the harmonic functions of the forward generator

`Descent.Coalescent.Duality` gives the Wright-Fisher diffusion its generator and shows that
applying it to `xⁿ` reproduces the coalescent's death rates.  That is the neutral case.  This
file asks the other classical question of the forward model -- what is the chance an allele
now at frequency `x` eventually takes over? -- and answers it in the only way that makes the
answer a theorem rather than a quotation: a fixation probability is a function the generator
kills, with boundary values `0` and `1`.

Two cases, and the contrast between them is the whole of what selection does to a genealogy.

**Neutral.**  The generator is `L f = ½x(1-x)f''`, which kills every affine function.  So
`u(x) = x`: a neutral allele fixes with probability equal to its current frequency.
`neutralFixation_generator_eq_zero` is that, and it is the `n = 1` case of `Duality` -- the
first moment of the diffusion is conserved, which is the same statement.  Everything the
corpus says about drift being unbiased is this identity.

**Selected.**  Add a drift term: an allele with scaled selection coefficient `α = 4Nₑs` has
generator `L f = ½x(1-x)f'' + ½α x(1-x) f'`.  Then

  `u(x) = (1 - e^{-αx})/(1 - e^{-α})`,                                     Kimura (1962)

and `selectedFixation_generator_eq_zero` verifies it.  The verification is worth doing rather
than citing, because the identity that makes it work is exact and visible: both terms carry
the factor `x(1-x)·α e^{-αx}/(1-e^{-α})`, and what remains is `-α/2 + α/2`.  The diffusion
coefficient cancels entirely, which is why the answer does not depend on the population size
except through `α`.

## What the formula says, proved

`selectedFixation_half_gt_half`: a beneficial allele at frequency one half fixes with probability
strictly above one half.  The proof is the factorisation
`1 - e^{-α} = (1 - e^{-α/2})(1 + e^{-α/2})`, which collapses the whole expression to
`1/(1 + e^{-α/2})`, and that exceeds `½` exactly when `e^{-α/2} < 1`.

That is the sharpest statement available here without convexity machinery, and it is the one
that matters: selection biases fixation in its own direction at every strength, with no
threshold.  What it does NOT say is anything about how large the bias is at small `x`, which
is where Haldane's `2s` lives and where the sample sizes of real studies sit.

## Why it belongs in the coalescent group

A selected allele's genealogy is not Kingman's -- `Descent.Coalescent.Selection` carries the
ancestral selection graph's rates, and its point is that the branching-to-coalescence ratio
`σ/(k-1)` vanishes as the sample grows.  This file supplies the forward-time quantity that
ratio is about, and the boundary conditions that make the ASG's two parents resolve into one.

## Main results

- `neutralFixation_generator_eq_zero`: **`u(x) = x`**, the neutral answer.
- `selectedFixation`: Kimura's formula.
- `hasDerivAt_selectedFixation`, `hasDerivAt_selectedFixationDeriv`: its two derivatives,
  computed.
- `selectedFixation_generator_eq_zero`: **it is killed by the generator with drift**.
- `selectedFixation_zero`, `selectedFixation_one`: the boundary conditions.
- `selectedFixation_half_gt_half`: selection biases fixation, at every strength.
-/

namespace Coalescent

/-! ### Neutral: the generator kills affine functions -/

/-- The neutral fixation probability: an allele at frequency `x` fixes with probability `x`.

Empirical status: DERIVED.  It is the function the neutral generator annihilates with the
right boundary values, which `neutralFixation_generator_eq_zero` proves. -/
noncomputable def neutralFixation (x : ℝ) : ℝ := Descent.Core.identifiedWith x

/-- **`u(x) = x` is harmonic for the neutral diffusion.**  The second derivative of the
identity is zero, so `½x(1-x)u'' = 0` whatever `x` is -- the diffusion coefficient never
enters.  This is why drift is unbiased: it is the `n = 1` companion of
`Duality.duality_identity`, whose `n ≥ 2` cases are the coalescent's death rates. -/
theorem neutralFixation_generator_eq_zero (x : ℝ) :
    x * (1 - x) / 2 * deriv (deriv neutralFixation) x = 0 := by
  have h1 : deriv neutralFixation = fun _ : ℝ ↦ (1 : ℝ) := by
    funext y
    unfold neutralFixation Descent.Core.identifiedWith
    simp
  rw [h1]
  simp

@[simp] theorem neutralFixation_zero : neutralFixation 0 = 0 := rfl

@[simp] theorem neutralFixation_one : neutralFixation 1 = 1 := rfl

/-! ### Selected: Kimura's formula -/

/-- **Kimura (1962).**  The probability that an allele with scaled selection coefficient
`α = 4Nₑs`, currently at frequency `x`, eventually fixes.

Empirical status: DERIVED, given the model.  It is the solution of `L u = 0` with `u(0) = 0`
and `u(1) = 1` for the generator with a selective drift term, and
`selectedFixation_generator_eq_zero` is that verification.  What is ASSUMED is the diffusion
with drift `½α x(1-x)` -- genic selection, no dominance, constant size -- which is a model of
a population and not a consequence of one. -/
noncomputable def selectedFixation (α x : ℝ) : ℝ :=
  (1 - Real.exp (-(α * x))) / (1 - Real.exp (-α))

@[simp] theorem selectedFixation_zero (α : ℝ) : selectedFixation α 0 = 0 := by
  unfold selectedFixation
  simp

theorem selectedFixation_one {α : ℝ} (hα : α ≠ 0) : selectedFixation α 1 = 1 := by
  have hne : 1 - Real.exp (-α) ≠ 0 := by
    intro h
    have hexp : Real.exp (-α) = 1 := by linarith
    have hz : -α = 0 := (Real.exp_eq_one_iff (-α)).mp hexp
    exact hα (by linarith)
  unfold selectedFixation
  rw [mul_one, div_self hne]

/-- The first derivative of Kimura's formula, named so the generator identity can be stated
as algebra. -/
noncomputable def selectedFixationDeriv (α x : ℝ) : ℝ :=
  α * Real.exp (-(α * x)) / (1 - Real.exp (-α))

/-- The second derivative, likewise. -/
noncomputable def selectedFixationDeriv2 (α x : ℝ) : ℝ :=
  -(α ^ 2 * Real.exp (-(α * x)) / (1 - Real.exp (-α)))

/-- **The generator with selective drift kills Kimura's formula.**

  `½x(1-x)u'' + ½α x(1-x)u' = 0`.

Stated on the named derivative expressions, so that the mathematical content -- the exact
cancellation `-α/2 + α/2` after the common factor `x(1-x)αe^{-αx}/(1-e^{-α})` is pulled out
-- is an identity with no analysis in it.  `hasDerivAt_selectedFixation` and
`hasDerivAt_selectedFixationDeriv` supply the analysis separately. -/
theorem selectedFixation_generator_eq_zero (α x : ℝ) :
    x * (1 - x) / 2 * selectedFixationDeriv2 α x
      + α / 2 * (x * (1 - x)) * selectedFixationDeriv α x = 0 := by
  unfold selectedFixationDeriv selectedFixationDeriv2
  ring

/-- **The coefficient in the fixation equation is the pair coalescence rate.**  The factor
`x(1-x)` multiplying both `u''` and `u'` is `Duality.diffusionOnPow 0`, which
`Duality.duality_two` identifies with the `n = 2` duality term -- the rate at which two
lineages coalesce.

So the forward equation whose solution is a fixation probability and the backward rate at
which a sample of two finds its common ancestor are built from one quantity, and this states
it rather than leaving a reader to notice that two expressions coincide. -/
theorem fixationCoefficient_eq_duality (x : ℝ) : x * (1 - x) = diffusionOnPow 0 x :=
  (duality_two x).symm

/-- The generator identity written on that coefficient, so the dependence is in the statement
and not only in the prose. -/
theorem selectedFixation_generator_eq_zero_duality (α x : ℝ) :
    diffusionOnPow 0 x / 2 * selectedFixationDeriv2 α x
      + α / 2 * diffusionOnPow 0 x * selectedFixationDeriv α x = 0 := by
  rw [← fixationCoefficient_eq_duality]
  exact selectedFixation_generator_eq_zero α x

/-- The named first derivative is the derivative. -/
theorem hasDerivAt_selectedFixation (α x : ℝ) :
    HasDerivAt (selectedFixation α) (selectedFixationDeriv α x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -(α * y)) (-α) x := by
    simpa using ((hasDerivAt_id x).const_mul α).neg
  have h2 : HasDerivAt (fun y : ℝ ↦ Real.exp (-(α * y)))
      (Real.exp (-(α * x)) * -α) x := h1.exp
  have h3 : HasDerivAt (fun y : ℝ ↦ 1 - Real.exp (-(α * y)))
      (-(Real.exp (-(α * x)) * -α)) x := h2.const_sub 1
  have h4 := h3.div_const (1 - Real.exp (-α))
  have hval : -(Real.exp (-(α * x)) * -α) / (1 - Real.exp (-α))
      = selectedFixationDeriv α x := by
    unfold selectedFixationDeriv
    ring
  rwa [hval] at h4

/-- And the named second derivative is the derivative of the first. -/
theorem hasDerivAt_selectedFixationDeriv (α x : ℝ) :
    HasDerivAt (selectedFixationDeriv α) (selectedFixationDeriv2 α x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -(α * y)) (-α) x := by
    simpa using ((hasDerivAt_id x).const_mul α).neg
  have h2 : HasDerivAt (fun y : ℝ ↦ Real.exp (-(α * y)))
      (Real.exp (-(α * x)) * -α) x := h1.exp
  have h3 : HasDerivAt (fun y : ℝ ↦ α * Real.exp (-(α * y)))
      (α * (Real.exp (-(α * x)) * -α)) x := h2.const_mul α
  have h4 := h3.div_const (1 - Real.exp (-α))
  have hval : α * (Real.exp (-(α * x)) * -α) / (1 - Real.exp (-α))
      = selectedFixationDeriv2 α x := by
    unfold selectedFixationDeriv2
    ring
  rwa [hval] at h4

/-! ### Selection biases fixation, at every strength -/

/-- **A beneficial allele at frequency one half fixes with probability above one half.**

The proof is a factorisation: with `e = e^{-α/2}`, the denominator `1 - e^{-α}` is
`(1-e)(1+e)` and the numerator is `1-e`, so the whole expression is `1/(1+e)`.  That exceeds
`½` exactly when `e < 1`, which is exactly when `α > 0`.

No threshold, no approximation, and no dependence on the population size except through `α`
-- which is the substantive content of the diffusion approximation for selection, and the
reason `Nₑ s` rather than `s` is the quantity that matters. -/
theorem selectedFixation_half_gt_half {α : ℝ} (hα : 0 < α) :
    1 / 2 < selectedFixation α (1 / 2) := by
  have he0 : 0 < Real.exp (-(α / 2)) := Real.exp_pos _
  have he1 : Real.exp (-(α / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h1e : (0 : ℝ) < 1 + Real.exp (-(α / 2)) := by linarith
  have hne : (1 : ℝ) - Real.exp (-(α / 2)) ≠ 0 := ne_of_gt (by linarith)
  have harg : α * (1 / 2) = α / 2 := by ring
  have hsq : Real.exp (-α) = Real.exp (-(α / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hval : (1 - Real.exp (-(α / 2))) / (1 - Real.exp (-(α / 2)) ^ 2)
      = 1 / (1 + Real.exp (-(α / 2))) := by
    have hfac : (1 : ℝ) - Real.exp (-(α / 2)) ^ 2
        = (1 - Real.exp (-(α / 2))) * (1 + Real.exp (-(α / 2))) := by ring
    rw [hfac, div_eq_div_iff (mul_ne_zero hne (ne_of_gt h1e)) (ne_of_gt h1e)]
    ring
  unfold selectedFixation
  rw [harg, hsq, hval, div_lt_div_iff₀ (by norm_num) h1e]
  linarith

end Coalescent

end Descent

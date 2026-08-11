/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

/-!
# A law written as a product pins the product and neither factor

A recurring shape in this corpus is a law whose two parameters appear only multiplied
together: `m · σ²` in the stepping-stone `F_ST`, a rate against a timescale, a per-locus
effect against a locus count. The arithmetic consequence is always the same and it is
proved once here.

## The rule

`productRescaling` scales one factor and inversely scales the other. It fixes the product
(`productRescaling_fixes_product`), so any observation that reads the parameters only
through the product is invariant under it, and it moves each factor, so neither factor is
identified (`not_identifiedBy_firstFactor_of_product` and its second-factor twin). Meanwhile
the product itself is pinned whenever the report is injective
(`product_identifiedBy_of_injective`). `factorizedLaw_pins_product_only` is the three
statements together, which is the form worth quoting.

## Why the transitivity theorem is here

`exists_productRescaling_of_product_eq` says the rescalings act transitively on each level
set of the product: any two parameter pairs with the same product and nonzero first
coordinates are related by ONE rescaling. That is what upgrades the rule from "the product
is an invariant" to "the product is THE invariant" — nothing coarser is forced on the
observation and nothing finer is available to it. A per-law identification claim can
therefore be checked rather than asserted: name the combination, and either exhibit a
transformation moving everything else, or show there is none.

## The admissibility reading

A factorized law is admissible as a *law about its factors* only if each factor is
independently identifiable — by some other measurement, or by being held at a value fixed
outside the fit. Absent that, a fit reports the product, and quoting either factor from it
is quoting a number the data never constrained. `Counterexamples.dispersalSymmetry` is this
rule at `m · σ²`, and the regime it forces — hold `σ²` at an independently measured
dispersal scale while `m` varies — is what the rule demands in general.

## What this does not say

It does not say a product-form law is wrong, and it does not say the factors are
meaningless. It says exactly which function of them the observation sees. A law that never
quotes a factor on its own is untouched by any of this.
-/

/-- **The rescaling that fixes a product**: scale the first factor, inversely scale the
second. At `scale = 0` the second coordinate divides by zero and Mathlib returns `0`, so the
product is not preserved there; every statement below carries `scale ≠ 0`. -/
noncomputable def productRescaling (scale : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun parameter ↦ (scale * parameter.1, parameter.2 / scale)

/-- **The rescaling fixes the product.** This is the whole mechanism of the file. -/
theorem productRescaling_fixes_product (scale : ℝ) (hscale : scale ≠ 0) (parameter : ℝ × ℝ) :
    (productRescaling scale parameter).1 * (productRescaling scale parameter).2
      = parameter.1 * parameter.2 := by
  show scale * parameter.1 * (parameter.2 / scale) = parameter.1 * parameter.2
  field_simp

/-- **The rescalings act transitively on each level set of the product.** Any two parameter
pairs with the same product and nonzero first coordinates are related by one rescaling, so
the product is not merely an invariant of the family but its complete invariant: an
observation reading the product can distinguish nothing further, and one distinguishing
anything further does not read the product alone. -/
theorem exists_productRescaling_of_product_eq (first second : ℝ × ℝ)
    (hfirst : first.1 ≠ 0) (hsecond : second.1 ≠ 0)
    (hproduct : first.1 * first.2 = second.1 * second.2) :
    ∃ scale : ℝ, scale ≠ 0 ∧ productRescaling scale first = second := by
  refine ⟨second.1 / first.1, div_ne_zero hsecond hfirst, ?_⟩
  have hfirstCoordinate : second.1 / first.1 * first.1 = second.1 := by
    field_simp
  have hsecondCoordinate : first.2 / (second.1 / first.1) = second.2 := by
    rw [div_div_eq_mul_div, div_eq_iff hsecond]
    linarith [hproduct]
  exact Prod.ext hfirstCoordinate hsecondCoordinate

/-- **A product-form observation cannot see the rescaling, and the rescaling moves the
second factor.** The observation is given by the factorization hypothesis rather than by its
syntax, so a law only equal to a product form qualifies without being rewritten. -/
noncomputable def productSymmetrySecondFactor {Data : Type*}
    (observe : ℝ × ℝ → Data) (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (scale : ℝ) (hscale : scale ≠ 0) (hscaleNeOne : scale ≠ 1)
    (base : ℝ × ℝ) (hbase : base.2 ≠ 0) :
    ObservationalSymmetry observe (fun parameter ↦ parameter.2) where
  transform := productRescaling scale
  observation_invariant := by
    intro parameter
    simp only [hfactors, productRescaling_fixes_product scale hscale parameter]
  moved := base
  target_moved := by
    show base.2 / scale ≠ base.2
    intro hcontra
    have hequation : base.2 = base.2 * scale := (div_eq_iff hscale).mp hcontra
    have hzero : base.2 * (scale - 1) = 0 := by
      rw [mul_sub, mul_one, ← hequation, sub_self]
    rcases mul_eq_zero.mp hzero with hbaseZero | hscaleZero
    · exact hbase hbaseZero
    · exact hscaleNeOne (by linarith)

/-- The same rescaling against the first factor. -/
noncomputable def productSymmetryFirstFactor {Data : Type*}
    (observe : ℝ × ℝ → Data) (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (scale : ℝ) (hscale : scale ≠ 0) (hscaleNeOne : scale ≠ 1)
    (base : ℝ × ℝ) (hbase : base.1 ≠ 0) :
    ObservationalSymmetry observe (fun parameter ↦ parameter.1) where
  transform := productRescaling scale
  observation_invariant := by
    intro parameter
    simp only [hfactors, productRescaling_fixes_product scale hscale parameter]
  moved := base
  target_moved := by
    show scale * base.1 ≠ base.1
    intro hcontra
    have hzero : (scale - 1) * base.1 = 0 := by
      rw [sub_mul, one_mul, hcontra, sub_self]
    rcases mul_eq_zero.mp hzero with hscaleZero | hbaseZero
    · exact hscaleNeOne (by linarith)
    · exact hbase hbaseZero

/-- **The second factor is not identified by a product-form observation.** -/
theorem not_identifiedBy_secondFactor_of_product {Data : Type*} (observe : ℝ × ℝ → Data)
    (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (base : ℝ × ℝ) (hbase : base.2 ≠ 0) :
    ¬ Core.IdentifiedBy observe (fun parameter ↦ parameter.2) :=
  not_identifiedBy_of_observationalSymmetry
    (productSymmetrySecondFactor observe report hfactors 2 two_ne_zero (by norm_num) base hbase)

/-- **The first factor is not identified by a product-form observation.** -/
theorem not_identifiedBy_firstFactor_of_product {Data : Type*} (observe : ℝ × ℝ → Data)
    (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (base : ℝ × ℝ) (hbase : base.1 ≠ 0) :
    ¬ Core.IdentifiedBy observe (fun parameter ↦ parameter.1) :=
  not_identifiedBy_of_observationalSymmetry
    (productSymmetryFirstFactor observe report hfactors 2 two_ne_zero (by norm_num) base hbase)

/-- **The product IS identified, when the report separates its arguments.** The positive
half: injectivity of the report is exactly what a fit needs in order to be reporting the
product rather than nothing at all. -/
theorem product_identifiedBy_of_injective {Data : Type*} (observe : ℝ × ℝ → Data)
    (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (hinjective : Function.Injective report) :
    Core.IdentifiedBy observe (fun parameter ↦ parameter.1 * parameter.2) := by
  intro first second hobserve
  rw [hfactors, hfactors] at hobserve
  exact hinjective hobserve

/-- **The admissibility rule, whole.** A law reading its two parameters only through their
product pins the product, pins neither factor, and does so because the rescalings are
invisible to it. Quoting a factor from such a fit quotes a number the observation never
constrained; the repair is to fix that factor outside the fit, which is what the fourth
conjunct says cannot be avoided from inside it. -/
theorem factorizedLaw_pins_product_only {Data : Type*} (observe : ℝ × ℝ → Data)
    (report : ℝ → Data)
    (hfactors : ∀ parameter : ℝ × ℝ, observe parameter = report (parameter.1 * parameter.2))
    (hinjective : Function.Injective report)
    (base : ℝ × ℝ) (hfirst : base.1 ≠ 0) (hsecond : base.2 ≠ 0) :
    Core.IdentifiedBy observe (fun parameter ↦ parameter.1 * parameter.2)
      ∧ ¬ Core.IdentifiedBy observe (fun parameter ↦ parameter.1)
      ∧ ¬ Core.IdentifiedBy observe (fun parameter ↦ parameter.2)
      ∧ ∀ scale : ℝ, scale ≠ 0 → ∀ parameter : ℝ × ℝ,
          observe (productRescaling scale parameter) = observe parameter := by
  refine ⟨product_identifiedBy_of_injective observe report hfactors hinjective,
    not_identifiedBy_firstFactor_of_product observe report hfactors base hfirst,
    not_identifiedBy_secondFactor_of_product observe report hfactors base hsecond, ?_⟩
  intro scale hscale parameter
  simp only [hfactors, productRescaling_fixes_product scale hscale parameter]

end Descent.Blindness

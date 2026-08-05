/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.StarOrdered
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic
import Descent.Blindness.ObservationalCeiling

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.InvariantSeparation`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

section InvariantSeparation

/-- The complete limiting-risk signature of a design for a uniform procedure class.  Algorithms,
models, and losses are all arguments, so a procedure cannot contain the design identity as
nonuniform advice. -/
def algorithmicRiskSignature
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (design : Design) :
    Algorithm → Model → Loss → ℝ :=
  fun algorithm model loss ↦ risk algorithm design model loss

/-- Two designs are indistinguishable by the entire uniform class exactly when all entries of
their limiting-risk signatures agree. -/
def AlgorithmicallyEquivalent
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (left right : Design) : Prop :=
  ∀ algorithm model loss, risk algorithm left model loss = risk algorithm right model loss

/-- All risks of the uniform procedure class factor through a proposed design
invariant when one common reconstruction map recovers the complete risk
signature from that invariant.  Requiring a common map is what excludes
nonuniform design advice. -/
def RiskSignaturesFactorThrough
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant) : Prop :=
  ∃ reconstruct : Invariant → Algorithm → Model → Loss → ℝ,
    ∀ design,
      reconstruct (invariant design) = algorithmicRiskSignature risk design

/-- The abstract correspondence is an equality of risk signatures, not an extra conjecture. -/
theorem algorithmicallyEquivalent_iff_signature_eq
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) (left right : Design) :
    AlgorithmicallyEquivalent risk left right ↔
      algorithmicRiskSignature risk left = algorithmicRiskSignature risk right := by
  constructor
  · intro h
    funext algorithm model loss
    exact h algorithm model loss
  · intro h algorithm model loss
    exact congrFun (congrFun (congrFun h algorithm) model) loss

/-- The canonical complete risk signature is itself a sufficient invariant:
its reconstruction map is the identity. -/
theorem riskSignatures_factorThrough_algorithmicRiskSignature
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) := by
  exact ⟨fun signature ↦ signature, fun _design ↦ rfl⟩

/-- Every sufficient design invariant refines the canonical risk signature.
If the proposed invariant identifies two designs, its common reconstruction
map forces their complete risk signatures to agree.  This is the missing
coarseness direction in the abstract correspondence. -/
theorem algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant)
    (hfactor : RiskSignaturesFactorThrough risk invariant)
    (left right : Design) (hsame : invariant left = invariant right) :
    algorithmicRiskSignature risk left = algorithmicRiskSignature risk right := by
  obtain ⟨reconstruct, hreconstruct⟩ := hfactor
  rw [← hreconstruct left, ← hreconstruct right, hsame]

/-- A sufficient invariant cannot identify algorithmically distinguishable
designs.  Equivalently, its equality relation is contained in the canonical
algorithmic-equivalence relation. -/
theorem algorithmicallyEquivalent_of_sufficientInvariant_eq
    {Algorithm Design Model Loss Invariant : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ)
    (invariant : Design → Invariant)
    (hfactor : RiskSignaturesFactorThrough risk invariant)
    (left right : Design) (hsame : invariant left = invariant right) :
    AlgorithmicallyEquivalent risk left right := by
  rw [algorithmicallyEquivalent_iff_signature_eq]
  exact algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    risk invariant hfactor left right hsame

/-- **Universal property of the abstract algorithmic correspondence.**  The
complete risk signature is sufficient, and every other sufficient invariant
refines it.  Hence, up to relabelling of realized signature values, it is the
unique coarsest invariant through which every uniform procedure's risk factors. -/
theorem algorithmicRiskSignature_isCoarsestSufficientInvariant
    {Algorithm Design Model Loss : Type*}
    (risk : Algorithm → Design → Model → Loss → ℝ) :
    RiskSignaturesFactorThrough risk (algorithmicRiskSignature risk) ∧
      ∀ (Invariant : Type*) (invariant : Design → Invariant),
        RiskSignaturesFactorThrough risk invariant →
          ∀ left right, invariant left = invariant right →
            algorithmicRiskSignature risk left =
              algorithmicRiskSignature risk right := by
  refine ⟨riskSignatures_factorThrough_algorithmicRiskSignature risk, ?_⟩
  intro Invariant invariant hfactor left right hsame
  exact algorithmicRiskSignature_eq_of_sufficientInvariant_eq
    risk invariant hfactor left right hsame

/-- **Hardness by invariant separation.**

    `risk a` is the limiting risk of procedure `a` on the first design and
    `risk' a` its limiting risk on the second. `h_equiv` says the class cannot
    distinguish them; `h_opt'` says `bayes'` is optimal on the second.

    The conclusion is that `a`'s excess risk on the FIRST design is at least the
    difference of the two optima. No factor is lost: the bound is the full gap.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is a statement about risks of
    procedures, not about any population, and its content is exhausted by the
    inequality below. -/
theorem suboptimal_of_invariant_separation
    {A : Type*} (risk risk' : A → ℝ) (bayes bayes' : ℝ)
    (h_equiv : ∀ a, risk a = risk' a)
    (h_opt' : ∀ a, bayes' ≤ risk' a)
    (a : A) :
    bayes' - bayes ≤ risk a - bayes := by
  have h := h_opt' a
  rw [h_equiv a]
  linarith

/-- **The separation is vacuous exactly when the two optima agree.** Stated so
    that the template cannot be quoted as a bound when it delivers nothing: a
    class blind to two designs of equal difficulty is not thereby shown to be
    suboptimal on either. -/
theorem invariant_separation_trivial_iff
    (bayes bayes' : ℝ) :
    bayes' - bayes ≤ 0 ↔ bayes' ≤ bayes := by
  constructor <;> intro h <;> linarith

/-- **An invariant separation is an instance of the observational ceiling.**

    `Descent.Blindness.ObservationalCeiling` states the law this file's template is a
    quantitative form of: a probe returning the same data on two objects
    certifies neither, so no criterion factoring through it decides any property
    separating them. Here the probe is the algorithmic invariant, and the
    property is "the optimum is at least as good as `thr`".

    Relating the two is what makes this module contradictable from outside it: if
    the separation pair were wrong, `ProbeBlindness.no_criterion` would deliver a
    false conclusion about the corpus's own blindness law rather than only about
    a private definition here. -/
def separationBlindness {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    ProbeBlindness invariant (fun x ↦ bayes x ≤ thr) where
  positive := d
  negative := d'
  same_data := same
  holds := hd
  fails := hd'

/-- **No rule reading only the invariant decides which design is easier.**
    The observational ceiling applied to the separation pair. -/
theorem no_invariant_criterion_for_optimum {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    ¬ ∃ decide : Invariant → Prop,
        ∀ x : Design, bayes x ≤ thr ↔ decide (invariant x) :=
  (separationBlindness invariant bayes d d' thr same hd hd').no_criterion

/-- **The bridge, named in a statement rather than only in a proof.**

    `separationBlindness` really is a `ProbeBlindness` of the corpus's own kind,
    carrying the first design as its positive witness. Stating that puts this
    module's definitions beside `ObservationalCeiling`'s in one theorem, which is
    what makes a divergence between them a compile error instead of a silent
    fork. -/
@[simp] theorem separationBlindness_positive {Design Invariant : Type*}
    (invariant : Design → Invariant) (bayes : Design → ℝ)
    (d d' : Design) (thr : ℝ)
    (same : invariant d = invariant d')
    (hd : bayes d ≤ thr) (hd' : ¬ bayes d' ≤ thr) :
    (separationBlindness invariant bayes d d' thr same hd hd' :
      ProbeBlindness invariant (fun x ↦ bayes x ≤ thr)).positive = d := rfl

end InvariantSeparation

end TrafficInvariantSeparation
end Descent.Blindness

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Topology.Order.IntermediateValue

assert_below Descent.Decision Descent.Program

/-!
# The marginal anchor on a declared predictor law, and its Fisher orthogonality

A marginally interpretable binary model fixes the population risk `π` of a context and
lets an individual predictor `h(v)` move each person around it:
`p(v) = σ(a + h(v))` with the intercept `a` determined by the **anchoring equation**

`E_p[σ(a + h(v))] = π`,

the expectation taken under the declared law `p` of the predictor in that context.  The
closed-form probit identity `E[Φ(q√(1+b²) + bz)] = Φ(q)` is the special case of a
standard-normal `z`; it fails as soon as the conditional law of the predictor is not
the one the transform assumed.  This module replaces the shortcut by the defining
equation on an arbitrary finite law -- the empirical grid a fitting engine actually
declares -- and proves what the design needs of it:

* `exists_unique_anchor`: for every `π ∈ (0, 1)` and every predictor shape `h`, exactly
  one intercept solves the anchoring equation.  Continuity and strict monotonicity of
  the anchored mean in `a`, with limits `0` and `1`, are the whole proof; nothing is
  assumed about the shape of `p`.
* `anchored_score_orthogonal`: along any differentiable path `θ ↦ (a(θ), h(θ, ·))` on
  which the anchor holds identically, the Bernoulli-weighted score of the linear
  predictor vanishes: `Σ_v p_v W_v (a' + h'_v) = 0` with `W = σ(1 − σ)`.
* `anchor_deriv_eq`: hence `a' = −E_p[W h'] / E_p[W]`, the implicit-function form.
* `baseline_anchor_deriv`: moving the target risk `π = σ(q)` with `h` fixed gives
  `a_q · E_p[W] = W(q)`, a score direction constant across predictor values.
* `crossInformation_baseline_shape_zero`: the expected Bernoulli cross-information
  between that constant baseline direction and the anchored shape direction is zero.

That last statement is the design's stronger separation: at the declared law, baseline
and predictor shape are orthogonal in expected information, not merely separately
penalised.  Its scope is exactly its hypotheses -- an observed predictor, the canonical
logit link, a fixed declared law, and the anchor holding along the path.  A law that
itself depends on `θ`, an integrated-out latent predictor, or a two-stage estimate of
the law is outside it.

Builds on `FiniteReportLaw` and its `expectation`, and on Mathlib's `Real.sigmoid`
with its positivity, monotonicity, derivative and limits.

## Empirical status

None. The anchor is a property of the specified model under the specified law.  It
does not assert that `π` is any population's prevalence, nor that observed outcomes are
calibrated in any subgroup.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarginalAnchor

open Filter Topology

noncomputable section

variable {V : Type*} [Fintype V]

/-! ### The anchored mean -/

/-- The anchored mean: the population risk the intercept `a` produces with predictor
shape `h` under the declared predictor law `p`, `E_p[σ(a + h(v))]`. -/
def anchoredMean (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ) : ℝ :=
  p.expectation (fun v ↦ Real.sigmoid (a + h v))

theorem anchoredMean_eq_sum (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ) :
    anchoredMean p h a = ∑ v, p.mass v * Real.sigmoid (a + h v) := rfl

/-- A probability law on a finite space puts positive mass somewhere. -/
theorem exists_pos_mass (p : FiniteReportLaw V) : ∃ v, 0 < p.mass v := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ v, p.mass v = 0 := fun v ↦ le_antisymm (hcon v) (p.mass_nonneg v)
  have hsum := p.mass_sum
  simp [hzero] at hsum

theorem continuous_sigmoid : Continuous Real.sigmoid :=
  continuous_iff_continuousAt.mpr fun x ↦ (Real.hasDerivAt_sigmoid x).continuousAt

theorem continuous_anchoredMean (p : FiniteReportLaw V) (h : V → ℝ) :
    Continuous (anchoredMean p h) := by
  unfold anchoredMean FiniteReportLaw.expectation
  exact continuous_finset_sum _ fun v _ ↦
    continuous_const.mul (continuous_sigmoid.comp (continuous_add_right (h v)))

/-- The anchored mean is strictly increasing in the intercept. -/
theorem anchoredMean_strictMono (p : FiniteReportLaw V) (h : V → ℝ) :
    StrictMono (anchoredMean p h) := by
  intro a b hab
  rw [anchoredMean_eq_sum, anchoredMean_eq_sum]
  obtain ⟨v₀, hv₀⟩ := exists_pos_mass p
  apply Finset.sum_lt_sum
  · intro v _
    exact mul_le_mul_of_nonneg_left
      (Real.sigmoid_strictMono (by linarith : a + h v < b + h v)).le (p.mass_nonneg v)
  · exact ⟨v₀, Finset.mem_univ _,
      mul_lt_mul_of_pos_left
        (Real.sigmoid_strictMono (by linarith : a + h v₀ < b + h v₀)) hv₀⟩

theorem tendsto_anchoredMean_atBot (p : FiniteReportLaw V) (h : V → ℝ) :
    Tendsto (anchoredMean p h) atBot (𝓝 0) := by
  have hsum : Tendsto (fun a ↦ ∑ v, p.mass v * Real.sigmoid (a + h v)) atBot
      (𝓝 (∑ v : V, p.mass v * 0)) :=
    tendsto_finset_sum _ fun v _ ↦
      (Real.tendsto_sigmoid_atBot.comp
        (tendsto_atBot_add_const_right atBot (h v) tendsto_id)).const_mul (p.mass v)
  simpa [anchoredMean, FiniteReportLaw.expectation] using hsum

theorem tendsto_anchoredMean_atTop (p : FiniteReportLaw V) (h : V → ℝ) :
    Tendsto (anchoredMean p h) atTop (𝓝 1) := by
  have hsum : Tendsto (fun a ↦ ∑ v, p.mass v * Real.sigmoid (a + h v)) atTop
      (𝓝 (∑ v : V, p.mass v * 1)) :=
    tendsto_finset_sum _ fun v _ ↦
      (Real.tendsto_sigmoid_atTop.comp
        (tendsto_atTop_add_const_right atTop (h v) tendsto_id)).const_mul (p.mass v)
  have hone : (∑ v : V, p.mass v * 1) = 1 := by simp [p.mass_sum]
  rw [hone] at hsum
  simpa [anchoredMean, FiniteReportLaw.expectation] using hsum

/-! ### Existence and uniqueness of the anchor -/

/-- **The anchor exists and is unique.**  For a target risk `π ∈ (0, 1)` and any predictor
shape `h`, exactly one intercept `a` makes the anchored mean equal to `π`.  The declared
law may be skewed, discrete, a mixture -- any finite law. -/
theorem exists_unique_anchor (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ} (hπ0 : 0 < π)
    (hπ1 : π < 1) :
    ∃! a : ℝ, anchoredMean p h a = π := by
  obtain ⟨lo, hlo⟩ : ∃ lo, anchoredMean p h lo < π :=
    ((tendsto_anchoredMean_atBot p h).eventually_lt_const hπ0).exists
  obtain ⟨hi, hhi⟩ : ∃ hi, π < anchoredMean p h hi :=
    ((tendsto_anchoredMean_atTop p h).eventually_const_lt hπ1).exists
  have hmem : π ∈ Set.uIcc (anchoredMean p h lo) (anchoredMean p h hi) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hlo.le, hhi.le⟩)
  obtain ⟨a, -, ha⟩ :=
    intermediate_value_uIcc (continuous_anchoredMean p h).continuousOn hmem
  exact ⟨a, ha, fun b hb ↦ (anchoredMean_strictMono p h).injective (hb.trans ha.symm)⟩

/-- The anchor intercept: the unique solution of the anchoring equation. -/
def anchor (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) :
    ℝ :=
  Classical.choose (exists_unique_anchor p h hπ0 hπ1).exists

theorem anchor_spec (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ} (hπ0 : 0 < π)
    (hπ1 : π < 1) :
    anchoredMean p h (anchor p h hπ0 hπ1) = π :=
  Classical.choose_spec (exists_unique_anchor p h hπ0 hπ1).exists

/-- Any solution of the anchoring equation is the anchor. -/
theorem eq_anchor_of_anchoredMean_eq (p : FiniteReportLaw V) (h : V → ℝ) {π a : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) (ha : anchoredMean p h a = π) :
    a = anchor p h hπ0 hπ1 :=
  (exists_unique_anchor p h hπ0 hπ1).unique ha (anchor_spec p h hπ0 hπ1)

/-! ### Differentiating the anchor -/

/-- The Bernoulli weight `W(η) = σ(η)(1 − σ(η))` at linear predictor `η`. -/
def bernoulliWeight (η : ℝ) : ℝ := Real.sigmoid η * (1 - Real.sigmoid η)

theorem bernoulliWeight_pos (η : ℝ) : 0 < bernoulliWeight η :=
  mul_pos (Real.sigmoid_pos η) (by linarith [Real.sigmoid_lt_one η])

/-- Derivative of the anchored mean along a differentiable path `θ ↦ (a(θ), h(θ, ·))`. -/
theorem hasDerivAt_anchoredMean_path (p : FiniteReportLaw V) (a : ℝ → ℝ)
    (h : ℝ → V → ℝ) {θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ) :
    HasDerivAt (fun t ↦ anchoredMean p (h t) (a t))
      (∑ v, p.mass v * (bernoulliWeight (a θ + h θ v) * (a' + h' v))) θ := by
  have hterm : ∀ v ∈ (Finset.univ : Finset V),
      HasDerivAt (fun t ↦ p.mass v * Real.sigmoid (a t + h t v))
        (p.mass v * (bernoulliWeight (a θ + h θ v) * (a' + h' v))) θ := by
    intro v _
    have hsum : HasDerivAt (fun t ↦ a t + h t v) (a' + h' v) θ := ha.add (hh v)
    have hcomp := (Real.hasDerivAt_sigmoid (a θ + h θ v)).comp θ hsum
    exact hcomp.const_mul (p.mass v)
  have hderiv := HasDerivAt.sum hterm
  convert hderiv using 1
  funext t
  simp [anchoredMean, FiniteReportLaw.expectation, Finset.sum_apply]

/-- **The anchored score is Bernoulli-orthogonal.**  Along a path on which the anchor
equation holds identically, `Σ_v p_v W_v (a' + h'_v) = 0`. -/
theorem anchored_score_orthogonal (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean p (h t) (a t) = π) :
    ∑ v, p.mass v * (bernoulliWeight (a θ + h θ v) * (a' + h' v)) = 0 := by
  have hpath := hasDerivAt_anchoredMean_path p a h ha hh
  have hconst : HasDerivAt (fun t ↦ anchoredMean p (h t) (a t)) 0 θ := by
    have hfun : (fun t ↦ anchoredMean p (h t) (a t)) = fun _ ↦ π := funext hanchor
    rw [hfun]
    exact hasDerivAt_const θ π
  exact hpath.unique hconst

/-- The total Bernoulli weight under the declared law is positive. -/
theorem sum_mass_bernoulliWeight_pos (p : FiniteReportLaw V) (η : V → ℝ) :
    0 < ∑ v, p.mass v * bernoulliWeight (η v) := by
  obtain ⟨v₀, hv₀⟩ := exists_pos_mass p
  exact Finset.sum_pos' (fun v _ ↦ mul_nonneg (p.mass_nonneg v) (bernoulliWeight_pos _).le)
    ⟨v₀, Finset.mem_univ _, mul_pos hv₀ (bernoulliWeight_pos _)⟩

/-- **The implicit-function form.**  The anchor's derivative is the negated
`W`-weighted mean of the predictor-shape derivative: `a' = −E_p[W h'] / E_p[W]`. -/
theorem anchor_deriv_eq (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean p (h t) (a t) = π) :
    a' = -(∑ v, p.mass v * bernoulliWeight (a θ + h θ v) * h' v)
      / (∑ v, p.mass v * bernoulliWeight (a θ + h θ v)) := by
  have h0 := anchored_score_orthogonal p a h ha hh hanchor
  have hW := sum_mass_bernoulliWeight_pos p (fun v ↦ a θ + h θ v)
  rw [eq_div_iff hW.ne']
  have hexp : ∑ v, p.mass v * (bernoulliWeight (a θ + h θ v) * (a' + h' v))
      = a' * ∑ v, p.mass v * bernoulliWeight (a θ + h θ v)
        + ∑ v, p.mass v * bernoulliWeight (a θ + h θ v) * h' v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  linarith

/-- **The baseline direction.**  Moving the target risk `π = σ(q)` with the predictor
shape fixed, the anchor satisfies `a_q · E_p[W] = W(q)`: its score direction is the
same positive number at every predictor value. -/
theorem baseline_anchor_deriv (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ → ℝ) {q a' : ℝ}
    (ha : HasDerivAt a a' q) (hanchor : ∀ t, anchoredMean p h (a t) = Real.sigmoid t) :
    a' * ∑ v, p.mass v * bernoulliWeight (a q + h v) = bernoulliWeight q := by
  have hpath := hasDerivAt_anchoredMean_path p a (fun _ ↦ h) ha
    (fun v ↦ hasDerivAt_const q (h v))
  have hsig : HasDerivAt (fun t ↦ anchoredMean p h (a t)) (bernoulliWeight q) q := by
    have hfun : (fun t ↦ anchoredMean p h (a t)) = Real.sigmoid := funext hanchor
    rw [hfun]
    exact Real.hasDerivAt_sigmoid q
  have huniq := hpath.unique hsig
  rw [← huniq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

/-! ### Fisher orthogonality -/

/-- Expected Bernoulli cross-information between two score directions `s₁`, `s₂` at
linear predictor `η`, under the declared law: `Σ_v p_v W(η_v) s₁(v) s₂(v)`. -/
def crossInformation (p : FiniteReportLaw V) (η s₁ s₂ : V → ℝ) : ℝ :=
  ∑ v, p.mass v * bernoulliWeight (η v) * s₁ v * s₂ v

/-- **Fisher orthogonality of baseline and predictor shape.**  The baseline score
direction is constant across predictor values; the anchored shape direction is
`a' + h'_v`.  Their expected cross-information under the declared law is zero. -/
theorem crossInformation_baseline_shape_zero (p : FiniteReportLaw V) (a : ℝ → ℝ)
    (h : ℝ → V → ℝ) {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean p (h t) (a t) = π) (c : ℝ) :
    crossInformation p (fun v ↦ a θ + h θ v) (fun _ ↦ c) (fun v ↦ a' + h' v) = 0 := by
  unfold crossInformation
  have h0 := anchored_score_orthogonal p a h ha hh hanchor
  calc ∑ v, p.mass v * bernoulliWeight (a θ + h θ v) * c * (a' + h' v)
      = c * ∑ v, p.mass v * (bernoulliWeight (a θ + h θ v) * (a' + h' v)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ ↦ by ring
    _ = 0 := by rw [h0, mul_zero]

end

end Descent.Portability.MarginalAnchor

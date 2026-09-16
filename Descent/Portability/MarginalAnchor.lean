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
`p(v) = L(a + h(v))` for a link `L`, with the intercept `a` determined by the
**anchoring equation**

`E_p[L(a + h(v))] = π`,

the expectation taken under the declared law `p` of the predictor in that context.  The
closed-form probit identity `E[Φ(q√(1+b²) + bz)] = Φ(q)` is the special case of a
standard-normal `z`; it fails as soon as the conditional law of the predictor is not
the one the transform assumed.  This module replaces the shortcut by the defining
equation on an arbitrary finite law -- the empirical grid a fitting engine actually
declares -- for an arbitrary link, and proves what the design needs of it:

* `exists_unique_anchor`: for a continuous, strictly increasing link with limits `0`
  and `1`, every `π ∈ (0, 1)` and every predictor shape `h`, exactly one intercept
  solves the anchoring equation.  Nothing is assumed about the shape of `p`.
* `anchored_score_orthogonal`: along any differentiable path `θ ↦ (a(θ), h(θ, ·))` on
  which the anchor holds identically, the link-weighted score of the linear predictor
  vanishes: `Σ_v p_v W_v (a' + h'_v) = 0` with `W = L'`.
* `anchor_deriv_eq`: hence `a' = −E_p[W h'] / E_p[W]`, the implicit-function form.
* `baseline_anchor_deriv`: moving the target risk `π = L(q)` with `h` fixed gives
  `a_q · E_p[W] = W(q)`, a score direction constant across predictor values.
* `crossInformation_baseline_shape_zero`: the expected cross-information between that
  constant baseline direction and the anchored shape direction is zero.

The link enters only through the hypotheses each theorem names -- continuity, strict
monotonicity, the two limits, a derivative `W` -- so the statements cover the logit
link (instantiated below with Mathlib's `Real.sigmoid`, where `W` is the Bernoulli
weight `σ(1 − σ)` and the cross-information is expected Fisher information) and the
probit link alike; `ProbitAnchor` supplies the probit's four facts and states that
instance, and `GaussianAnchor` gives its closed form under a Gaussian declared law.

That last statement is the design's stronger separation: at the declared law, baseline
and predictor shape are orthogonal in expected information, not merely separately
penalised.  Its scope is exactly its hypotheses -- an observed predictor, a fixed
declared law, and the anchor holding along the path.  A law that itself depends on
`θ`, an integrated-out latent predictor, or a two-stage estimate of the law is outside
it.

Builds on `FiniteReportLaw` and its `expectation`, and on Mathlib's `Real.sigmoid`
with its positivity, monotonicity, derivative and limits.

## Empirical status

None. The anchor is a property of the specified model under the specified law.  It
does not assert that `π` is any population's prevalence, nor that observed outcomes are
calibrated in any subgroup.
-/

namespace Descent.Portability.MarginalAnchor

open Filter Topology

noncomputable section

variable {V : Type*} [Fintype V]

/-! ### The anchored mean under a link -/

/-- The anchored mean: the population risk the intercept `a` produces with predictor
shape `h` under the declared predictor law `p` and link `L`, `E_p[L(a + h(v))]`. -/
def anchoredMean (L : ℝ → ℝ) (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ) : ℝ :=
  p.expectation (fun v ↦ L (a + h v))

theorem anchoredMean_eq_sum (L : ℝ → ℝ) (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ) :
    anchoredMean L p h a = ∑ v, p.mass v * L (a + h v) := rfl

/-- A probability law on a finite space puts positive mass somewhere. -/
theorem exists_pos_mass (p : FiniteReportLaw V) : ∃ v, 0 < p.mass v := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ v, p.mass v = 0 := fun v ↦ le_antisymm (hcon v) (p.mass_nonneg v)
  have hsum := p.mass_sum
  simp [hzero] at hsum

theorem continuous_anchoredMean {L : ℝ → ℝ} (hL : Continuous L) (p : FiniteReportLaw V)
    (h : V → ℝ) : Continuous (anchoredMean L p h) := by
  unfold anchoredMean FiniteReportLaw.expectation
  exact continuous_finset_sum _ fun v _ ↦
    continuous_const.mul (hL.comp (continuous_add_right (h v)))

/-- A strictly increasing link makes the anchored mean strictly increasing in the
intercept. -/
theorem anchoredMean_strictMono {L : ℝ → ℝ} (hL : StrictMono L) (p : FiniteReportLaw V)
    (h : V → ℝ) : StrictMono (anchoredMean L p h) := by
  intro a b hab
  rw [anchoredMean_eq_sum, anchoredMean_eq_sum]
  obtain ⟨v₀, hv₀⟩ := exists_pos_mass p
  apply Finset.sum_lt_sum
  · intro v _
    exact mul_le_mul_of_nonneg_left (hL (by linarith : a + h v < b + h v)).le (p.mass_nonneg v)
  · exact ⟨v₀, Finset.mem_univ _,
      mul_lt_mul_of_pos_left (hL (by linarith : a + h v₀ < b + h v₀)) hv₀⟩

theorem tendsto_anchoredMean_atBot {L : ℝ → ℝ} (h0 : Tendsto L atBot (𝓝 0))
    (p : FiniteReportLaw V) (h : V → ℝ) : Tendsto (anchoredMean L p h) atBot (𝓝 0) := by
  have hsum : Tendsto (fun a ↦ ∑ v, p.mass v * L (a + h v)) atBot
      (𝓝 (∑ v : V, p.mass v * 0)) :=
    tendsto_finset_sum _ fun v _ ↦
      (h0.comp (tendsto_atBot_add_const_right atBot (h v) tendsto_id)).const_mul (p.mass v)
  simpa [anchoredMean, FiniteReportLaw.expectation] using hsum

theorem tendsto_anchoredMean_atTop {L : ℝ → ℝ} (h1 : Tendsto L atTop (𝓝 1))
    (p : FiniteReportLaw V) (h : V → ℝ) : Tendsto (anchoredMean L p h) atTop (𝓝 1) := by
  have hsum : Tendsto (fun a ↦ ∑ v, p.mass v * L (a + h v)) atTop
      (𝓝 (∑ v : V, p.mass v * 1)) :=
    tendsto_finset_sum _ fun v _ ↦
      (h1.comp (tendsto_atTop_add_const_right atTop (h v) tendsto_id)).const_mul (p.mass v)
  have hone : (∑ v : V, p.mass v * 1) = 1 := by simp [p.mass_sum]
  rw [hone] at hsum
  simpa [anchoredMean, FiniteReportLaw.expectation] using hsum

/-! ### Existence and uniqueness of the anchor -/

/-- **The anchor exists and is unique.**  For a continuous, strictly increasing link
with limits `0` and `1`, a target risk `π ∈ (0, 1)` and any predictor shape `h`, exactly
one intercept `a` makes the anchored mean equal to `π`.  The declared law may be skewed,
discrete, a mixture -- any finite law. -/
theorem exists_unique_anchor {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictMono L)
    (h0 : Tendsto L atBot (𝓝 0)) (h1 : Tendsto L atTop (𝓝 1)) (p : FiniteReportLaw V)
    (h : V → ℝ) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) :
    ∃! a : ℝ, anchoredMean L p h a = π := by
  obtain ⟨lo, hlo⟩ : ∃ lo, anchoredMean L p h lo < π :=
    ((tendsto_anchoredMean_atBot h0 p h).eventually_lt_const hπ0).exists
  obtain ⟨hi, hhi⟩ : ∃ hi, π < anchoredMean L p h hi :=
    ((tendsto_anchoredMean_atTop h1 p h).eventually_const_lt hπ1).exists
  have hmem : π ∈ Set.uIcc (anchoredMean L p h lo) (anchoredMean L p h hi) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hlo.le, hhi.le⟩)
  obtain ⟨a, -, ha⟩ :=
    intermediate_value_uIcc (continuous_anchoredMean hc p h).continuousOn hmem
  exact ⟨a, ha, fun b hb ↦ (anchoredMean_strictMono hm p h).injective (hb.trans ha.symm)⟩

/-- The anchor intercept: the unique solution of the anchoring equation. -/
def anchor {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictMono L) (h0 : Tendsto L atBot (𝓝 0))
    (h1 : Tendsto L atTop (𝓝 1)) (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) : ℝ :=
  Classical.choose (exists_unique_anchor hc hm h0 h1 p h hπ0 hπ1).exists

theorem anchor_spec {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictMono L)
    (h0 : Tendsto L atBot (𝓝 0)) (h1 : Tendsto L atTop (𝓝 1)) (p : FiniteReportLaw V)
    (h : V → ℝ) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) :
    anchoredMean L p h (anchor hc hm h0 h1 p h hπ0 hπ1) = π :=
  Classical.choose_spec (exists_unique_anchor hc hm h0 h1 p h hπ0 hπ1).exists

/-- Any solution of the anchoring equation is the anchor. -/
theorem eq_anchor_of_anchoredMean_eq {L : ℝ → ℝ} (hc : Continuous L) (hm : StrictMono L)
    (h0 : Tendsto L atBot (𝓝 0)) (h1 : Tendsto L atTop (𝓝 1)) (p : FiniteReportLaw V)
    (h : V → ℝ) {π a : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) (ha : anchoredMean L p h a = π) :
    a = anchor hc hm h0 h1 p h hπ0 hπ1 :=
  (exists_unique_anchor hc hm h0 h1 p h hπ0 hπ1).unique ha (anchor_spec hc hm h0 h1 p h hπ0 hπ1)

/-! ### Differentiating the anchor -/

/-- Derivative of the anchored mean along a differentiable path `θ ↦ (a(θ), h(θ, ·))`,
for a link with derivative `W`. -/
theorem hasDerivAt_anchoredMean_path {L W : ℝ → ℝ} (hd : ∀ x, HasDerivAt L (W x) x)
    (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ) {θ a' : ℝ} {h' : V → ℝ}
    (ha : HasDerivAt a a' θ) (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ) :
    HasDerivAt (fun t ↦ anchoredMean L p (h t) (a t))
      (∑ v, p.mass v * (W (a θ + h θ v) * (a' + h' v))) θ := by
  have hterm : ∀ v ∈ (Finset.univ : Finset V),
      HasDerivAt (fun t ↦ p.mass v * L (a t + h t v))
        (p.mass v * (W (a θ + h θ v) * (a' + h' v))) θ := by
    intro v _
    have hsum : HasDerivAt (fun t ↦ a t + h t v) (a' + h' v) θ := ha.add (hh v)
    have hcomp := (hd (a θ + h θ v)).comp θ hsum
    exact hcomp.const_mul (p.mass v)
  have hderiv := HasDerivAt.sum hterm
  convert hderiv using 1
  funext t
  simp [anchoredMean, FiniteReportLaw.expectation, Finset.sum_apply]

/-- **The anchored score is link-orthogonal.**  Along a path on which the anchor
equation holds identically, `Σ_v p_v W_v (a' + h'_v) = 0`. -/
theorem anchored_score_orthogonal {L W : ℝ → ℝ} (hd : ∀ x, HasDerivAt L (W x) x)
    (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ) {π θ a' : ℝ}
    {h' : V → ℝ} (ha : HasDerivAt a a' θ) (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean L p (h t) (a t) = π) :
    ∑ v, p.mass v * (W (a θ + h θ v) * (a' + h' v)) = 0 := by
  have hpath := hasDerivAt_anchoredMean_path hd p a h ha hh
  have hconst : HasDerivAt (fun t ↦ anchoredMean L p (h t) (a t)) 0 θ := by
    have hfun : (fun t ↦ anchoredMean L p (h t) (a t)) = fun _ ↦ π := funext hanchor
    rw [hfun]
    exact hasDerivAt_const θ π
  exact hpath.unique hconst

/-- The total link weight under the declared law is positive when the weight is. -/
theorem sum_mass_weight_pos {W : ℝ → ℝ} (hW : ∀ x, 0 < W x) (p : FiniteReportLaw V)
    (η : V → ℝ) : 0 < ∑ v, p.mass v * W (η v) := by
  obtain ⟨v₀, hv₀⟩ := exists_pos_mass p
  exact Finset.sum_pos' (fun v _ ↦ mul_nonneg (p.mass_nonneg v) (hW _).le)
    ⟨v₀, Finset.mem_univ _, mul_pos hv₀ (hW _)⟩

/-- **The implicit-function form.**  The anchor's derivative is the negated
`W`-weighted mean of the predictor-shape derivative: `a' = −E_p[W h'] / E_p[W]`. -/
theorem anchor_deriv_eq {L W : ℝ → ℝ} (hd : ∀ x, HasDerivAt L (W x) x)
    (hW : ∀ x, 0 < W x) (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ}
    (ha : HasDerivAt a a' θ) (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean L p (h t) (a t) = π) :
    a' = -(∑ v, p.mass v * W (a θ + h θ v) * h' v)
      / (∑ v, p.mass v * W (a θ + h θ v)) := by
  have h0 := anchored_score_orthogonal hd p a h ha hh hanchor
  have hpos := sum_mass_weight_pos hW p (fun v ↦ a θ + h θ v)
  rw [eq_div_iff hpos.ne']
  have hexp : ∑ v, p.mass v * (W (a θ + h θ v) * (a' + h' v))
      = a' * ∑ v, p.mass v * W (a θ + h θ v)
        + ∑ v, p.mass v * W (a θ + h θ v) * h' v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  linarith

/-- **The baseline direction.**  Moving the target risk `π = L(q)` with the predictor
shape fixed, the anchor satisfies `a_q · E_p[W] = W(q)`: its score direction is the
same number at every predictor value. -/
theorem baseline_anchor_deriv {L W : ℝ → ℝ} (hd : ∀ x, HasDerivAt L (W x) x)
    (p : FiniteReportLaw V) (h : V → ℝ) (a : ℝ → ℝ) {q a' : ℝ} (ha : HasDerivAt a a' q)
    (hanchor : ∀ t, anchoredMean L p h (a t) = L t) :
    a' * ∑ v, p.mass v * W (a q + h v) = W q := by
  have hpath := hasDerivAt_anchoredMean_path hd p a (fun _ ↦ h) ha
    (fun v ↦ hasDerivAt_const q (h v))
  have hlink : HasDerivAt (fun t ↦ anchoredMean L p h (a t)) (W q) q := by
    have hfun : (fun t ↦ anchoredMean L p h (a t)) = L := funext hanchor
    rw [hfun]
    exact hd q
  have huniq := hpath.unique hlink
  rw [← huniq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

/-! ### Cross-information -/

/-- Expected cross-information between two score directions `s₁`, `s₂` at linear
predictor `η`, under the declared law and link weight `W`: `Σ_v p_v W(η_v) s₁(v) s₂(v)`.
For the logit link with `W = σ(1 − σ)` this is the expected Bernoulli Fisher
information. -/
def crossInformation (W : ℝ → ℝ) (p : FiniteReportLaw V) (η s₁ s₂ : V → ℝ) : ℝ :=
  ∑ v, p.mass v * W (η v) * s₁ v * s₂ v

/-- **Orthogonality of baseline and predictor shape.**  The baseline score direction
is constant across predictor values; the anchored shape direction is `a' + h'_v`.
Their expected cross-information under the declared law is zero. -/
theorem crossInformation_baseline_shape_zero {L W : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt L (W x) x) (p : FiniteReportLaw V) (a : ℝ → ℝ)
    (h : ℝ → V → ℝ) {π θ a' : ℝ} {h' : V → ℝ}
    (ha : HasDerivAt a a' θ) (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean L p (h t) (a t) = π) (c : ℝ) :
    crossInformation W p (fun v ↦ a θ + h θ v) (fun _ ↦ c) (fun v ↦ a' + h' v) = 0 := by
  unfold crossInformation
  have h0 := anchored_score_orthogonal hd p a h ha hh hanchor
  calc ∑ v, p.mass v * W (a θ + h θ v) * c * (a' + h' v)
      = c * ∑ v, p.mass v * (W (a θ + h θ v) * (a' + h' v)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ ↦ by ring
    _ = 0 := by rw [h0, mul_zero]

/-! ### The logit link -/

/-- The Bernoulli weight `W(η) = σ(η)(1 − σ(η))`: the logit link's derivative. -/
def bernoulliWeight (η : ℝ) : ℝ := Real.sigmoid η * (1 - Real.sigmoid η)

theorem bernoulliWeight_pos (η : ℝ) : 0 < bernoulliWeight η :=
  mul_pos (Real.sigmoid_pos η) (by linarith [Real.sigmoid_lt_one η])

theorem hasDerivAt_sigmoid_bernoulliWeight (x : ℝ) :
    HasDerivAt Real.sigmoid (bernoulliWeight x) x :=
  Real.hasDerivAt_sigmoid x

theorem continuous_sigmoid : Continuous Real.sigmoid :=
  continuous_iff_continuousAt.mpr fun x ↦ (Real.hasDerivAt_sigmoid x).continuousAt

/-- **The logit anchor exists and is unique.** -/
theorem exists_unique_anchor_logit (p : FiniteReportLaw V) (h : V → ℝ) {π : ℝ}
    (hπ0 : 0 < π) (hπ1 : π < 1) :
    ∃! a : ℝ, anchoredMean Real.sigmoid p h a = π :=
  exists_unique_anchor continuous_sigmoid Real.sigmoid_strictMono Real.tendsto_sigmoid_atBot
    Real.tendsto_sigmoid_atTop p h hπ0 hπ1

/-- **The logit anchor's derivative** is the negated Bernoulli-weighted mean of the
predictor-shape derivative. -/
theorem anchor_deriv_eq_logit (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean Real.sigmoid p (h t) (a t) = π) :
    a' = -(∑ v, p.mass v * bernoulliWeight (a θ + h θ v) * h' v)
      / (∑ v, p.mass v * bernoulliWeight (a θ + h θ v)) :=
  anchor_deriv_eq hasDerivAt_sigmoid_bernoulliWeight bernoulliWeight_pos p a h ha hh hanchor

/-- **Fisher orthogonality of baseline and predictor shape under the logit link.** -/
theorem fisher_baseline_shape_zero (p : FiniteReportLaw V) (a : ℝ → ℝ) (h : ℝ → V → ℝ)
    {π θ a' : ℝ} {h' : V → ℝ} (ha : HasDerivAt a a' θ)
    (hh : ∀ v, HasDerivAt (fun t ↦ h t v) (h' v) θ)
    (hanchor : ∀ t, anchoredMean Real.sigmoid p (h t) (a t) = π) (c : ℝ) :
    crossInformation bernoulliWeight p (fun v ↦ a θ + h θ v) (fun _ ↦ c)
      (fun v ↦ a' + h' v) = 0 :=
  crossInformation_baseline_shape_zero hasDerivAt_sigmoid_bernoulliWeight p a h ha hh hanchor c

end

end Descent.Portability.MarginalAnchor

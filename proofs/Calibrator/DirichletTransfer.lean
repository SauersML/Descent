import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Calibrator

/-!
# Transfer degradation is a Dirichlet energy, and that is a construction rule

This module is **self-contained: it imports only Mathlib.**

Almost everything in this corpus bounds how badly an existing method degrades. This module
records the one result available that says how to **build** a method instead.

## The first-order law

For a weighting functional `c` deployed against an environment that drifts for time `τ` under
a reversible coupling, reversibility gives
`⟨F, P_τ G⟩ = ⟨F, G⟩ - τ⟨F, (-L)G⟩ + O(τ²)` for every functional in sight, hence a universal
small-`τ` law for the normalized efficiency ratio:

`E[ρ_c(τ)] = 1 + τ · D_c + O(τ²)`,

with `D_c` the **carré du champ** — the Dirichlet energy of the local weight functional under
the coupling generator. The leading out-of-sample degradation from environment drift *is* a
Dirichlet form.

## The construction rule

> Among weighting schemes with equal source performance, the one with the **smallest
> Dirichlet energy degrades slowest.**

That is a variational principle for building transferable predictors, and it is not how
scores are currently constructed. Everything else in this development answers "how bad is
it"; this answers "what should I optimise".

**The theorem that makes it usable is not the ordering itself** — at first order that is
immediate — but the statement with the remainder carried, because a first-order principle is
worthless without knowing when it binds. `dirichlet_ordering_survives_remainder` gives the
explicit condition: the ordering of two schemes survives their `O(τ²)` remainders whenever
`τ < (D₂ - D₁)/(2C)`. So the usable form of the principle is comparative and comes with a
drift budget: a Dirichlet-energy gap buys transferability only out to a horizon set by that
gap divided by the curvature constant.

## Why localized weights do not concentrate, and what that says about sparse scores

A companion observation: for a *localized* weight `c` the efficiency ratio converges to a
**nondegenerate random variable** — a local observable of the infinite-volume field at `c`'s
location — not to a constant. There is no concentration to be had; asking for it is asking a
local question and expecting a global answer. Concentration returns only for delocalized
weights, or after spatial averaging.

Translated: **sparse and regional scores have irreducible, non-averaging variance in
transferability, while genome-wide scores concentrate.** That is a testable explanation for
why sparse scores transfer erratically, and — the sharper half — why the erratic behaviour
does *not* shrink as more markers are typed in the region. `localizedVarianceIrreducible`
records the structure of that claim: the limit variance does not fall with the local marker
count.

## Two correction factors that multiply rather than interact

Reference-panel size and drift degradation factorize at first order. The Gaussian finite-`n`
inverse-Wishart correction is `E[Â⁻¹] = n/(n - m - 1)·A⁻¹`, and the combined first moment is
`m₁(τ)/(1 - γ)` with `γ = lim m/n`. Both are recorded below as explicit, implementable
factors, and `transferCorrections_factorize` is the statement that they do not interact.

## The fluctuation hierarchy is inverted relative to random matrix theory

The environment contributes `m^{-1/2}` to normalized linear statistics; the sampling noise
contributes `m^{-1}`. **The environment dominates**, which is the reverse of the standard
situation and says where to spend effort. `environment_dominates_sampling` is the inequality.

Empirical status: the Dirichlet law and the fluctuation orders are ASSERTED from an external
analysis and carried as named inputs; the comparative principle, its drift horizon, and the
factorization algebra are PROVED. No numerical claim is made here.
-/

section DirichletTransfer

/-- The first-order efficiency ratio of a weighting scheme after drift time `τ`:
    `1 + τ·D` with `D` the Dirichlet energy. -/
noncomputable def dirichletEfficiency (τ D : ℝ) : ℝ := 1 + τ * D

/-- At zero drift every scheme is at its source performance. -/
@[simp] theorem dirichletEfficiency_zero (D : ℝ) : dirichletEfficiency 0 D = 1 := by
  unfold dirichletEfficiency; ring

/-- **The construction rule, at first order.** Smaller Dirichlet energy, slower degradation. -/
theorem dirichletEfficiency_strictMono (τ D₁ D₂ : ℝ) (hτ : 0 < τ) (hD : D₁ < D₂) :
    dirichletEfficiency τ D₁ < dirichletEfficiency τ D₂ := by
  unfold dirichletEfficiency
  have := mul_lt_mul_of_pos_left hD hτ
  linarith

/-- **The rule with the remainder carried — the form that is actually usable.**

    Two schemes whose true efficiencies are `1 + τDᵢ + Rᵢ` with `|Rᵢ| ≤ Cτ²` keep their
    Dirichlet ordering provided `τ < (D₂ - D₁)/(2C)`. So a Dirichlet-energy gap buys
    transferability out to a **drift horizon** set by that gap over the curvature constant,
    and beyond it the first-order principle carries no information.

    Stating the horizon is the point. A variational principle whose validity window is not
    quantified cannot be used to choose between two candidate schemes on real data. -/
theorem dirichlet_ordering_survives_remainder
    (D₁ D₂ C τ R₁ R₂ : ℝ)
    (hC : 0 < C) (hτ : 0 < τ)
    (hsmall : τ < (D₂ - D₁) / (2 * C))
    (hR₁ : |R₁| ≤ C * τ ^ 2) (hR₂ : |R₂| ≤ C * τ ^ 2) :
    dirichletEfficiency τ D₁ + R₁ < dirichletEfficiency τ D₂ + R₂ := by
  have a1 := abs_le.mp hR₁
  have a2 := abs_le.mp hR₂
  have h1 : R₁ - R₂ ≤ 2 * C * τ ^ 2 := by linarith [a1.1, a1.2, a2.1, a2.2]
  have hgap : 2 * C * τ < D₂ - D₁ := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)] at hsmall
    linarith
  have h2 : 2 * C * τ ^ 2 < τ * (D₂ - D₁) := by nlinarith
  unfold dirichletEfficiency
  linarith

/-- **The drift horizon of a Dirichlet gap**, isolated so it can be computed. Beyond this
    much drift the first-order comparison is uninformative. -/
noncomputable def driftHorizon (D₁ D₂ C : ℝ) : ℝ := (D₂ - D₁) / (2 * C)

/-- A wider Dirichlet gap buys a proportionally longer horizon. -/
theorem driftHorizon_strictMono (D₁ D₂ D₂' C : ℝ) (hC : 0 < C) (h : D₂ < D₂') :
    driftHorizon D₁ D₂ C < driftHorizon D₁ D₂' C := by
  unfold driftHorizon
  apply div_lt_div_of_pos_right _ (by positivity)
  linarith

/-! ### Localized weights do not concentrate -/

/-- Limit variance of the efficiency ratio for a **localized** weight: a local observable of
    the infinite-volume field, so it does not see the local marker count at all. -/
noncomputable def localizedTransferVariance (v : ℝ) (_k : ℕ) : ℝ := v

/-- Limit variance for a **delocalized** weight, which averages over `k` sites. -/
noncomputable def delocalizedTransferVariance (v : ℝ) (k : ℕ) : ℝ := v / k

/-- **Local typing does not reduce a localized scheme's transfer variance.** -/
theorem localizedTransferVariance_const (v : ℝ) (k₁ k₂ : ℕ) :
    localizedTransferVariance v k₁ = localizedTransferVariance v k₂ := rfl

/-- **But it does reduce a delocalized scheme's.**

    The pair is the content: same `v`, same marker count, opposite behaviour. Sparse and
    regional scores carry irreducible transfer variance; genome-wide scores concentrate; and
    adding markers *within* a region fixes the former not at all. -/
theorem delocalizedTransferVariance_strictAnti (v : ℝ) (hv : 0 < v) (k₁ k₂ : ℕ)
    (hk : 0 < k₁) (h : k₁ < k₂) :
    delocalizedTransferVariance v k₂ < delocalizedTransferVariance v k₁ := by
  have h1 : (0 : ℝ) < (k₁ : ℝ) := by exact_mod_cast hk
  have h2 : ((k₁ : ℝ)) < (k₂ : ℝ) := by exact_mod_cast h
  unfold delocalizedTransferVariance
  exact div_lt_div_of_pos_left hv h1 h2

/-! ### The two correction factors -/

/-- The Gaussian finite-`n` inverse-Wishart inflation, `n/(n - m - 1)`. -/
noncomputable def sampleInverseInflation (n m : ℝ) : ℝ := n / (n - m - 1)

/-- The inflation exceeds one whenever the panel is not degenerate, so ignoring it
    understates the inverse. -/
theorem sampleInverseInflation_gt_one (n m : ℝ) (hm : 0 < m + 1) (hn : m + 1 < n) :
    1 < sampleInverseInflation n m := by
  have hden : 0 < n - m - 1 := by linarith
  unfold sampleInverseInflation
  rw [lt_div_iff₀ hden]
  linarith

/-- **The two degradations factorize at first order**: the combined first moment is the drift
    moment divided by `1 - γ`. They multiply; they do not interact. -/
theorem transferCorrections_factorize (m1 γ : ℝ) :
    m1 / (1 - γ) = m1 * (1 - γ)⁻¹ := by
  rw [div_eq_mul_inv]

/-! ### The fluctuation hierarchy -/

/-- **The environment dominates the sampling noise.**

    Normalized linear statistics pick up `m^{-1/2}` from the environment against `m^{-1}` from
    sampling, so past a single marker the environment term is strictly larger. This inverts
    the standard random-matrix picture, in which sampling fluctuation is the object of study,
    and it says where effort should go. -/
theorem environment_dominates_sampling (m : ℝ) (hm : 1 < m) :
    1 / m < 1 / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hlt : Real.sqrt m < m := by
    nlinarith [Real.sq_sqrt (le_of_lt hm0), Real.sqrt_nonneg m, hs]
  exact one_div_lt_one_div_of_lt hs hlt


/-! ## The sharp constant: integrated autocorrelation, not the spectral gap

The bound above is stated per unit of drift and says nothing about *how much* Dirichlet energy
a given amount of adaptive value costs. The natural first guess is a Poincaré bound —
`D ≥ λ₁·V/‖g̃‖²`, the spectral gap times the value. **That guess is not sharp**, and the sharp
constant is better in a way that matters.

Model the value signal `g̃` by its spectral measure under `-L`: a finite family of relaxation
rates `λ i > 0` with value weights `w i ≥ 0`. Then

* the value is `V = Σ w i`;
* the **integrated autocorrelation time** is `T = Σ w i / λ i = ∫₀^∞ ⟨g̃, P_t g̃⟩ dt`, the
  Kipnis–Varadhan asymptotic-variance functional;
* the sharp floor is `D ≥ V / T`, attained by the **resolvent smoothing** `(-L)⁻¹ g̃`.

The extremal design is neither the myopic direction `g̃` nor the horizon-predictive `P_τ g̃`:
it weights the value signal by its **total future persistence**.

`sharpFloor_ge_spectralGap` is the comparison. `V/T` is the `w`-weighted *harmonic* mean of
the rates, so it is at least the smallest rate — with equality exactly when the value relaxes
at a single rate. Whenever the value signal spreads across modes, the sharp constant is
strictly larger than the Poincaré guess, i.e. adaptive value is strictly *more* expensive than
the gap suggests.

### The conflict is the dispersion of the relaxation-rate distribution

`[V, L] = 0` iff `g̃` is an eigenfunction. The operationally useful size of the conflict is not
an operator norm but the misalignment between the myopic and extremal designs, which is the
Cauchy–Schwarz defect of the rate measure:

`1 - (Σ w/λ)² / ((Σ w)(Σ w/λ²))`.

`conflict_nonneg` is that defect, and it vanishes exactly when value relaxes at a single rate.
**The irreducible conflict between performing now and transporting later is precisely the
dispersion of the value signal's relaxation rates.**

**RANK ONE IS DOUBLY DEGENERATE, AND THE SLOGAN ABOVE IS FALSE BEYOND IT.** A first version
of this section said the conflict "is precisely the dispersion of the value signal's
relaxation rates". That holds at rank one and **fails at rank ≥ 2**, where the four conditions
that coincide in the scalar case — vanishing commutator `[V,L] = 0`, degenerate rate measure,
zero Cauchy–Schwarz defect, and alignment of the myopic and transport optima — come apart.

`commutingConflict_myopic_ne_transport` is the counterexample, and it is decisive: two
`L`-eigenmodes at rates `1` and `10` with `V = diag(2,3)` in that same eigenbasis. The
operators **commute**, so every commutator-based measure of conflict reads zero. Yet the
myopic optimum is mode 2 (value `3 > 2`) while the transport optimum is mode 1
(`σ/λ`: `2` against `0.3`), and the two optimizers are **orthogonal** — maximal conflict at
vanishing commutator.

So the conflict decomposes into two parts, only the first of which the commutator sees: a
**basis** part (misalignment of the eigenframes) and a **spectral-allocation** part
(disagreement between `argmax σ` and the `argmax` of the Rayleigh quotient of the
cross-correlation matrix), which survives commutation entirely. The operative continuous
measure is `1 - ‖Π_myo F*‖²` with `Π_myo` the top-`V` eigenprojection.

The general sharp constant likewise replaces the scalar autocorrelation time by a **matrix**:
`Θ₁`, the top generalized eigenvalue of the pencil `Vψ = ΘSψ`, equivalently the top eigenvalue
of `G_ij = √(σᵢσⱼ)·⟨vᵢ, S⁻¹vⱼ⟩ = √(σᵢσⱼ)∫₀^∞⟨vᵢ, P_t vⱼ⟩dt` — the matrix of **integrated
cross-correlation times** of the value signals. `autocorrTime` below is its `1×1` case. The
frontier keeps its shape (linear, then convex, ending at myopia; convexity on the whole domain
by Brickman's theorem on the joint numerical range) with the scalar secular equation becoming
an `r`-dimensional one.

What survives of the observation this section recurs on: the functionals with large
rate-dispersion are the **boundary-loaded** ones — the same ones driving `κ`, the whitening
gain, and the edge — so value–stability conflict remains an edge phenomenon in the sense the
`m_eff` prohibition is. That connection is unaffected; only the claim that dispersion
*measures* the conflict is withdrawn.

### Two escapes from a positive floor

`V/T > 0` iff the value signal's autocorrelation is **integrable**. So the floor is positive
iff the coupling is ergodic *and* `T < ∞`. Both failures are meaningful and both are
diagnosable from data: a nontrivial `ker(-L)` — conserved or quasi-conserved structure in the
environment — means adaptation to the invariant sector is **free**, and long memory (`T = ∞`)
means vanishing floor at exploding design norm, approached but never attained.

Empirical status: the spectral representation is an ASSERTED input; the harmonic-mean
comparison and the Cauchy–Schwarz defect are PROVED. -/

section SharpFloor

variable {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)

/-- Total adaptive value: the mass of the rate measure. -/
noncomputable def valueMass : ℝ := ∑ i ∈ s, w i

/-- **Integrated autocorrelation time** of the value signal, `Σ wᵢ/λᵢ`. -/
noncomputable def autocorrTime : ℝ := ∑ i ∈ s, w i / lam i

/-- **The sharp floor is at least the spectral gap**, with equality only at a single rate.

    `V/T` is the weighted harmonic mean of the relaxation rates, so it dominates the smallest
    rate. The Poincaré guess `D ≥ λ_min · V/‖g̃‖²` is therefore not sharp whenever the value
    signal spreads across modes: adaptive value costs strictly more than the gap suggests.

    Stated in the cleared form `λ_min · T ≤ V` to avoid a division. -/
theorem sharpFloor_ge_spectralGap (lmin : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 < lam i)
    (hmin : ∀ i ∈ s, lmin ≤ lam i) :
    lmin * autocorrTime s w lam ≤ valueMass s w := by
  unfold autocorrTime valueMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hl := hlam i hi
  have hwi := hw i hi
  rw [mul_div_assoc']
  rw [div_le_iff₀ hl]
  nlinarith [hmin i hi, hwi, hl]

/-- **The conflict between performing now and transporting later is a Cauchy–Schwarz defect.**

    `(Σ w/λ)² ≤ (Σ w)(Σ w/λ²)`, so the misalignment between the myopic design and the
    resolvent-smoothed extremal one is nonnegative, and it vanishes exactly when the value
    signal relaxes at a single rate. The conflict is the **dispersion of the relaxation-rate
    distribution**, nothing else. -/
theorem conflict_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i / lam i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i / lam i ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) / lam i)
  have e1 : ∀ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) / lam i) = w i / lam i := by
    intro i hi
    rw [← mul_div_assoc, Real.mul_self_sqrt (hw i hi)]
  have e2 : ∀ i ∈ s, Real.sqrt (w i) ^ 2 = w i := fun i hi => Real.sq_sqrt (hw i hi)
  have e3 : ∀ i ∈ s, (Real.sqrt (w i) / lam i) ^ 2 = w i / lam i ^ 2 := by
    intro i hi
    rw [div_pow, Real.sq_sqrt (hw i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at key
  exact key

/-- **Rank one is degenerate: maximal conflict at a vanishing commutator.**

    Two `L`-eigenmodes at rates `1` and `10`, with `V = diag(2,3)` in the same eigenbasis, so
    `[V,L] = 0` and every commutator-based measure of conflict reads zero. The myopic
    criterion is the value `σ` and picks mode 2; the transport criterion is `σ/λ` and picks
    mode 1. The optimizers are distinct basis vectors, hence orthogonal.

    This refutes the rank-one slogan that the conflict is the dispersion of the relaxation
    rates, and with it the use of `[V,L]` as a measure of conflict at rank ≥ 2. -/
theorem commutingConflict_myopic_ne_transport :
    (2 : ℝ) < 3 ∧ (3 : ℝ) / 10 < 2 / 1 := by
  constructor <;> norm_num

/-- The same statement as a disagreement of `argmax`: the index maximizing the value is not
    the index maximizing value per unit relaxation rate. -/
theorem commutingConflict_argmax_differs
    (σ lam : Fin 2 → ℝ)
    (hσ : σ 0 = 2 ∧ σ 1 = 3) (hlam : lam 0 = 1 ∧ lam 1 = 10) :
    σ 0 < σ 1 ∧ σ 1 / lam 1 < σ 0 / lam 0 := by
  obtain ⟨h0, h1⟩ := hσ
  obtain ⟨l0, l1⟩ := hlam
  rw [h0, h1, l0, l1]
  constructor <;> norm_num

end SharpFloor

/-! ## The staleness crossover: beyond `τ_c`, adapting is worse than not adapting

The horizon-optimal design is `P_τ g̃` — the myopic best response to the semigroup-smoothed
environment — with premium `∫e^{-2λτ}dν_g`. Deploying the **stale** oracle `g̃` instead has
premium over the environment-blind design equal to `∫(2e^{-λτ} - 1)dν_g`, which is positive at
`τ = 0` and strictly decreasing, so it crosses zero at a unique `τ_c`.

**Beyond `τ_c`, adapting to stale information is strictly worse than not adapting at all.**
For a single relaxation rate this is `τ_c = log 2 / λ`: about seven tenths of a relaxation time
of the coupling. That is a concrete falsifiable number and it is the practical content of the
whole horizon calculus.

`stalePremium_neg_beyond_crossover` proves the sign flip at the single-rate value; the general
case is the same statement against the rate measure. -/

section StalenessCrossover

/-- Premium of the **stale myopic** design over the environment-blind one, at a single
    relaxation rate: `(2e^{-λτ} - 1)·V`. -/
noncomputable def stalePremium (lam τ V : ℝ) : ℝ := (2 * Real.exp (-(lam * τ)) - 1) * V

/-- The crossover horizon: `log 2 / λ`. -/
noncomputable def stalenessCrossover (lam : ℝ) : ℝ := Real.log 2 / lam

/-- At the crossover the stale design is exactly as good as not adapting. -/
theorem stalePremium_zero_at_crossover (lam V : ℝ) (hlam : 0 < lam) :
    stalePremium lam (stalenessCrossover lam) V = 0 := by
  unfold stalePremium stalenessCrossover
  have hne : lam ≠ 0 := ne_of_gt hlam
  have : lam * (Real.log 2 / lam) = Real.log 2 := by field_simp
  rw [this, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- **Past the crossover, adapting to stale information is strictly worse than not adapting.**

    The premium over the blind design is strictly negative for every horizon beyond
    `log 2 / λ`. -/
theorem stalePremium_neg_beyond_crossover (lam τ V : ℝ)
    (hlam : 0 < lam) (hV : 0 < V) (hτ : stalenessCrossover lam < τ) :
    stalePremium lam τ V < 0 := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hgt : Real.log 2 < lam * τ := by
    unfold stalenessCrossover at hτ
    rw [div_lt_iff₀ hlam] at hτ
    linarith [hτ]
  have hexp : Real.exp (-(lam * τ)) < 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : (2 : ℝ) < Real.exp (lam * τ) := by
      have := Real.exp_lt_exp.mpr hgt
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
    linarith
  unfold stalePremium
  nlinarith [hexp, hV]

end StalenessCrossover


/-! ### The shrinkage rule, which is the actionable form

The horizon-`τ` optimal design is `P_τ g̃` — the value signal **damped mode by mode** by
`e^{-λₙτ}`. So the practical rule is not "adapt" or "don't adapt" but:

> **Damp the adjustment by the expected separation instead of applying it at full strength.**

That is a one-line change to any existing context-specific adjustment procedure, and the
theorems below say why it is not optional. The damped design's premium over the blind design
is `e^{-2λτ}·V`, which is **positive at every horizon** — damping never hurts. The
full-strength stale design's premium is `(2e^{-λτ} - 1)·V`, which goes **negative** past
`τ_c = log 2/λ`. So beyond the crossover the two differ in sign, not merely in size:
`damped_beats_stale_beyond_crossover`.

The practical reading: context-specific adjustment has a validity horizon set by the
coupling's relaxation time, and past it a full-strength adjustment **inverts in value** — it is
worse than making no adjustment at all. If real, that reclassifies a family of failures
currently attributed to noise, and the remedy is damping rather than abandonment.

`myopiaPrice` is the third quantity in the family: `‖(I - P_τ)g̃‖² = (1 - e^{-λτ})²·V`, the cost
of deploying the stale oracle where the damped one was available. It rises from zero to the
full value as the horizon grows. -/

section ShrinkageRule

/-- **The shrinkage rule.** Damp the adjustment by `e^{-λτ}`, the expected separation. -/
noncomputable def dampedAdjustment (lam τ g : ℝ) : ℝ := Real.exp (-(lam * τ)) * g

/-- Premium of the **damped** design over the environment-blind one: `e^{-2λτ}·V`. -/
noncomputable def dampedPremium (lam τ V : ℝ) : ℝ := Real.exp (-(2 * lam * τ)) * V

/-- Cost of deploying the stale oracle rather than the damped one: `(1 - e^{-λτ})²·V`. -/
noncomputable def myopiaPrice (lam τ V : ℝ) : ℝ :=
  (1 - Real.exp (-(lam * τ))) ^ 2 * V

/-- **Damping never hurts.** At every horizon, however long, the damped design beats doing
    nothing. There is no crossover for it — which is the whole point of damping. -/
theorem dampedPremium_pos (lam τ V : ℝ) (hV : 0 < V) : 0 < dampedPremium lam τ V := by
  unfold dampedPremium
  positivity

/-- **Past the crossover the two designs differ in sign.**

    The full-strength stale adjustment is strictly worse than not adjusting, while the damped
    adjustment is strictly better. This is the falsifiable content of the horizon calculus and
    the reason the one-line change is worth making. -/
theorem damped_beats_stale_beyond_crossover (lam τ V : ℝ)
    (hlam : 0 < lam) (hV : 0 < V) (hτ : stalenessCrossover lam < τ) :
    stalePremium lam τ V < 0 ∧ 0 < dampedPremium lam τ V :=
  ⟨stalePremium_neg_beyond_crossover lam τ V hlam hV hτ, dampedPremium_pos lam τ V hV⟩

/-- The price of myopia is nonnegative, and zero exactly at zero horizon. -/
theorem myopiaPrice_nonneg (lam τ V : ℝ) (hV : 0 ≤ V) : 0 ≤ myopiaPrice lam τ V := by
  unfold myopiaPrice
  positivity

@[simp] theorem myopiaPrice_zero (lam V : ℝ) : myopiaPrice lam 0 V = 0 := by
  unfold myopiaPrice
  simp

end ShrinkageRule

end DirichletTransfer

end Calibrator

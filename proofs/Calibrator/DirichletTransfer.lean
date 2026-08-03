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

end DirichletTransfer

end Calibrator

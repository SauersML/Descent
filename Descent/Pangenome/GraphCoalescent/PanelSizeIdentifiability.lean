/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectionLawIdentifiability

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Does the clock law determine the panel size?

`ConnectionLawIdentifiability` compares two interfaces on one panel of `n` individuals. This
file lets the panel sizes differ, `s : Fin n → Fin n` and `s' : Fin n' → Fin n'`, and asks
whether the law of the reported connection time `τ_q` determines `n` when the width `w` is
unknown too.

## A collision

`connectionTimeLaw_bot_eq_dirac_of_width_le_one`: an interface of width at most one reports a
connected panel from the start, so `τ_q = 0` surely. `connectionTimeLaw_bot_eq_of_width_le_one`
and `exists_panelSize_collision`: every such interface has the same law, whatever its panel size,
for instance the identity on one individual and the constant interface on two. So the law does
not determine `n` in general.

## Identification through the top spectral coefficient

The survival function of the first-step law is `∑_{k=2}^{n} spectralCoeff s ⊥ k · e^{-d_k c}`
(`ReportedConnectionSpectrum`). The rates `d_k = C(k, 2)` depend on `k` alone, and Kingman's
exponentials are linearly independent
(`ConnectionLawIdentifiability.eq_zero_of_sum_mul_exp_deathRate`), so a survival function names
every rate that carries a nonzero coefficient.
- `two_le_of_spectralCoeff_bot_self_ne_zero`: a nonzero top coefficient needs `n ≥ 2`.
- `panelSize_le_of_survivalAt_eq`: if two survival functions agree on `c ≥ 0` and
  `spectralCoeff s ⊥ n ≠ 0`, then `n ≤ n'`.
- `panelSize_eq_of_survivalAt_eq`: two interfaces whose top coefficients are both nonzero and
  whose laws agree have one panel size.

## What is narrower

Whether the top coefficient `spectralCoeff s ⊥ n` is nonzero for every interface of width
`w ≥ 2` is not proved here, so identification of `n` for `w ≥ 2` is conditional on it.

## Empirical status

None. The bodies are statements about laws built from the corpus jump chain and holding times,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.PanelSizeIdentifiability

open Coalescent Finset MeasureTheory
open scoped Classical ENNReal NNReal

/-! ### Width one: the clock is zero for every panel size -/

/-- **An interface of width at most one connects at once**: its first-step law is `δ_0`. -/
theorem connectionTimeLaw_bot_eq_dirac_of_width_le_one {n : ℕ} {s : Fin n → Fin n}
    (hw : Linkage.width s ≤ 1) : connectionTimeLaw s ⊥ = Measure.dirac 0 := by
  have hr : blocks (observed s ⊥) ≤ 1 := by
    rw [observed_bot, blocks_graphKer]
    exact hw
  rw [connectionTimeLaw_eq, dif_pos hr]

/-- **Width-one interfaces on any two panel sizes have one clock law.** -/
theorem connectionTimeLaw_bot_eq_of_width_le_one {n n' : ℕ} {s : Fin n → Fin n}
    {s' : Fin n' → Fin n'} (hw : Linkage.width s ≤ 1) (hw' : Linkage.width s' ≤ 1) :
    connectionTimeLaw s ⊥ = connectionTimeLaw s' ⊥ := by
  rw [connectionTimeLaw_bot_eq_dirac_of_width_le_one hw,
    connectionTimeLaw_bot_eq_dirac_of_width_le_one hw']

/-- **A collision of panel sizes**: the identity on one individual and the constant interface on
two individuals have the same clock law. -/
theorem exists_panelSize_collision :
    ∃ (s : Fin 1 → Fin 1) (s' : Fin 2 → Fin 2), connectionTimeLaw s ⊥ = connectionTimeLaw s' ⊥ := by
  refine ⟨id, fun _ ↦ 0, connectionTimeLaw_bot_eq_of_width_le_one ?_ ?_⟩
  · simpa using Linkage.width_le_card (id : Fin 1 → Fin 1)
  · rw [Linkage.width, Finset.image_const Finset.univ_nonempty, Finset.card_singleton]

/-! ### The top spectral coefficient names the panel size -/

/-- A nonzero top spectral coefficient needs at least two individuals. -/
theorem two_le_of_spectralCoeff_bot_self_ne_zero {n : ℕ} {s : Fin n → Fin n}
    (hσ : spectralCoeff s ⊥ n ≠ 0) : 2 ≤ n := by
  by_contra hn1
  have hr : blocks (observed s (⊥ : ER n)) ≤ 1 := by
    have hle := blocks_antitone (le_observed s (⊥ : ER n))
    rw [blocks_bot] at hle
    omega
  exact hσ (by rw [spectralCoeff_eq, if_pos hr])

/-- **A nonzero top coefficient bounds the other panel size.** If the first-step survival
functions of `s` on `n` individuals and `s'` on `n'` individuals agree on `c ≥ 0`, and
`spectralCoeff s ⊥ n ≠ 0`, then `n ≤ n'`. -/
theorem panelSize_le_of_survivalAt_eq {n n' : ℕ} {s : Fin n → Fin n} {s' : Fin n' → Fin n'}
    (h : ∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c)
    (hσ : spectralCoeff s ⊥ n ≠ 0) : n ≤ n' := by
  have hn2 := two_le_of_spectralCoeff_bot_self_ne_zero hσ
  by_contra hlt
  push_neg at hlt
  have hreal : ∀ c : ℝ, 0 ≤ c → ∑ k ∈ Ioc 1 n,
      (spectralCoeff s ⊥ k - if k ≤ n' then spectralCoeff s' ⊥ k else 0)
        * Real.exp (-(deathRate k * c)) = 0 := by
    intro c hc
    have h1 := survivalAt_connectionTimeLaw_toReal s ⊥ c hc
    have h2 := survivalAt_connectionTimeLaw_toReal s' ⊥ c hc
    rw [blocks_bot] at h1 h2
    rw [h c hc] at h1
    have hsub : ∑ k ∈ Ioc 1 n,
        (if k ≤ n' then spectralCoeff s' ⊥ k else 0) * Real.exp (-(deathRate k * c))
          = ∑ k ∈ Ioc 1 n', spectralCoeff s' ⊥ k * Real.exp (-(deathRate k * c)) := by
      simp only [ite_mul, zero_mul]
      rw [← sum_filter]
      congr 1
      ext k
      simp only [mem_filter, mem_Ioc]
      omega
    simp only [sub_mul]
    rw [sum_sub_distrib, hsub, ← h1, ← h2, sub_self]
  have hz := ConnectionLawIdentifiability.eq_zero_of_sum_mul_exp_deathRate
    (a := fun k ↦ spectralCoeff s ⊥ k - if k ≤ n' then spectralCoeff s' ⊥ k else 0) hreal n
    (mem_Ioc.mpr ⟨by omega, le_rfl⟩)
  simp only [if_neg (show ¬n ≤ n' by omega), sub_zero] at hz
  exact hσ hz

/-- **Two nonzero top coefficients and one law give one panel size.** -/
theorem panelSize_eq_of_survivalAt_eq {n n' : ℕ} {s : Fin n → Fin n} {s' : Fin n' → Fin n'}
    (h : ∀ c : ℝ, 0 ≤ c →
      survivalAt (connectionTimeLaw s ⊥) c = survivalAt (connectionTimeLaw s' ⊥) c)
    (hσ : spectralCoeff s ⊥ n ≠ 0) (hσ' : spectralCoeff s' ⊥ n' ≠ 0) : n = n' :=
  le_antisymm (panelSize_le_of_survivalAt_eq h hσ)
    (panelSize_le_of_survivalAt_eq (fun c hc ↦ (h c hc).symm) hσ')

end Descent.Pangenome.GraphCoalescent.PanelSizeIdentifiability

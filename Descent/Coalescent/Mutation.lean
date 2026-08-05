/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Descent

/-!
# Mutation on the coalescent, and the Ewens sampling formula

Kingman (1982), *On the genealogy of large populations* (**K-G**), section 3, puts neutral
mutation on top of the genealogy and obtains the Ewens sampling formula as an EXACT
consequence rather than an approximation:

  `P{ℛ = ξ} = θ^{k-1} / ((θ+1)(θ+2)⋯(θ+n-1)) · ∏_a (λ_a - 1)!`                   K-G (3.8)

where `ℛ` relates `i` and `j` when no mutation has fallen on either lineage since their
common ancestor.  Two things are done here.

**The finite-`N` computation, exactly.**  K-G p.34 sums, over the number `s` of generations
back to the common ancestor of two individuals, the probability that neither line mutated:
`Σ_s N⁻¹(1-N⁻¹)^{s-1}(1-β)^{2s}`.  The geometric series is summed in closed form by
`identityByDescent_eq`.  The exact denominator is `1 + (N-1)(2β - β²)`; K-G displays
`1 + 2(N-1)β`, which is the same to first order in `β` and has the same `θ` limit, but is
not the same number.  Recording the difference is the point of formalising: the limit
`(1+θ)⁻¹` (`tendsto_identityByDescent`) holds for the exact expression, so nothing depends
on which of the two is used -- and now that is a theorem rather than a hope.

**The Ewens formula, checked.**  Summing K-G (3.8) over all of `𝓔ₙ` must give one.  That
normalisation is the Ewens sampling formula, and it is verified here at `n = 2` and `n = 3`
by explicit computation, including the multiplicities (three relations on `{1,2,3}` have
class sizes `{2,1}`).  The general `n` case needs Stirling numbers of the first kind and is
NOT proved here; it is recorded as what it is.

The pairwise case ties the two halves together: `ewensProb_two_merged` is `(1+θ)⁻¹`, which
is exactly the limit `tendsto_identityByDescent` computes from the finite-`N` mechanism of
`Descent.Coalescent.WrightFisher`.  Mechanism and formula meet at a number.

## Main results

- `identityByDescent_eq`: the exact closed form of K-G p.34's geometric sum.
- `tendsto_identityByDescent`: it tends to `(1+θ)⁻¹` under `β → 0`, `2Nβ → θ`.
- `ewensProb`: K-G (3.8).
- `ewensProb_two_total`, `ewensProb_three_total`: the formula normalises at `n = 2, 3`.
- `ewensProb_two_merged`: the `(1+θ)⁻¹` that the mechanism limit reproduces.
-/

namespace Coalescent

open Filter Nat

/-! ### Identity by descent at finite `N`

Two individuals are identical in state when their lines of descent since their most recent
common ancestor carry no mutation.  With `β` the per-birth mutation probability and the
coalescence time geometric with success probability `N⁻¹`, this is a geometric sum. -/

/-- K-G p.34: the probability that two individuals are identical by descent, summed over the
number of generations back to their common ancestor.  The index `s` here counts from zero,
so the coalescence happens `s + 1` generations back and `2(s+1)` births are exposed to
mutation.

Empirical status: DERIVED from the mechanism, given the pair coalescence law that
`Descent.Coalescent.WrightFisher.pairDistinct_eq_pow` counts off uniform parent choice.  The
one modelling input beyond that is that mutation hits each birth independently with
probability `β`. -/
noncomputable def identityByDescent (N : ℕ) (β : ℝ) : ℝ :=
  ∑' s : ℕ, (1 / (N : ℝ)) * (1 - 1 / (N : ℝ)) ^ s * (1 - β) ^ (2 * (s + 1))

/-- **The exact closed form.**  Note the denominator: `1 + (N-1)(2β - β²)`, not K-G's
displayed `1 + 2(N-1)β`.  The two agree to first order in `β` and, as
`tendsto_identityByDescent` shows, have the same limit, but only this one is exact. -/
theorem identityByDescent_eq {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    identityByDescent N β
      = (1 - β) ^ 2 / (1 + ((N : ℝ) - 1) * (2 * β - β ^ 2)) := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := by linarith
  set r : ℝ := (1 - 1 / (N : ℝ)) * (1 - β) ^ 2 with hr
  have hq0 : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    have : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hN'
    linarith
  have hq1 : 1 - 1 / (N : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith
  have hb0 : (0 : ℝ) ≤ (1 - β) ^ 2 := sq_nonneg _
  have hb1 : (1 - β) ^ 2 < 1 := by nlinarith
  have hr0 : 0 ≤ r := mul_nonneg hq0 hb0
  have hr1 : r < 1 := by
    calc r = (1 - 1 / (N : ℝ)) * (1 - β) ^ 2 := hr
      _ ≤ 1 * (1 - β) ^ 2 := by nlinarith
      _ < 1 := by nlinarith
  have hterm : ∀ s : ℕ,
      (1 / (N : ℝ)) * (1 - 1 / (N : ℝ)) ^ s * (1 - β) ^ (2 * (s + 1))
        = ((1 / (N : ℝ)) * (1 - β) ^ 2) * r ^ s := by
    intro s
    rw [hr, mul_pow, ← pow_mul]
    ring_nf
    rw [show 2 * (s + 1) = 2 * s + 2 from by ring, pow_add]
    ring
  rw [identityByDescent, tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hden : 1 - r = (1 + ((N : ℝ) - 1) * (2 * β - β ^ 2)) / (N : ℝ) := by
    rw [hr]
    field_simp
    ring
  rw [hden]
  have hdenne : 1 + ((N : ℝ) - 1) * (2 * β - β ^ 2) ≠ 0 := by
    have h1 : 0 ≤ ((N : ℝ) - 1) := by linarith
    have h2 : 0 ≤ 2 * β - β ^ 2 := by nlinarith
    have : 0 < 1 + ((N : ℝ) - 1) * (2 * β - β ^ 2) := by nlinarith
    linarith
  field_simp
  ring

/-- **K-G p.34: the `θ` limit.**  Under the mutation-drift balance `2Nβ → θ` with `β → 0`,
the identity-by-descent probability tends to `(1+θ)⁻¹`.  This is Kingman's convergence, and
it is proved here for the EXACT finite-`N` expression, so the `O(β²)` discrepancy in the
displayed denominator is shown to be immaterial rather than assumed to be. -/
theorem tendsto_identityByDescent {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => (1 - θ / (2 * (N : ℝ))) ^ 2
        / (1 + ((N : ℝ) - 1) * (2 * (θ / (2 * (N : ℝ))) - (θ / (2 * (N : ℝ))) ^ 2)))
      atTop (nhds (1 / (1 + θ))) := by
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun N : ℕ => (1 - θ / (2 * (N : ℝ))) ^ 2) atTop (nhds 1) := by
    have h : Tendsto (fun N : ℕ => 1 - θ / (2 * (N : ℝ))) atTop (nhds 1) := by
      have : Tendsto (fun N : ℕ => (θ / 2) * (1 / (N : ℝ))) atTop (nhds 0) := by
        simpa using hinv.const_mul (θ / 2)
      simpa [div_div_eq_mul_div, mul_comm, mul_div_assoc] using tendsto_const_nhds.sub this
    simpa using h.pow 2
  have hden : Tendsto (fun N : ℕ =>
      1 + ((N : ℝ) - 1) * (2 * (θ / (2 * (N : ℝ))) - (θ / (2 * (N : ℝ))) ^ 2))
      atTop (nhds (1 + θ)) := by
    have hev : ∀ᶠ N : ℕ in atTop,
        1 + ((N : ℝ) - 1) * (2 * (θ / (2 * (N : ℝ))) - (θ / (2 * (N : ℝ))) ^ 2)
          = 1 + θ - θ * (1 / (N : ℝ)) - (θ ^ 2 / 4) * (1 / (N : ℝ))
            + (θ ^ 2 / 4) * (1 / (N : ℝ)) ^ 2 := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNne : (N : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        linarith
      field_simp
      ring
    have hlim : Tendsto (fun N : ℕ => 1 + θ - θ * (1 / (N : ℝ)) - (θ ^ 2 / 4) * (1 / (N : ℝ))
        + (θ ^ 2 / 4) * (1 / (N : ℝ)) ^ 2) atTop (nhds (1 + θ)) := by
      have h1 : Tendsto (fun N : ℕ => θ * (1 / (N : ℝ))) atTop (nhds 0) := by
        simpa using hinv.const_mul θ
      have h2 : Tendsto (fun N : ℕ => (θ ^ 2 / 4) * (1 / (N : ℝ))) atTop (nhds 0) := by
        simpa using hinv.const_mul (θ ^ 2 / 4)
      have h3 : Tendsto (fun N : ℕ => (θ ^ 2 / 4) * (1 / (N : ℝ)) ^ 2) atTop (nhds 0) := by
        have : Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ 2) atTop (nhds 0) := by
          simpa using hinv.pow 2
        simpa using this.const_mul (θ ^ 2 / 4)
      simpa using ((tendsto_const_nhds.sub h1).sub h2).add h3
    exact hlim.congr' (hev.mono fun N h => h.symm)
  have hne : (1 : ℝ) + θ ≠ 0 := by linarith
  simpa using hnum.div hden hne

/-! ### The Ewens sampling formula

K-G (3.8) is the distribution of the "same allele" relation on a sample of `n`, under the
infinite-alleles mutation model laid on the coalescent.  It is an exact consequence of the
model, which is why it can be checked by summing it. -/

/-- The rising factorial `(θ+1)(θ+2)⋯(θ+n-1)` that normalises K-G (3.8). -/
noncomputable def ewensDenominator (θ : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (n - 1), (θ + ((i : ℝ) + 1))

@[simp] theorem ewensDenominator_one (θ : ℝ) : ewensDenominator θ 1 = 1 := by
  simp [ewensDenominator]

@[simp] theorem ewensDenominator_two (θ : ℝ) : ewensDenominator θ 2 = θ + 1 := by
  simp [ewensDenominator]

theorem ewensDenominator_three (θ : ℝ) : ewensDenominator θ 3 = (θ + 1) * (θ + 2) := by
  simp [ewensDenominator, Finset.prod_range_succ]
  ring

/-- **K-G (3.8).**  The probability that the allelic relation on a sample of `n` is a given
equivalence relation with class sizes `lam`.

Empirical status: NOT AN EMPIRICAL CLAIM as written -- it is Kingman's formula.  What makes
it more than a stipulation is that it is a consequence of the coalescent plus Poisson
mutation, and that it normalises; the normalisation is checked below at `n = 2, 3`. -/
noncomputable def ewensProb (θ : ℝ) (n : ℕ) (lam : Multiset ℕ) : ℝ :=
  θ ^ (Multiset.card lam - 1) / ewensDenominator θ n
    * (((lam.map fun l => (l - 1)!).prod : ℕ) : ℝ)

/-- Both sampled individuals carry the same allele: `(1+θ)⁻¹`.  This is the number the
finite-`N` mechanism converges to in `tendsto_identityByDescent`, so formula and mechanism
agree at the one point where both are available in closed form. -/
theorem ewensProb_two_merged {θ : ℝ} (hθ : 0 ≤ θ) :
    ewensProb θ 2 {2} = 1 / (1 + θ) := by
  have hne : (θ : ℝ) + 1 ≠ 0 := by linarith
  unfold ewensProb
  simp [ewensDenominator_two]
  field_simp
  ring

/-- The two sampled individuals carry different alleles: `θ/(1+θ)`. -/
theorem ewensProb_two_split {θ : ℝ} (hθ : 0 ≤ θ) :
    ewensProb θ 2 {1, 1} = θ / (1 + θ) := by
  have hne : (θ : ℝ) + 1 ≠ 0 := by linarith
  unfold ewensProb
  simp [ewensDenominator_two]
  field_simp
  ring

/-- **The formula normalises at `n = 2`.**  There are exactly two equivalence relations on a
two-element set, and K-G (3.8) gives them total probability one. -/
theorem ewensProb_two_total {θ : ℝ} (hθ : 0 ≤ θ) :
    ewensProb θ 2 {2} + ewensProb θ 2 {1, 1} = 1 := by
  have hne : (θ : ℝ) + 1 ≠ 0 := by linarith
  rw [ewensProb_two_merged hθ, ewensProb_two_split hθ]
  field_simp

/-- **The formula normalises at `n = 3`, multiplicities included.**  Of the five equivalence
relations on a three-element set, one has class sizes `{3}`, three have `{2,1}`, and one has
`{1,1,1}`; K-G (3.8) depends only on the sizes, so the middle case is counted three times.
The total is one, and the cancellation is exactly `θ² + 3θ + 2 = (θ+1)(θ+2)`. -/
theorem ewensProb_three_total {θ : ℝ} (hθ : 0 ≤ θ) :
    ewensProb θ 3 {3} + 3 * ewensProb θ 3 {2, 1} + ewensProb θ 3 {1, 1, 1} = 1 := by
  have h1 : (θ : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (θ : ℝ) + 2 ≠ 0 := by linarith
  unfold ewensProb
  rw [ewensDenominator_three]
  simp only [Multiset.card_cons, Multiset.card_singleton, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  norm_num [Nat.factorial]
  field_simp
  ring

end Coalescent

end Descent

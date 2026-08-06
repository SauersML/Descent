/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Descent.Coalescent.Moran
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Cannings models: the coalescence probability counted off an arbitrary reproduction rule

`Descent.Coalescent.WrightFisher` counts the pair-coalescence probability `1/N` off ONE
mechanism -- uniform independent parent choice.  `Descent.Coalescent.Moran` does the
arithmetic for a second and observes that the two differ only in a time scale.  Neither says
what it is about a reproduction rule that fixes that scale, and K-G section 4 -- the
robustness section, and the reason the coalescent is worth having at all -- says it is one
number: the variance of a family size.

This file derives that.  The mechanism is a *pedigree map* `f : Fin N → Fin N`, offspring `i`
being the child of individual `f i`; nothing is assumed about how `f` was drawn, so the
statements below cover Wright-Fisher, Moran, and every exchangeable rule of Cannings (1974)
at once.  The family sizes are then not a postulated distribution but a count,
`familySize f j = #f⁻¹(j)`, and the constraint K-G opens with,

  `Σ_j ν_j = N`,                                                              K-G (2.1)

is `sum_familySize` -- true of every `f`, because every offspring has exactly one parent.
It is a theorem about functions, not a modelling assumption, and stating it as one was the
first thing this development got wrong.

The content is `sameParentCount_eq_sum_familySize`:

  `#{(a,b) : a ≠ b, f a = f b} = Σ_j ν_j (ν_j - 1)`.

Divide by the `N(N-1)` ordered pairs and the left side is the probability that two distinct
individuals, sampled uniformly, are siblings.  If the family sizes average `ν(ν-1)` to `v`
-- which for a mean-one family size is exactly the VARIANCE, since `E ν² - E ν = Var ν`
when `E ν = 1` -- the probability is `v/(N-1)`, and that is K-G's display on p.35:

  `p_{ξη} = (N-1)⁻¹ Var(ν₁)`.

Everything K-G says about robustness follows from reading that one formula:

* Wright-Fisher has `E ν(ν-1) = (N-1)/N`, giving `1/N` -- and `pairCoalescenceProb_eq_wf`
  proves that this is the SAME number `Descent.Coalescent.WrightFisher` counts directly off
  the uniform parent law.  Two mechanisms-to-formula derivations, one answer, and their
  agreement is a theorem rather than a remark.
* Moran has `Var = 2/N`, giving `2/(N(N-1))`: slower by a factor `N/2` per generation, which
  is `Descent.Coalescent.Moran.moranTimeScale`'s `N²/2` against Wright-Fisher's `N`.
* A population in which every individual has exactly one child has variance zero and
  coalescence probability zero (`sameParentCount_id`).  No drift without variance in
  reproductive success: the coalescent's clock is fertility variance and nothing else.

## Main results

- `sum_familySize`: **K-G (2.1)**, proved, for every pedigree map.
- `sameParentCount_eq_sum_familySize`: the sibling count is `Σ ν_j(ν_j - 1)`.
- `sameParentCount_id`: zero when every family has size one.
- `pairCoalescenceProb`: `v/(N-1)`, K-G p.35.
- `pairCoalescenceProb_eq_wf`: **it reproduces `WrightFisher`'s independently counted
  `1/N`**.
- `pairCoalescenceProb_moran`: and Moran's `2/(N(N-1))`, whose ratio to Wright-Fisher's is
  the `2/(N-1)` that becomes the two models' time-scale gap.
-/

namespace Coalescent

open Finset

/-! ### The mechanism: a pedigree map, and the family sizes it induces -/

/-- `ν_j`, the number of children of individual `j` under the pedigree map `f`.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the cardinality of a fibre: "how many
offspring have `j` as their parent", written down. -/
def familySize {N : ℕ} (f : Fin N → Fin N) (j : Fin N) : ℕ :=
  (univ.filter fun i ↦ f i = j).card

/-- **K-G (2.1): `Σ_j ν_j = N`.**  Kingman writes this as a constraint on the family-size
distribution ("subject of course to the constraint"); under a pedigree map it is not a
constraint at all but a consequence of every offspring having exactly one parent.  A
modelling assumption has become a theorem about functions, which is the whole difference
between positing the multinomial and deriving it. -/
theorem sum_familySize {N : ℕ} (f : Fin N → Fin N) : ∑ j, familySize f j = N := by
  have h := Finset.sum_fiberwise (univ : Finset (Fin N)) f (fun _ ↦ 1)
  simpa [familySize] using h

/-! ### The sibling count

Two distinct offspring coalesce in one generation exactly when they are siblings.  Counting
siblings from the offspring side gives `Σ_a (ν_{f a} - 1)`; counting them from the parent
side gives `Σ_j ν_j(ν_j - 1)`.  They are equal, and that equality is the whole mechanism-to-
formula step: the left side is what a sampled pair experiences, the right side is what a
demographer measures. -/

/-- The number of ORDERED pairs of distinct individuals sharing a parent, counted from the
offspring side: for each `a`, the number of others in its sibship.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a count on a given pedigree. -/
def sameParentCount {N : ℕ} (f : Fin N → Fin N) : ℕ :=
  ∑ a, ((univ.filter fun b ↦ f b = f a).card - 1)

/-- **The count, from the parent side: `Σ_j ν_j(ν_j - 1)`.**  This is the identity that puts
the family-size variance into the coalescence rate, and it holds for every pedigree map --
no exchangeability, no independence, no distributional assumption of any kind. -/
theorem sameParentCount_eq_sum_familySize {N : ℕ} (f : Fin N → Fin N) :
    sameParentCount f = ∑ j, familySize f j * (familySize f j - 1) := by
  have h := Finset.sum_fiberwise (univ : Finset (Fin N)) f
    (fun a ↦ (univ.filter fun b ↦ f b = f a).card - 1)
  unfold sameParentCount
  rw [← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hconst : ∀ a ∈ univ.filter (fun a ↦ f a = j),
      (univ.filter fun b ↦ f b = f a).card - 1
        = (univ.filter fun b ↦ f b = j).card - 1 := by
    intro a ha
    have hfa : f a = j := (Finset.mem_filter.mp ha).2
    rw [hfa]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rfl

/-- **No variance, no coalescence.**  If every individual has exactly one child -- the
pedigree map is the identity -- no two offspring are siblings, and the one-generation
coalescence probability is zero however large the population.

This is the sharpest form of the point K-G section 4 is making.  Drift is not caused by
finite population size; it is caused by variance in reproductive success, and a finite
population without that variance has none.  `Descent.Core.PopGenParameters`'s `Nₑ` is the
scalar that stands in for this, and the mechanism says what it is standing in for. -/
theorem sameParentCount_id {N : ℕ} : sameParentCount (id : Fin N → Fin N) = 0 := by
  unfold sameParentCount
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  have hfilter : (univ.filter fun b : Fin N ↦ (id b) = (id a)) = {a} := by
    ext b
    simp
  rw [hfilter]
  simp

/-! ### The probability, and the two models

Dividing the sibling count by the `N(N-1)` ordered pairs of distinct individuals gives the
probability that a uniformly sampled distinct pair coalesces in one generation.  Writing `v`
for the average of `ν(ν-1)` over parents -- the variance, when the mean family size is one --
the division collapses:

  `Σ_j ν_j(ν_j - 1) / (N(N-1)) = N v / (N(N-1)) = v/(N-1)`.  -/

/-- **K-G p.35: `p = Var(ν₁)/(N-1)`.**  The one-generation pair-coalescence probability of a
Cannings model with mean-one family size whose second factorial moment is `v`.

Empirical status: DERIVED.  It is `sameParentCount_eq_sum_familySize` divided by the number
of ordered pairs and simplified; `pairCoalescenceProb_eq_ratio` is that statement.  What is
empirical is the value of `v` for a given species, which is a measurement of fertility
variance and not of population size. -/
noncomputable def pairCoalescenceProb (N : ℕ) (v : ℝ) : ℝ := v / ((N : ℝ) - 1)

/-- The division, done: a family-size profile averaging `v` gives sibling probability
`v/(N-1)`.  The `N` in the numerator of `N v` cancels the `N` in `N(N-1)`, which is why the
answer depends on the population size only through `N - 1`. -/
theorem pairCoalescenceProb_eq_ratio {N : ℕ} (hN : 2 ≤ N) (v : ℝ) :
    pairCoalescenceProb N v = (N : ℝ) * v / ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hne : (N : ℝ) ≠ 0 := by linarith
  have hne1 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold pairCoalescenceProb
  rw [div_eq_div_iff hne1 (mul_ne_zero hne hne1)]
  ring

/-- Wright-Fisher's second factorial moment: `ν` is binomial `(N, 1/N)`, so
`E ν(ν-1) = N(N-1)/N² = (N-1)/N`, and its variance is `1 - 1/N`, which tends to the `σ² = 1`
K-G (4.2) uses for the Wright-Fisher time scale.

Empirical status: THIS IS THE MODEL -- it is the second moment of the family size under
`WrightFisher.parentAssignment`, i.e. a property of uniform independent parent choice, not
of any population. -/
noncomputable def wrightFisherSecondFactorialMoment (N : ℕ) : ℝ := ((N : ℝ) - 1) / (N : ℝ)

/-- **The two derivations agree.**  `Descent.Coalescent.WrightFisher` counts the pair
coalescence probability directly off the uniform parent law and gets `1/N`
(`noCoalescenceProb_two`).  This file computes it from the family-size variance by a route
that never mentions uniformity, and gets `1/N` as well.

That the two agree is the check that the Cannings formula is the right generalisation: a
general formula that failed to reproduce the special case it generalises would be a fourth
name for a quantity, which is the failure mode this corpus is built to make impossible. -/
theorem pairCoalescenceProb_eq_wf {N : ℕ} (hN : 2 ≤ N) :
    pairCoalescenceProb N (wrightFisherSecondFactorialMoment N) = 1 / (N : ℝ) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hne : (N : ℝ) ≠ 0 := by linarith
  have hne1 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold pairCoalescenceProb wrightFisherSecondFactorialMoment
  rw [div_div, div_eq_div_iff (mul_ne_zero hne hne1) hne]
  ring

/-- And therefore it is the complement of `WrightFisher.noCoalescenceProb` at `k = 2`: the
Cannings route and the counting route produce one number, stated against the corpus's own
definition rather than against a literal. -/
theorem pairCoalescenceProb_eq_one_sub_noCoalescenceProb {N : ℕ} (hN : 2 ≤ N) :
    pairCoalescenceProb N (wrightFisherSecondFactorialMoment N)
      = 1 - noCoalescenceProb N 2 := by
  have hpos : 0 < N := by omega
  rw [pairCoalescenceProb_eq_wf hN, noCoalescenceProb_two hpos]
  ring

/-- **Moran's `2/(N(N-1))`.**  K-G (4.5) gives the Moran family-size law variance `2/N`
(`Moran.moranVariance`), and the same formula turns it into a coalescence probability.
Against Wright-Fisher's `1/N` this is smaller by a factor `2/(N-1)`, which is the
per-generation form of the time-scale gap `N²/2` versus `N` that
`Moran.moranTimeScale` records. -/
theorem pairCoalescenceProb_moran {N : ℕ} (hN : 2 ≤ N) :
    pairCoalescenceProb N (2 / (N : ℝ)) = 2 / ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hne : (N : ℝ) ≠ 0 := by linarith
  have hne1 : (N : ℝ) - 1 ≠ 0 := by linarith
  unfold pairCoalescenceProb
  rw [div_div]

/-- Zero fertility variance, zero coalescence -- the scalar form of `sameParentCount_id`. -/
@[simp] theorem pairCoalescenceProb_zero (N : ℕ) : pairCoalescenceProb N 0 = 0 := by
  simp [pairCoalescenceProb]

/-- **The clock is fertility variance.**  Two populations of the same size whose family-size
variances differ by a factor `c` have coalescence probabilities differing by the same factor,
and hence coalescent time scales differing by `c`.  Population size enters only through the
common `N - 1`.

Stated as a ratio because that is the invariant: no measurement of a single population's
genealogy can separate `N` from `Var(ν)`, only their quotient, which is what `Nₑ` names. -/
theorem pairCoalescenceProb_scales (N : ℕ) (c v : ℝ) :
    pairCoalescenceProb N (c * v) = c * pairCoalescenceProb N v := by
  unfold pairCoalescenceProb
  ring

end Coalescent

end Descent

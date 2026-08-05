/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SegregatingSites
import Mathlib.Tactic

namespace Descent

/-!
# The site frequency spectrum, and the sum rule that ties it to the tree

`Descent.Coalescent.SegregatingSites` counts all the mutations on the coalescent tree.  The
site frequency spectrum splits that count by how many of the `n` sampled sequences carry the
derived allele: `ξ_i` is the number of segregating sites at which exactly `i` of the `n`
sequences are derived.  A mutation is seen by `i` sequences exactly when it fell on a branch
subtending `i` leaves, so the spectrum is the tree's branch lengths sorted by subtended leaf
count, and Fu (1995) computes those expectations:

  `E(L_i) = 2/i`  for `i = 1, …, n-1`,     hence     `E(ξ_i) = θ/i`.

That `2/i` is not derived in THIS file: it needs the Pólya-urn combinatorics giving the
chance that a branch in the `k`-lineage phase subtends `i` of the `n` leaves.  That count is
supplied downstream, in `Descent.Coalescent.FuUrn`, where `spectrumBranchLength_eq_urn`
proves the value below IS the urn expectation and `fu_sum` reduces the whole identity to the
hockey stick.  What is derived HERE is the sum rule, `sum_spectrumBranchLength`:

  `Σ_{i=1}^{n-1} 2/i = 2 a_{n-1} = E(L_n)`,

which says the spectrum's pieces reassemble into the total length that
`BranchLength.expectedTotalBranchLength_eq_harmonic` derives from the rate ladder.  A posited
formula that failed this would be posited *and* wrong; passing it is the strongest check
available without the missing combinatorics, and stating which of the two it is, is the
point.

## What the spectrum is for

Two consequences, both proved:

* `spectrum_shape_independent_of_theta`: `E(ξ_i) · i = θ` for every `i`, so the SHAPE of the
  spectrum -- the profile `1, 1/2, 1/3, …` -- carries no information about the mutation rate.
  Everything a spectrum says beyond its total is a statement about the genealogy, which is to
  say about demography and selection.  This is why the spectrum is the standard instrument
  for demographic inference and a poor one for mutation rates.
* `singletonShare_eq`: the expected share of singletons is `1/a_{n-1}`, which decays like
  `1/log n`.  Singletons never stop being the largest class, and they never stop shrinking
  as a fraction.

Both are statements about the constant-size neutral null.  A real spectrum departing from
them is the signal `Descent.Coalescent.SegregatingSites.expectedTajimaNumerator_eq_zero`
turns into a test, and what the departure indicates -- growth, structure, selection -- is not
determined by the spectrum, which is the kind of non-identifiability `Descent.Blindness`
exists to record.

## Main results

- `spectrumBranchLength`, `expectedSpectrum`: Fu (1995)'s `2/i` and `θ/i`, derived in
  `Descent.Coalescent.FuUrn`.
- `sum_spectrumBranchLength`: **the sum rule** -- the pieces are `E(L_n)`.
- `sum_expectedSpectrum`: and therefore the spectrum totals Watterson's `E(S_n)`.
- `spectrum_shape_independent_of_theta`: the shape does not see `θ`.
- `singletonShare_eq`: singletons are a `1/a_{n-1}` share of segregating sites.
-/

namespace Coalescent

open Finset

/-! ### The spectrum -/

/-- `E(L_i)`, the expected total length of the branches subtending exactly `i` of the `n`
sampled leaves.

Empirical status: DERIVED, with referent `Descent.Coalescent.FuUrn`.  Fu (1995, Theor.
Popul. Biol. 48, 172-197) obtains `2/i` from the probability that a branch in the `k`-lineage
phase subtends `i` leaves; that Pólya-urn count and the resulting identity are proved in
`FuUrn.fu_sum`, and `FuUrn.spectrumBranchLength_eq_urn` identifies this value with the
expectation.  A second, independent check is `sum_spectrumBranchLength`:
its total over `i` is the tree length the corpus DOES derive.  Note that `E(L_i)` does not
depend on `n` -- adding sample members adds new classes rather than changing the old ones,
which is the property the sum rule turns into a telescoping statement. -/
noncomputable def spectrumBranchLength (i : ℕ) : ℝ := 2 / (i : ℝ)

/-- `E(ξ_i)`, the expected number of segregating sites at which exactly `i` of the `n`
sampled sequences carry the derived allele: `θ/i`.

Empirical status: MIXED.  The `1/i` shape is DERIVED, in `Descent.Coalescent.FuUrn`; the
factor `θ/2` converting branch length to mutations is the Poisson mutation premise flagged at
`Descent.Coalescent.SegregatingSites.expectedSegregatingSites`, i.e. ASSUMED.  The head is
`MIXED` because those are two different verdicts and this definition depends on both. -/
noncomputable def expectedSpectrum (θ : ℝ) (i : ℕ) : ℝ := θ / 2 * spectrumBranchLength i

theorem expectedSpectrum_eq (θ : ℝ) (i : ℕ) : expectedSpectrum θ i = θ / (i : ℝ) := by
  unfold expectedSpectrum spectrumBranchLength
  ring

/-! ### The sum rule -/

/-- **The spectrum reassembles the tree.**  Summing the branch lengths over the `n-1`
possible leaf counts gives the total branch length, which
`BranchLength.expectedTotalBranchLength_eq_harmonic` derives from the rate ladder.

This is the check that Fu's asserted `2/i` is consistent with everything the corpus proves:
each `2/i` is a summand of `2 a_{n-1}`, so the classes partition the length exactly, with
nothing left over and nothing double counted. -/
theorem sum_spectrumBranchLength (n : ℕ) :
    ∑ j ∈ range (n - 1), spectrumBranchLength (j + 1) = expectedTotalBranchLength n := by
  rw [expectedTotalBranchLength_eq_harmonic]
  unfold harmonicSum spectrumBranchLength
  rw [mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  push_cast
  ring

/-- **And therefore the spectrum totals Watterson's `E(S_n)`.**  A spectrum whose classes sum
to something else would contradict the tree, not merely disagree with a convention. -/
theorem sum_expectedSpectrum (θ : ℝ) (n : ℕ) :
    ∑ j ∈ range (n - 1), expectedSpectrum θ (j + 1) = expectedSegregatingSites θ n := by
  unfold expectedSpectrum expectedSegregatingSites
  rw [← mul_sum, sum_spectrumBranchLength]

/-! ### What the shape says, and what it does not -/

/-- **The shape does not see `θ`.**  Multiplying the `i`-th class by `i` returns the mutation
rate whatever `i` is, so the profile `E(ξ_i) ∝ 1/i` is the same curve for every mutation rate
and only its height moves.

The practical reading: a spectrum's SHAPE is a statement about the genealogy alone.  Fitting
demography to a spectrum and then reading a mutation rate off the same fit is reading one
number twice. -/
theorem spectrum_shape_independent_of_theta (θ : ℝ) (j : ℕ) :
    expectedSpectrum θ (j + 1) * ((j : ℝ) + 1) = θ := by
  rw [expectedSpectrum_eq]
  have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The classes fall off exactly like `1/i` relative to the singleton class, for every `θ`
including `θ = 0` where both sides vanish. -/
theorem spectrum_ratio (θ : ℝ) (j : ℕ) :
    expectedSpectrum θ (j + 1) * ((j : ℝ) + 1) = expectedSpectrum θ 1 := by
  rw [spectrum_shape_independent_of_theta, expectedSpectrum_eq]
  norm_num

/-- **Singletons are a `1/a_{n-1}` share of the segregating sites.**  The numerator is `θ`
and the denominator `θ a_{n-1}`, so the mutation rate cancels: the share is a pure function
of sample size, decaying like `1/log n`.

Every sample is dominated by singletons, and every larger sample is dominated by them
slightly less.  A design that expects rare-variant burden to stabilise with sample size is
expecting the harmonic series to converge. -/
theorem singletonShare_eq {θ : ℝ} (hθ : θ ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    expectedSpectrum θ 1 / expectedSegregatingSites θ n = 1 / harmonicSum (n - 1) := by
  have hpos := harmonicSum_pos_of_two_le hn
  have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [expectedSpectrum_eq, expectedSegregatingSites_eq, h1, div_one,
    div_eq_div_iff (mul_ne_zero hθ hpos.ne') hpos.ne']
  ring

end Coalescent

end Descent

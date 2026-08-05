/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SiteFrequencySpectrum
import Mathlib.Tactic

namespace Descent

/-!
# Fu's urn: the count that turns `E(ξ_i) = θ/i` from an assertion into a theorem

`Descent.Coalescent.SiteFrequencySpectrum` asserts Fu (1995)'s `E(L_i) = 2/i` for the total
length of the branches subtending exactly `i` of the `n` sampled leaves, and could only check
its total.  `Descent.Coalescent.Program` recorded the missing ingredient by name: the count
giving the chance that a branch in the `k`-lineage phase subtends `i` leaves.

That count is a consequence of K-C (2.3).  Kingman's absolute distribution
`P{ℛ_k = ξ} ∝ λ_1!⋯λ_k!` multiplied by the number of set partitions with those class sizes,
`n!/(∏λ_a! ∏m_j!)`, leaves `n!/∏m_j!` -- which is to say the ORDERED size vector
`(λ_1,…,λ_k)` is uniform on the compositions of `n` into `k` positive parts.  There are
`C(n-1, k-1)` of those, and `C(n-i-1, k-2)` have a prescribed first part `i`, so a given
block subtends `i` leaves with probability

  `C(n-i-1, k-2) / C(n-1, k-1)`.                                              Fu (1995)

Summing over phases, with `k` blocks each holding for mean time `d_k⁻¹`,

  `E(L_i) = Σ_k k · d_k⁻¹ · C(n-i-1,k-2)/C(n-1,k-1) = Σ_k (2/(k-1)) C(n-i-1,k-2)/C(n-1,k-1)`,

and `expectedSpectrumBranchLength_eq` proves that sum is `2/i`.

## The identity, and why it is the hockey stick

Written in the shifted indices `i = a+1`, `n = a+m+2`, `k = j+2`, the sum is

  `2 Σ_{j≤m} C(m,j) / ((j+1) C(a+m+1, j+1))`,

and three rewrites collapse it.  Each term is `m!(a+b)!/(b!(a+m+1)!)` with `b = m-j`
(`fuTerm_eq`, from `Nat.choose_mul_factorial_mul_factorial` twice).  Reflecting the sum turns
`m-j` into a free index.  And `(a+b)!/b! = a! C(a+b,a)`, so what is left is

  `Σ_{b≤m} C(a+b, a) = C(a+m+1, a+1)`,

the hockey-stick identity, after which the factorials cancel to `a!/(a+1)! = 1/i`.

So Fu's `2/i` is the hockey stick divided by a falling factorial.  That is worth saying
because the `1/i` shape is the entire basis of demographic inference from the site frequency
spectrum, and it now rests on a combinatorial identity rather than on a citation.

## What this changes upstream

`SiteFrequencySpectrum.spectrumBranchLength` carried `Empirical status: ASSERTED`.
`spectrumBranchLength_eq_urn` derives it, so the assertion is discharged: the `1/i` profile,
the shape-independence of `θ`, and the `1/a_{n-1}` singleton share are now consequences of
the state space's cardinalities like everything else in the group.

## Main results

- `sum_range_choose_add`: the hockey stick, reindexed to `range (m+1)`.
- `fuTerm_eq`: each term of Fu's sum in factorials.
- `fu_sum`: **`Σ_{j≤m} C(m,j)/((j+1) C(a+m+1,j+1)) = 1/(a+1)`**.
- `expectedSpectrumBranchLength_eq`: **`E(L_i) = 2/i`**, Fu (1995).
- `spectrumBranchLength_eq_urn`: the asserted formula IS this expectation.
-/

namespace Coalescent

open Finset Nat

/-! ### The hockey stick -/

/-- `Σ_{b≤m} C(a+b, a) = C(a+m+1, a+1)`.  Mathlib's `Nat.sum_Icc_choose` reindexed from
`Icc a (a+m)` to `range (m+1)`. -/
theorem sum_range_choose_add (a m : ℕ) :
    ∑ b ∈ range (m + 1), (a + b).choose a = (a + m + 1).choose (a + 1) := by
  induction m with
  | Conditionals.zero => simp
  | succ p ih =>
      rw [sum_range_succ, ih, show a + (p + 1) = a + p + 1 from by omega]
      conv_rhs => rw [Nat.choose_succ_succ]
      ring

/-! ### One term -/

/-- Each term of Fu's sum, in factorials: `C(m,j)/((j+1)C(a+m+1,j+1)) = m!(a+b)!/(b!(a+m+1)!)`
with `b = m - j`.

Both `choose`s are cleared by `Nat.choose_mul_factorial_mul_factorial`, and the `(j+1)`
outside cancels the `(j+1)` inside `(j+1)!`.  That cancellation is the reason the answer has
no `j` in it after the sum is reflected. -/
theorem fuTerm_eq (a m j : ℕ) (hj : j ≤ m) :
    (m.choose j : ℝ) / (((j : ℝ) + 1) * ((a + m + 1).choose (j + 1) : ℝ))
      = ((m ! : ℝ) * ((a + (m - j))! : ℝ)) / (((m - j)! : ℝ) * ((a + m + 1)! : ℝ)) := by
  have hjle : j + 1 ≤ a + m + 1 := by omega
  have hsub : a + m + 1 - (j + 1) = a + (m - j) := by omega
  have h1 : (m.choose j : ℝ) * (j ! : ℝ) * ((m - j)! : ℝ) = (m ! : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.choose_mul_factorial_mul_factorial hj)
  have h2 : ((a + m + 1).choose (j + 1) : ℝ) * ((j + 1)! : ℝ) * ((a + (m - j))! : ℝ)
      = ((a + m + 1)! : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial hjle
    rw [hsub] at this
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  have hfj : ((j + 1)! : ℝ) = ((j : ℝ) + 1) * (j ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hpos1 : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hpos2 : (0 : ℝ) < ((m - j)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m - j)
  have hpos3 : (0 : ℝ) < ((a + (m - j))! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpos4 : (0 : ℝ) < ((a + m + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hposC : (0 : ℝ) < ((a + m + 1).choose (j + 1) : ℝ) := by
    have : 0 < (a + m + 1).choose (j + 1) := Nat.choose_pos hjle
    exact_mod_cast this
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hfac : ((a + m + 1)! : ℝ)
      = ((a + m + 1).choose (j + 1) : ℝ) * (((j : ℝ) + 1) * (j ! : ℝ)) * ((a + (m - j))! : ℝ) := by
    rw [← hfj]
    exact h2.symm
  rw [hfac, ← h1]
  ring

/-! ### The sum -/

/-- **`Σ_{j≤m} C(m,j)/((j+1) C(a+m+1,j+1)) = 1/(a+1)`.**  Fu's identity, with the hockey
stick doing the work. -/
theorem fu_sum (a m : ℕ) :
    ∑ j ∈ range (m + 1), (m.choose j : ℝ) / (((j : ℝ) + 1) * ((a + m + 1).choose (j + 1) : ℝ))
      = 1 / ((a : ℝ) + 1) := by
  have hstep : ∀ j ∈ range (m + 1),
      (m.choose j : ℝ) / (((j : ℝ) + 1) * ((a + m + 1).choose (j + 1) : ℝ))
        = (m ! : ℝ) / ((a + m + 1)! : ℝ) * (((a + (m - j))! : ℝ) / ((m - j)! : ℝ)) := by
    intro j hjm
    have hj : j ≤ m := by
      have := mem_range.mp hjm
      omega
    rw [fuTerm_eq a m j hj]
    have hpos2 : (0 : ℝ) < ((m - j)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m - j)
    have hpos4 : (0 : ℝ) < ((a + m + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp
  rw [sum_congr rfl hstep, ← mul_sum]
  have hrefl : ∑ j ∈ range (m + 1), (((a + (m - j))! : ℝ) / ((m - j)! : ℝ))
      = ∑ b ∈ range (m + 1), (((a + b)! : ℝ) / (b ! : ℝ)) := by
    have := Finset.sum_range_reflect (fun b ↦ (((a + b)! : ℝ) / (b ! : ℝ))) (m + 1)
    simpa using this
  rw [hrefl]
  have hterm : ∀ b ∈ range (m + 1),
      (((a + b)! : ℝ) / (b ! : ℝ)) = (a ! : ℝ) * ((a + b).choose a : ℝ) := by
    intro b _
    have hab : a ≤ a + b := Nat.le_add_right a b
    have hsub : a + b - a = b := by omega
    have h := Nat.choose_mul_factorial_mul_factorial hab
    rw [hsub] at h
    have hposb : (0 : ℝ) < (b ! : ℝ) := by exact_mod_cast Nat.factorial_pos b
    have hR : ((a + b).choose a : ℝ) * (a ! : ℝ) * (b ! : ℝ) = ((a + b)! : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    rw [eq_comm, eq_div_iff (ne_of_gt hposb), ← hR]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  have hstick : ∑ b ∈ range (m + 1), ((a + b).choose a : ℝ)
      = ((a + m + 1).choose (a + 1) : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_range_choose_add a m)
  rw [hstick]
  have hCfac : ((a + m + 1).choose (a + 1) : ℝ) * ((a + 1)! : ℝ) * (m ! : ℝ)
      = ((a + m + 1)! : ℝ) := by
    have hle : a + 1 ≤ a + m + 1 := by omega
    have hsub : a + m + 1 - (a + 1) = m := by omega
    have h := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at h
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  have hfa : ((a + 1)! : ℝ) = ((a : ℝ) + 1) * (a ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hposm : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hposa : (0 : ℝ) < (a ! : ℝ) := by exact_mod_cast Nat.factorial_pos a
  have hposN : (0 : ℝ) < ((a + m + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  rw [hfa] at hCfac
  have hden : (((a : ℝ) + 1) * (a ! : ℝ)) * (m ! : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt ha1) (ne_of_gt hposa)) (ne_of_gt hposm)
  have hC : ((a + m + 1).choose (a + 1) : ℝ)
      = ((a + m + 1)! : ℝ) / ((((a : ℝ) + 1) * (a ! : ℝ)) * (m ! : ℝ)) := by
    rw [eq_div_iff hden]
    linear_combination hCfac
  rw [hC]
  field_simp

/-! ### Fu's branch length -/

/-- **Fu (1995): `E(L_i) = 2/i`.**  The expected total length of branches subtending exactly
`i` of the `n` leaves, summed over the phases, with the urn probability in each.

Stated in the shifted indices the identity is natural in: `i = a+1`, `n = a+m+2`, and the
phase index `k = j+2` runs over `range (m+1)`, which is `k = 2, …, n-i+1` -- exactly the
phases in which a block CAN have `i` of the `n` leaves. -/
theorem expectedSpectrumBranchLength_eq (a m : ℕ) :
    ∑ j ∈ range (m + 1),
        2 / ((j : ℝ) + 1) * ((m.choose j : ℝ) / ((a + m + 1).choose (j + 1) : ℝ))
      = 2 / ((a : ℝ) + 1) := by
  have hstep : ∀ j ∈ range (m + 1),
      2 / ((j : ℝ) + 1) * ((m.choose j : ℝ) / ((a + m + 1).choose (j + 1) : ℝ))
        = 2 * ((m.choose j : ℝ) / (((j : ℝ) + 1) * ((a + m + 1).choose (j + 1) : ℝ))) := by
    intro j _
    field_simp
  rw [sum_congr rfl hstep, ← mul_sum, fu_sum]
  ring

/-- **The assertion is discharged.**  `SiteFrequencySpectrum.spectrumBranchLength` posited
`2/i` with `Empirical status: ASSERTED` and a note that the Pólya-urn count was missing.  It
is missing no longer: the posited value IS the urn expectation.

Everything `SiteFrequencySpectrum` derives from `2/i` -- the sum rule, the shape's
independence of `θ`, the `1/a_{n-1}` singleton share -- therefore rests on the state space's
cardinalities, like the rest of the group. -/
theorem spectrumBranchLength_eq_urn (a m : ℕ) :
    spectrumBranchLength (a + 1)
      = ∑ j ∈ range (m + 1),
          2 / ((j : ℝ) + 1) * ((m.choose j : ℝ) / ((a + m + 1).choose (j + 1) : ℝ)) := by
  rw [expectedSpectrumBranchLength_eq]
  unfold spectrumBranchLength
  push_cast
  ring

end Coalescent

end Descent

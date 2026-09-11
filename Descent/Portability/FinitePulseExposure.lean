/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdmixtureChronologyLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic

assert_below Descent.Decision Descent.Program

/-!
# Realising a finitely supported exposure law by ordered migration pulses

NOTE1 section 6.3 claims that every finitely supported recombination-exposure law on `[0, R]`
is realised by finitely many instantaneous migration pulses interleaved with recombination
blocks: sort the support by decreasing remaining exposure, let the cumulative immigration
increment after `k` pulses be the target donor fraction times the cumulative weight, and take
each pulse fraction to be that increment divided by the recipient fraction still available.
This module proves the arithmetic of that construction.

The exposure law is a nonnegative weight vector `w : ℕ → ℝ` with `∑_{i < n} wᵢ = 1`, and the
target donor fraction is a real `p` with `0 < p < 1`. The cumulative increment is
`A_k = p ∑_{i < k} wᵢ` and the pulse fraction is `f_k = (A_{k+1} - A_k) / (1 - A_k)`.

Proved here: every cumulative increment is at most `p`, so the recipient fraction `1 - A_k`
stays strictly positive; every pulse fraction lies in `[0, 1)`; the recipient fraction after
`k` pulses, which is the product `∏_{j < k} (1 - f_j)`, equals `1 - A_k`, so after all `n`
pulses it is exactly `1 - p`; the migration total of pulse `k` is `-log(1 - f_k)` and these
sum to `-log(1 - p)` over the whole history; each pulse's Stieltjes increment
`e^{-M_before}(1 - e^{-ΔM})` is exactly `A_{k+1} - A_k`, which divided by `p` returns the
weight `wₖ`, so the exposure law recovered from the pulses is the one we started from; and one
pulse acts on the donor coordinate of the ordered-event recursion of `AdmixtureChronologyLaw`
exactly by advancing `A_k` to `A_{k+1}`.

Not formalised: the interleaving itself. The recombination blocks that separate consecutive
pulses carry the exposure gaps `b_k - b_{k+1}` of the sorted support, and the claim that the
resulting three-way bookkeeping attributes exposure `b_k` to the material of pulse `k` needs
the sorted support as data; every identity proved here is independent of the ordering, so the
ordering enters only that unformalised attribution step. Nothing here identifies an exposure
law from data.

## Empirical status

None. The bodies here are algebra: the weights and the target donor fraction are stated
parameters of a stated mechanism, and every theorem is an identity or inequality among them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FinitePulseExposure

open Descent.Portability.AdmixtureChronologyLaw

noncomputable section

/-- Cumulative immigration increment after `k` pulses: the target donor fraction times the
cumulative exposure weight. -/
def cumulativeMass (donor : ℝ) (weight : ℕ → ℝ) (index : ℕ) : ℝ :=
  donor * ∑ component ∈ Finset.range index, weight component

/-- No pulses have landed yet. -/
@[simp] theorem cumulativeMass_zero (donor : ℝ) (weight : ℕ → ℝ) :
    cumulativeMass donor weight 0 = 0 := by
  simp [cumulativeMass]

/-- One pulse adds its own share of the target donor fraction. -/
theorem cumulativeMass_succ_sub (donor : ℝ) (weight : ℕ → ℝ) (index : ℕ) :
    cumulativeMass donor weight (index + 1) - cumulativeMass donor weight index =
      donor * weight index := by
  unfold cumulativeMass
  rw [Finset.sum_range_succ]
  ring

/-- No prefix of the pulses can deliver more than the whole target donor fraction. -/
theorem cumulativeMass_le_donor (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (total index : ℕ) (hle : index ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    cumulativeMass donor weight index ≤ donor := by
  have hprefix : ∑ component ∈ Finset.range index, weight component ≤ 1 := by
    have hsubset : Finset.range index ⊆ Finset.range total := by
      intro component hmem
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hmem) hle)
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ ↦ hweight i)
  unfold cumulativeMass
  nlinarith [hprefix, hdonor]

/-- Some recipient ancestry is always still available for the next pulse. -/
theorem one_sub_cumulativeMass_pos (donor : ℝ) (weight : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ)
    (hle : index ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    0 < 1 - cumulativeMass donor weight index := by
  have hbound :=
    cumulativeMass_le_donor donor weight hweight hdonor total index hle hsum
  linarith

/-- The fraction of the remaining recipient material replaced by pulse `k`. -/
def pulseFraction (donor : ℝ) (weight : ℕ → ℝ) (index : ℕ) : ℝ :=
  (cumulativeMass donor weight (index + 1) - cumulativeMass donor weight index) /
    (1 - cumulativeMass donor weight index)

/-- A pulse never removes recipient material. -/
theorem pulseFraction_nonneg (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    0 ≤ pulseFraction donor weight index := by
  have hpos :=
    one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index hle hsum
  unfold pulseFraction
  rw [cumulativeMass_succ_sub]
  exact div_nonneg (mul_nonneg hdonor (hweight index)) hpos.le

/-- A pulse never replaces all of the remaining recipient material. -/
theorem pulseFraction_lt_one (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    pulseFraction donor weight index < 1 := by
  have hpos := one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index
    (Nat.le_of_succ_le hle) hsum
  have hnext := cumulativeMass_le_donor donor weight hweight hdonor total (index + 1) hle hsum
  unfold pulseFraction
  rw [div_lt_one hpos]
  linarith

/-- The recipient fraction surviving the first `k` pulses. -/
def recipientFraction (donor : ℝ) (weight : ℕ → ℝ) (index : ℕ) : ℝ :=
  ∏ component ∈ Finset.range index, (1 - pulseFraction donor weight component)

/-- The surviving recipient fraction after `k` pulses is exactly `1 - A_k`: the pulse
fractions telescope. -/
theorem recipientFraction_eq (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    ∀ index ≤ total,
      recipientFraction donor weight index = 1 - cumulativeMass donor weight index := by
  intro index
  induction index with
  | zero =>
    intro _
    simp [recipientFraction]
  | succ index ih =>
    intro hle
    have hprev : index ≤ total := Nat.le_of_succ_le hle
    have hpos := one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index
      hprev hsum
    have hne : (1 : ℝ) - cumulativeMass donor weight index ≠ 0 := ne_of_gt hpos
    have hstep : recipientFraction donor weight (index + 1) =
        recipientFraction donor weight index * (1 - pulseFraction donor weight index) := by
      unfold recipientFraction
      rw [Finset.prod_range_succ]
    rw [hstep, ih hprev]
    unfold pulseFraction
    field_simp
    ring

/-- The whole pulse history leaves exactly the intended recipient fraction. -/
theorem recipientFraction_total (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    recipientFraction donor weight total = 1 - donor := by
  rw [recipientFraction_eq donor weight hweight hdonor hlt total hsum total le_rfl]
  unfold cumulativeMass
  rw [hsum, mul_one]

/-- The migration total supplied by one instantaneous pulse. -/
def pulseMigration (donor : ℝ) (weight : ℕ → ℝ) (index : ℕ) : ℝ :=
  -Real.log (1 - pulseFraction donor weight index)

/-- The survival factor of a pulse's migration total is the recipient share it spares. -/
theorem exp_neg_pulseMigration (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    Real.exp (-pulseMigration donor weight index) = 1 - pulseFraction donor weight index := by
  have hfrac := pulseFraction_lt_one donor weight hweight hdonor hlt total index hle hsum
  unfold pulseMigration
  rw [neg_neg, Real.exp_log (by linarith)]

/-- NOTE1 section 6.3: the pulse migration totals sum to `-log(1 - p)`, the migration total of
the whole admixture. -/
theorem sum_pulseMigration (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    ∑ index ∈ Finset.range total, pulseMigration donor weight index =
      -Real.log (1 - donor) := by
  have hnonzero : ∀ index ∈ Finset.range total,
      (1 - pulseFraction donor weight index) ≠ 0 := by
    intro index hmem
    have hle : index + 1 ≤ total := Finset.mem_range.mp hmem
    have hfrac := pulseFraction_lt_one donor weight hweight hdonor hlt total index hle hsum
    linarith
  have hlogsum := Real.log_prod (Finset.range total)
    (fun index ↦ 1 - pulseFraction donor weight index) hnonzero
  have hprod : (∏ index ∈ Finset.range total, (1 - pulseFraction donor weight index)) =
      1 - donor := recipientFraction_total donor weight hweight hdonor hlt total hsum
  rw [hprod] at hlogsum
  unfold pulseMigration
  rw [Finset.sum_neg_distrib, hlogsum]

/-- NOTE1 section 6.3, the Stieltjes increment of one pulse: the recipient fraction still
available times the fraction the pulse replaces is exactly the increment of the cumulative
immigration, namely the target donor fraction times that pulse's exposure weight. -/
theorem recipientFraction_mul_pulseFraction (donor : ℝ) (weight : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ)
    (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    recipientFraction donor weight index * pulseFraction donor weight index =
      donor * weight index := by
  have hprev : index ≤ total := Nat.le_of_succ_le hle
  have hpos := one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index
    hprev hsum
  have hne : (1 : ℝ) - cumulativeMass donor weight index ≠ 0 := ne_of_gt hpos
  rw [recipientFraction_eq donor weight hweight hdonor hlt total hsum index hprev,
    ← cumulativeMass_succ_sub donor weight index]
  unfold pulseFraction
  field_simp

/-- The exposure law is recovered: dividing each pulse's increment by the target donor
fraction returns the weight it was built from. -/
theorem increment_div_donor (donor : ℝ) (weight : ℕ → ℝ) (hdonor : donor ≠ 0) (index : ℕ) :
    (cumulativeMass donor weight (index + 1) - cumulativeMass donor weight index) / donor =
      weight index := by
  rw [cumulativeMass_succ_sub, mul_comm, mul_div_assoc, div_self hdonor, mul_one]

/-- One pulse advances the donor coordinate of the ordered-event recursion from one cumulative
increment to the next, so the pulse history is a chronology in the sense of
`AdmixtureChronologyLaw`. -/
theorem stepEvent_migration_pulse (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) (linkage : ℝ) :
    (stepEvent (ChronologyEvent.migration (pulseMigration donor weight index))
        (cumulativeMass donor weight index, linkage)).1 =
      cumulativeMass donor weight (index + 1) := by
  have hprev : index ≤ total := Nat.le_of_succ_le hle
  have hpos := one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index
    hprev hsum
  have hne : (1 : ℝ) - cumulativeMass donor weight index ≠ 0 := ne_of_gt hpos
  simp only [stepEvent_migration]
  rw [exp_neg_pulseMigration donor weight hweight hdonor hlt total index hle hsum]
  unfold pulseFraction
  field_simp
  ring

end

end Descent.Portability.FinitePulseExposure

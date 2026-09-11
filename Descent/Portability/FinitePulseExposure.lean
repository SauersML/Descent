/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AdmixtureChronologyLaw
import Descent.Portability.AttainableChronologyCurve
import Descent.Portability.ExposureLaplaceConstraints
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Sort

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

The interleaved history itself is built here too. `pulseHistory` alternates each pulse with
the recombination block that separates it from the next, taking the exposure gaps as data; its
migration totals sum to `-log(1 - p)`, its recombination totals sum to the gaps, and running it
through the ordered-event recursion drives the donor fraction from zero to exactly `p`.

The attribution step is proved as well. Take a support `b : ℕ → ℝ` padded by zero at index
`n` and let the recombination block after pulse `k` supply the gap `b_k - b_{k+1}`. After `k`
pulses the linkage is `(1 - A_k) ∑_{i < k} p wᵢ e^{-(bᵢ - b_k)}`: the material of pulse `i`
has met exactly the blocks placed after it. At the end the linkage is `p (1 - p) ∑ wᵢ e^{-bᵢ}`,
so the normalised coupling `couplingOfState` of `AttainableChronologyCurve` is `∑ wᵢ e^{-bᵢ}`,
which is NOTE1 (29) for this history. Padding the weights and exposures of a
`FiniteReportLaw (Fin n)` by zero and scaling every gap by `λ` gives NOTE1 (30): the coupling
is `exposureLaplace` of `ExposureLaplaceConstraints` at `λ`, for every `λ`, so the interleaved
history carries exactly the supplied exposure law. The order of the support enters only through
the signs of the blocks. When the support is sorted by decreasing exposure, every event supplies
a nonnegative migration total and a nonnegative recombination exposure, and the blocks supply
`b₀` in total. A block placed before the first pulse acts on a monomorphic recipient and changes
nothing, so any recombination total `R ≥ b₀` is reached without moving the state.

Finally the support of an arbitrary finite law is sorted. `decreasingOrder` lists the positions
by decreasing exposure (through `Tuple.sort` and a reversal), `reorderedLaw` relists the law
along it without changing its transform, and `realisingHistory` is the chronology built from
the sorted support with a leading block `λ (R - b₀)`. For every law on `Fin n` with exposures
in `[0, R]`, every `p ∈ (0, 1)` and every `λ ≥ 0`, that chronology has nonnegative event
totals, migration total `-log(1 - p)`, recombination total `λ R`, final donor fraction `p`, and
normalised coupling `exposureLaplace law exposure λ`. The existence statement of NOTE1 section
6.3 is the corollary `exists_chronology_eq_exposureLaplace`.

Not formalised: exposure laws that are not finitely supported, and the claim that knowing
`C(λ)` for every `λ` determines `ν`. Nothing here identifies an exposure law from data.

## Empirical status

None. The bodies here are algebra: the weights and the target donor fraction are stated
parameters of a stated mechanism, and every theorem is an identity or inequality among them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FinitePulseExposure

open Descent.Portability.AdmixtureChronologyLaw
open Descent.Portability.AttainableChronologyCurve (couplingOfState)
open Descent.Portability.ExposureLaplaceConstraints (exposureLaplace)

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

/-- Assumes: the donor coordinate has already reached the `k`-th cumulative increment. One
pulse then advances it to the next, whatever linkage the state carries. -/
theorem fst_stepEvent_migration_pulse (donor : ℝ) (weight : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ)
    (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) (state : ℝ × ℝ)
    (hstate : state.1 = cumulativeMass donor weight index) :
    (stepEvent (ChronologyEvent.migration (pulseMigration donor weight index)) state).1 =
      cumulativeMass donor weight (index + 1) := by
  have hprev : index ≤ total := Nat.le_of_succ_le hle
  have hpos := one_sub_cumulativeMass_pos donor weight hweight hdonor hlt total index
    hprev hsum
  have hne : (1 : ℝ) - cumulativeMass donor weight index ≠ 0 := ne_of_gt hpos
  simp only [stepEvent_migration]
  rw [hstate, exp_neg_pulseMigration donor weight hweight hdonor hlt total index hle hsum]
  unfold pulseFraction
  field_simp
  ring

/-- One pulse advances the donor coordinate of the ordered-event recursion from one cumulative
increment to the next, so the pulse history is a chronology in the sense of
`AdmixtureChronologyLaw`. -/
theorem stepEvent_migration_pulse (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) (linkage : ℝ) :
    (stepEvent (ChronologyEvent.migration (pulseMigration donor weight index))
        (cumulativeMass donor weight index, linkage)).1 =
      cumulativeMass donor weight (index + 1) :=
  fst_stepEvent_migration_pulse donor weight hweight hdonor hlt total index hle hsum
    (cumulativeMass donor weight index, linkage) rfl

/-- The interleaved history: each pulse followed by the recombination block that separates it
from the next pulse, with the exposure gaps supplied as data. -/
def pulseHistory (donor : ℝ) (weight gap : ℕ → ℝ) : ℕ → List ChronologyEvent
  | 0 => []
  | count + 1 =>
      pulseHistory donor weight gap count ++
        [ChronologyEvent.migration (pulseMigration donor weight count),
          ChronologyEvent.recombination (gap count)]

/-- An empty history has no events. -/
@[simp] theorem pulseHistory_zero (donor : ℝ) (weight gap : ℕ → ℝ) :
    pulseHistory donor weight gap 0 = [] := rfl

/-- One more pulse appends its migration block and its trailing recombination block. -/
theorem pulseHistory_succ (donor : ℝ) (weight gap : ℕ → ℝ) (count : ℕ) :
    pulseHistory donor weight gap (count + 1) =
      pulseHistory donor weight gap count ++
        [ChronologyEvent.migration (pulseMigration donor weight count),
          ChronologyEvent.recombination (gap count)] := rfl

/-- Running a concatenated history is running its two halves in order. -/
theorem runEvents_append (first second : List ChronologyEvent) (state : ℝ × ℝ) :
    runEvents (first ++ second) state = runEvents second (runEvents first state) := by
  unfold runEvents
  rw [List.foldl_append]

/-- The interleaved history drives the donor fraction along the cumulative increments, so
after all `n` pulses it is exactly the target donor fraction. -/
theorem fst_runEvents_pulseHistory (donor : ℝ) (weight gap : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    ∀ count ≤ total,
      (runEvents (pulseHistory donor weight gap count) (0, 0)).1 =
        cumulativeMass donor weight count := by
  intro count
  induction count with
  | zero =>
    intro _
    simp [runEvents]
  | succ count ih =>
    intro hle
    have hprev : count ≤ total := Nat.le_of_succ_le hle
    rw [pulseHistory_succ, runEvents_append]
    simp only [runEvents_cons, runEvents_nil, stepEvent_recombination]
    exact fst_stepEvent_migration_pulse donor weight hweight hdonor hlt total count hle hsum
      _ (ih hprev)

/-- The interleaved history delivers exactly the target donor fraction. -/
theorem fst_runEvents_pulseHistory_total (donor : ℝ) (weight gap : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    (runEvents (pulseHistory donor weight gap total) (0, 0)).1 = donor := by
  rw [fst_runEvents_pulseHistory donor weight gap hweight hdonor hlt total hsum total le_rfl]
  unfold cumulativeMass
  rw [hsum, mul_one]

/-- The migration totals of the interleaved history are the pulse migration totals. -/
theorem migrationTotal_pulseHistory (donor : ℝ) (weight gap : ℕ → ℝ) (count : ℕ) :
    ((pulseHistory donor weight gap count).map eventMigration).sum =
      ∑ index ∈ Finset.range count, pulseMigration donor weight index := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [pulseHistory_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp [eventMigration]

/-- The recombination totals of the interleaved history are the supplied exposure gaps. -/
theorem recombinationTotal_pulseHistory (donor : ℝ) (weight gap : ℕ → ℝ) (count : ℕ) :
    ((pulseHistory donor weight gap count).map eventRecombination).sum =
      ∑ index ∈ Finset.range count, gap index := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [pulseHistory_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp [eventRecombination]

/-- NOTE1 section 6.3: the interleaved history has migration total exactly `-log(1 - p)`. -/
theorem migrationTotal_pulseHistory_total (donor : ℝ) (weight gap : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    ((pulseHistory donor weight gap total).map eventMigration).sum =
      -Real.log (1 - donor) := by
  rw [migrationTotal_pulseHistory,
    sum_pulseMigration donor weight hweight hdonor hlt total hsum]

/-- Assumes: the state has reached the `k`-th cumulative increment and its linkage is the
surviving recipient fraction `1 - A_k` times an accumulated coefficient. One pulse then shrinks
the surviving recipient fraction to `1 - A_{k+1}` and adds the pulse's own immigration increment
`p wₖ` to the coefficient. -/
theorem snd_stepEvent_migration_pulse (donor : ℝ) (weight : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ)
    (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) (state : ℝ × ℝ)
    (coefficient : ℝ) (hstate : state.1 = cumulativeMass donor weight index)
    (hlinkage : state.2 = (1 - cumulativeMass donor weight index) * coefficient) :
    (stepEvent (ChronologyEvent.migration (pulseMigration donor weight index)) state).2 =
      (1 - cumulativeMass donor weight (index + 1)) * (coefficient + donor * weight index) := by
  have hshare := recipientFraction_mul_pulseFraction donor weight hweight hdonor hlt total
    index hle hsum
  rw [recipientFraction_eq donor weight hweight hdonor hlt total hsum index
    (Nat.le_of_succ_le hle)] at hshare
  simp only [stepEvent_migration]
  rw [hstate, hlinkage,
    exp_neg_pulseMigration donor weight hweight hdonor hlt total index hle hsum]
  linear_combination
    (coefficient + (1 - cumulativeMass donor weight index) * pulseFraction donor weight index) *
        cumulativeMass_succ_sub donor weight index +
      (1 - cumulativeMass donor weight (index + 1) - coefficient -
        (1 - cumulativeMass donor weight index) * pulseFraction donor weight index) * hshare

/-- NOTE1 (28) along the interleaved history whose recombination blocks are the support gaps
`b_j - b_{j+1}`. After `k` pulses the linkage is the surviving recipient fraction `1 - A_k`
times the sum over the pulses `i < k` of the immigration increment `p wᵢ`, each damped by the
exposure `b_i - b_k` its material has met since it arrived. -/
theorem snd_runEvents_pulseHistory (donor : ℝ) (weight exposure : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    ∀ count ≤ total,
      (runEvents (pulseHistory donor weight
          (fun index ↦ exposure index - exposure (index + 1)) count) (0, 0)).2 =
        (1 - cumulativeMass donor weight count) *
          ∑ index ∈ Finset.range count,
            donor * weight index * Real.exp (-(exposure index - exposure count)) := by
  intro count
  induction count with
  | zero =>
    intro _
    simp [runEvents]
  | succ count ih =>
    intro hnext
    have hbefore : count ≤ total := Nat.le_of_succ_le hnext
    have hdamp : ∑ index ∈ Finset.range count,
        donor * weight index * Real.exp (-(exposure index - exposure (count + 1))) =
          (∑ index ∈ Finset.range count,
            donor * weight index * Real.exp (-(exposure index - exposure count))) *
            Real.exp (-(exposure count - exposure (count + 1))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun index _ ↦ ?_)
      have hexp : Real.exp (-(exposure index - exposure (count + 1))) =
          Real.exp (-(exposure index - exposure count)) *
            Real.exp (-(exposure count - exposure (count + 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    have hfst := fst_runEvents_pulseHistory donor weight
      (fun index ↦ exposure index - exposure (index + 1)) hweight hdonor hlt total hsum count
      hbefore
    rw [pulseHistory_succ, runEvents_append]
    simp only [runEvents_cons, runEvents_nil, stepEvent_recombination]
    rw [snd_stepEvent_migration_pulse donor weight hweight hdonor hlt total count hnext hsum _ _
      hfst (ih hbefore), Finset.sum_range_succ, hdamp]
    ring

/-- NOTE1 section 6.3, the attribution step. Assumes: the support is padded by zero at index
`n`. The interleaved history whose recombination blocks are the support gaps `b_j - b_{j+1}`
ends with linkage `p (1 - p) ∑ wᵢ e^{-bᵢ}`, so the material of pulse `i` meets exactly the
exposure `bᵢ`, in whatever order the support is listed. -/
theorem snd_runEvents_pulseHistory_total (donor : ℝ) (weight exposure : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1)
    (hterminal : exposure total = 0) :
    (runEvents (pulseHistory donor weight
        (fun index ↦ exposure index - exposure (index + 1)) total) (0, 0)).2 =
      donor * (1 - donor) *
        ∑ index ∈ Finset.range total, weight index * Real.exp (-exposure index) := by
  rw [snd_runEvents_pulseHistory donor weight exposure hweight hdonor hlt total hsum total
    le_rfl, hterminal]
  unfold cumulativeMass
  rw [hsum, mul_one, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun index _ ↦ ?_)
  rw [sub_zero]
  ring

/-- NOTE1 (29) for the interleaved history. Assumes: a target donor fraction in `(0, 1)` and a
support padded by zero at index `n`. The normalised coupling of the state the history reaches
is `∑ wᵢ e^{-bᵢ}`, the survival factor averaged over the supplied exposure law. -/
theorem couplingOfState_pulseHistory (donor : ℝ) (weight exposure : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 < donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1)
    (hterminal : exposure total = 0) :
    couplingOfState (runEvents (pulseHistory donor weight
        (fun index ↦ exposure index - exposure (index + 1)) total) (0, 0)) =
      ∑ index ∈ Finset.range total, weight index * Real.exp (-exposure index) := by
  have hne : donor * (1 - donor) ≠ 0 := ne_of_gt (mul_pos hdonor (by linarith))
  unfold couplingOfState
  rw [fst_runEvents_pulseHistory_total donor weight _ hweight hdonor.le hlt total hsum,
    snd_runEvents_pulseHistory_total donor weight exposure hweight hdonor.le hlt total hsum
      hterminal, div_eq_iff hne]
  ring

/-- A weight or exposure vector on `Fin n`, extended by zero to every natural index. -/
def padByZero {n : ℕ} (value : Fin n → ℝ) (index : ℕ) : ℝ :=
  if hindex : index < n then value ⟨index, hindex⟩ else 0

/-- Padding leaves the vector alone on its own indices. -/
@[simp] theorem padByZero_val {n : ℕ} (value : Fin n → ℝ) (index : Fin n) :
    padByZero value index = value index := by
  simp [padByZero]

/-- The padded vector vanishes at index `n`, just past its own indices. -/
@[simp] theorem padByZero_self {n : ℕ} (value : Fin n → ℝ) : padByZero value n = 0 := by
  simp [padByZero]

/-- The padded weights of a finite law are nonnegative at every index. -/
theorem padByZero_mass_nonneg {n : ℕ} (law : FiniteReportLaw (Fin n)) (index : ℕ) :
    0 ≤ padByZero law.mass index := by
  unfold padByZero
  split_ifs with hindex
  · exact law.mass_nonneg _
  · exact le_rfl

/-- The padded weights of a finite law sum to one over the first `n` indices. -/
theorem sum_range_padByZero_mass {n : ℕ} (law : FiniteReportLaw (Fin n)) :
    ∑ index ∈ Finset.range n, padByZero law.mass index = 1 := by
  rw [Finset.sum_range]
  simp only [padByZero_val]
  exact law.mass_sum

/-- NOTE1 (30), the attribution step for a finitely supported exposure law. Assumes: a target
donor fraction in `(0, 1)`. Pad the law's weights and exposures by zero beyond index `n` and
scale every support gap by `λ`. The normalised coupling of the chronology this builds is the
transform `exposureLaplace` of the supplied law at `λ`, for every `λ`: the interleaved history
carries exactly the supplied exposure law. -/
theorem couplingOfState_pulseHistory_eq_exposureLaplace {n : ℕ}
    (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ) (donor lam : ℝ)
    (hdonor : 0 < donor) (hlt : donor < 1) :
    couplingOfState (runEvents (pulseHistory donor (padByZero law.mass)
        (fun index ↦ lam * padByZero exposure index - lam * padByZero exposure (index + 1)) n)
        (0, 0)) = exposureLaplace law exposure lam := by
  refine (couplingOfState_pulseHistory donor (padByZero law.mass)
    (fun index ↦ lam * padByZero exposure index) (padByZero_mass_nonneg law) hdonor hlt n
    (sum_range_padByZero_mass law) (by simp)).trans ?_
  rw [Finset.sum_range]
  unfold exposureLaplace FiniteReportLaw.expectation
  refine Finset.sum_congr rfl (fun index _ ↦ ?_)
  simp only [padByZero_val]

/-- Each pulse supplies a nonnegative migration total. -/
theorem pulseMigration_nonneg (donor : ℝ) (weight : ℕ → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (hdonor : 0 ≤ donor) (hlt : donor < 1) (total index : ℕ) (hle : index + 1 ≤ total)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1) :
    0 ≤ pulseMigration donor weight index := by
  have hnonneg := pulseFraction_nonneg donor weight hweight hdonor hlt total index
    (Nat.le_of_succ_le hle) hsum
  have hfrac := pulseFraction_lt_one donor weight hweight hdonor hlt total index hle hsum
  unfold pulseMigration
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))

/-- Assumes: the support is sorted by decreasing exposure over the first `n + 1` indices. Every
event of the interleaved history then supplies a nonnegative migration total and a nonnegative
recombination exposure, so the history is a chronology with nonnegative rates. -/
theorem eventTotals_nonneg_pulseHistory (donor : ℝ) (weight exposure : ℕ → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (hdonor : 0 ≤ donor) (hlt : donor < 1) (total : ℕ)
    (hsum : ∑ component ∈ Finset.range total, weight component = 1)
    (hsorted : ∀ index, index + 1 ≤ total → exposure (index + 1) ≤ exposure index) :
    ∀ count ≤ total, ∀ event ∈ pulseHistory donor weight
        (fun index ↦ exposure index - exposure (index + 1)) count,
      0 ≤ eventMigration event ∧ 0 ≤ eventRecombination event := by
  intro count
  induction count with
  | zero =>
    intro _ event hevent
    simp at hevent
  | succ count ih =>
    intro hnext event hevent
    rw [pulseHistory_succ, List.mem_append] at hevent
    rcases hevent with hold | hnew
    · exact ih (Nat.le_of_succ_le hnext) event hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
      rcases hnew with rfl | rfl
      · exact ⟨pulseMigration_nonneg donor weight hweight hdonor hlt total count hnext hsum,
          le_rfl⟩
      · exact ⟨le_rfl, sub_nonneg.mpr (hsorted count hnext)⟩

/-- The support gaps supply `b₀ - bₙ` of recombination exposure in total, which is the largest
exposure `b₀` when the support is padded by zero at index `n`. -/
theorem recombinationTotal_supportGaps (donor : ℝ) (weight exposure : ℕ → ℝ) (total : ℕ) :
    ((pulseHistory donor weight (fun index ↦ exposure index - exposure (index + 1))
        total).map eventRecombination).sum = exposure 0 - exposure total := by
  rw [recombinationTotal_pulseHistory]
  exact Finset.sum_range_sub' exposure total

/-- A recombination block placed before the first pulse acts on a monomorphic recipient and
leaves the state where it was, so prefixing the block `R - b₀` raises the recombination total
to `R` without changing the donor fraction or the linkage the history reaches. -/
theorem runEvents_leading_recombination (exposure : ℝ) (events : List ChronologyEvent) :
    runEvents (ChronologyEvent.recombination exposure :: events) (0, 0) =
      runEvents events (0, 0) := by
  simp

/-- The positions of a finite support listed by decreasing exposure: `Tuple.sort` lists them by
increasing exposure, and reversing the positions turns that order around. -/
def decreasingOrder {n : ℕ} (exposure : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans (Tuple.sort exposure)

/-- The exposures relisted by decreasing size. -/
def sortedExposure {n : ℕ} (exposure : Fin n → ℝ) : Fin n → ℝ :=
  fun position ↦ exposure (decreasingOrder exposure position)

/-- The relisted exposures decrease along the positions. -/
theorem antitone_sortedExposure {n : ℕ} (exposure : Fin n → ℝ) :
    Antitone (sortedExposure exposure) := by
  intro first second hle
  simp only [sortedExposure, decreasingOrder, Equiv.trans_apply, Fin.revPerm_apply]
  exact Tuple.monotone_sort exposure (Fin.rev_le_rev.mpr hle)

/-- A finite law relisted along a permutation of its support. -/
def reorderedLaw {n : ℕ} (law : FiniteReportLaw (Fin n)) (order : Equiv.Perm (Fin n)) :
    FiniteReportLaw (Fin n) where
  mass := fun position ↦ law.mass (order position)
  mass_nonneg := fun position ↦ law.mass_nonneg (order position)
  mass_sum := (Equiv.sum_comp order law.mass).trans law.mass_sum

/-- Relisting the support along any permutation leaves the exposure transform unchanged. -/
theorem exposureLaplace_reorderedLaw {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (order : Equiv.Perm (Fin n)) (lam : ℝ) :
    exposureLaplace (reorderedLaw law order) (fun position ↦ exposure (order position)) lam =
      exposureLaplace law exposure lam := by
  unfold exposureLaplace FiniteReportLaw.expectation
  exact Equiv.sum_comp order
    (fun position ↦ law.mass position * Real.exp (-(lam * exposure position)))

/-- Assumes: the vector is antitone and nonnegative. The padded vector then does not increase
from any index to the next over the first `n + 1` indices. -/
theorem padByZero_succ_le {n : ℕ} (value : Fin n → ℝ) (hanti : Antitone value)
    (hnonneg : ∀ position, 0 ≤ value position) (index : ℕ) (hle : index + 1 ≤ n) :
    padByZero value (index + 1) ≤ padByZero value index := by
  have hindex : index < n := Nat.lt_of_succ_le hle
  unfold padByZero
  rw [dif_pos hindex]
  split_ifs with hnext
  · exact hanti (Fin.mk_le_mk.mpr (Nat.le_succ index))
  · exact hnonneg _

/-- The chronology realising a finite exposure law on `[0, R]` with every recombination block
scaled by `λ`: a leading block `λ (R - b₀)`, then the pulses with the support listed by
decreasing exposure, each followed by the scaled gap to the next exposure and the last by its
own scaled exposure. -/
def realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n)) (exposure : Fin n → ℝ)
    (donor lam bound : ℝ) : List ChronologyEvent :=
  ChronologyEvent.recombination (lam * (bound - padByZero (sortedExposure exposure) 0)) ::
    pulseHistory donor (padByZero (reorderedLaw law (decreasingOrder exposure)).mass)
      (fun index ↦ lam * padByZero (sortedExposure exposure) index -
        lam * padByZero (sortedExposure exposure) (index + 1)) n

/-- NOTE1 (30) for the realising chronology. Assumes: a target donor fraction in `(0, 1)`. Its
normalised coupling is the exposure transform of the supplied law at `λ`, in whatever order the
law lists its support. -/
theorem couplingOfState_realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) (hdonor : 0 < donor) (hlt : donor < 1) :
    couplingOfState (runEvents (realisingHistory law exposure donor lam bound) (0, 0)) =
      exposureLaplace law exposure lam := by
  unfold realisingHistory
  rw [runEvents_leading_recombination]
  exact (couplingOfState_pulseHistory_eq_exposureLaplace
    (reorderedLaw law (decreasingOrder exposure)) (sortedExposure exposure) donor lam hdonor
    hlt).trans (exposureLaplace_reorderedLaw law exposure (decreasingOrder exposure) lam)

/-- The realising chronology drives the donor fraction from zero to exactly the target. -/
theorem fst_runEvents_realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) (hdonor : 0 ≤ donor) (hlt : donor < 1) :
    (runEvents (realisingHistory law exposure donor lam bound) (0, 0)).1 = donor := by
  unfold realisingHistory
  rw [runEvents_leading_recombination]
  exact fst_runEvents_pulseHistory_total donor _ _
    (padByZero_mass_nonneg (reorderedLaw law (decreasingOrder exposure))) hdonor hlt n
    (sum_range_padByZero_mass (reorderedLaw law (decreasingOrder exposure)))

/-- The realising chronology has migration total exactly `-log(1 - p)`. -/
theorem migrationTotal_realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) (hdonor : 0 ≤ donor) (hlt : donor < 1) :
    ((realisingHistory law exposure donor lam bound).map eventMigration).sum =
      -Real.log (1 - donor) := by
  unfold realisingHistory
  rw [List.map_cons, List.sum_cons, migrationTotal_pulseHistory_total donor _ _
    (padByZero_mass_nonneg (reorderedLaw law (decreasingOrder exposure))) hdonor hlt n
    (sum_range_padByZero_mass (reorderedLaw law (decreasingOrder exposure)))]
  simp [eventMigration]

/-- The realising chronology has recombination total exactly `λ R`. -/
theorem recombinationTotal_realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) :
    ((realisingHistory law exposure donor lam bound).map eventRecombination).sum =
      lam * bound := by
  unfold realisingHistory
  rw [List.map_cons, List.sum_cons, recombinationTotal_supportGaps donor _
    (fun index ↦ lam * padByZero (sortedExposure exposure) index) n]
  simp only [eventRecombination, padByZero_self]
  ring

/-- Assumes: exposures in `[0, R]` and a nonnegative scale `λ`. Every event of the realising
chronology supplies a nonnegative migration total and a nonnegative recombination exposure. -/
theorem eventTotals_nonneg_realisingHistory {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) (hdonor : 0 ≤ donor) (hlt : donor < 1)
    (hlam : 0 ≤ lam) (hexposure : ∀ position, 0 ≤ exposure position)
    (hbound : ∀ position, exposure position ≤ bound) :
    ∀ event ∈ realisingHistory law exposure donor lam bound,
      0 ≤ eventMigration event ∧ 0 ≤ eventRecombination event := by
  have hleading : padByZero (sortedExposure exposure) 0 ≤ bound := by
    unfold padByZero
    split_ifs with hpositive
    · exact hbound _
    · rcases Nat.eq_zero_or_pos n with hzero | hpos
      · subst hzero
        have hmass := law.mass_sum
        simp at hmass
      · exact absurd hpos hpositive
  intro event hevent
  unfold realisingHistory at hevent
  rcases List.mem_cons.mp hevent with rfl | hrest
  · exact ⟨le_rfl, mul_nonneg hlam (sub_nonneg.mpr hleading)⟩
  · exact eventTotals_nonneg_pulseHistory donor
      (padByZero (reorderedLaw law (decreasingOrder exposure)).mass)
      (fun index ↦ lam * padByZero (sortedExposure exposure) index)
      (padByZero_mass_nonneg (reorderedLaw law (decreasingOrder exposure))) hdonor hlt n
      (sum_range_padByZero_mass (reorderedLaw law (decreasingOrder exposure)))
      (fun index hnext ↦ mul_le_mul_of_nonneg_left
        (padByZero_succ_le (sortedExposure exposure) (antitone_sortedExposure exposure)
          (fun position ↦ hexposure _) index hnext) hlam) n le_rfl event hrest

/-- NOTE1 section 6.3: every finitely supported exposure law on `[0, R]` is realised by finitely
many ordered migration pulses. Assumes: exposures in `[0, R]`, a target donor fraction in
`(0, 1)`, and a nonnegative scale `λ`. Some ordered chronology with nonnegative event totals has
migration total `-log(1 - p)`, recombination total `λ R`, final donor fraction `p`, and
normalised coupling equal to the exposure transform of the law at `λ`. -/
theorem exists_chronology_eq_exposureLaplace {n : ℕ} (law : FiniteReportLaw (Fin n))
    (exposure : Fin n → ℝ) (donor lam bound : ℝ) (hdonor : 0 < donor) (hlt : donor < 1)
    (hlam : 0 ≤ lam) (hexposure : ∀ position, 0 ≤ exposure position)
    (hbound : ∀ position, exposure position ≤ bound) :
    ∃ events : List ChronologyEvent,
      (∀ event ∈ events, 0 ≤ eventMigration event ∧ 0 ≤ eventRecombination event) ∧
        (events.map eventMigration).sum = -Real.log (1 - donor) ∧
        (events.map eventRecombination).sum = lam * bound ∧
        (runEvents events (0, 0)).1 = donor ∧
        couplingOfState (runEvents events (0, 0)) = exposureLaplace law exposure lam :=
  ⟨realisingHistory law exposure donor lam bound,
    eventTotals_nonneg_realisingHistory law exposure donor lam bound hdonor.le hlt hlam
      hexposure hbound,
    migrationTotal_realisingHistory law exposure donor lam bound hdonor.le hlt,
    recombinationTotal_realisingHistory law exposure donor lam bound,
    fst_runEvents_realisingHistory law exposure donor lam bound hdonor.le hlt,
    couplingOfState_realisingHistory law exposure donor lam bound hdonor hlt⟩

end

end Descent.Portability.FinitePulseExposure

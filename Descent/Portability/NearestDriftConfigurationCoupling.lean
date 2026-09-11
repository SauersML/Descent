/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConvexOrderCoupling
import Descent.Portability.TurnoverExtremalCouplings

assert_below Descent.Decision Descent.Program

/-!
# The nearest-drift coupling at the configuration level

DC Lemma 3.2 constructs the joint sign process that attains the lower endpoint of the dynamic
convex-order envelope.  `Descent.Portability.ConvexOrderCoupling` proves the envelope itself and
that its lower endpoint is the nearest-drift chain `driftStep`, but only as a comparison of
aggregate count laws.  This module supplies the missing construction: an explicit kernel on sign
configurations `Fin n → Bool` whose induced count process is exactly that chain, so the endpoint
is attained by an actual joint process and not only at the aggregate level.

`nearestDriftKernel` is DC (3.7) written for a skeleton step.  At a configuration with `k` ones
it flips each one-zero pair with probability `τ c / (k (n - k))` where `c = min(α k, β (n - k))`,
each single one with probability `τ (α k - β (n - k))₊ / k`, and each single zero with
probability `τ (β (n - k) - α k)₊ / (n - k)`; formulas over an empty group contribute nothing,
which is the manuscript's instruction to omit them.

Three theorems make it DC Lemma 3.2.  `nearestDriftKernel_flip` is admissibility, DC (3.2): each
coordinate flips with probability exactly `τα` when it is one and `τβ` when it is zero, because
the paired rate and the singleton rate of a one add to `α`, and likewise for a zero.
`nearestDriftKernel_count` is the count identity: paired flips leave the count alone, the
remaining singleton flips carry exactly the nearest-drift rates, and the induced one-step count
operator is `driftStep`.  `pathExp_nearestDriftKernel` iterates that to every horizon, so the
path expectation of every count report under this configuration process equals the nearest-drift
chain's.  Together with `ConvexOrderCoupling.pathExp_nearestDrift_le` this turns the envelope's
lower endpoint from a bound into an attained value, and
`nearestDrift_pathExp_le_synchronous` compares it with the maximally dependent coupling of
`Descent.Portability.TurnoverExtremalCouplings` at the other endpoint.

Domain conditions: nonnegative rates, and a step short enough that the row is a probability
vector.  Nothing is assumed about the coordinates beyond their prescribed flip rates.

## Empirical status

None.  The kernel here is an exhibited coupling, not a measurement: its rates are inputs, and
what it asserts is that a joint process with those rates exists and induces the nearest-drift
count chain.  Nothing is fitted, and no cohort is described.  What could carry an empirical
status is a named quantity in a downstream module claiming that this coupling is the one some
population realizes; such a name keeps its own docstring, its own regime, and its own ledger
row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NearestDriftConfigurationCoupling

open Foundations ConvexOrderCoupling TurnoverArchitectureMetrics TurnoverExtremalCouplings

noncomputable section

variable {n : ℕ}

/-! ## The rates of DC Lemma 3.2 -/

/-- The total one-to-zero rate `A₀ = α k` at a configuration. -/
def oneRateTotal (α : ℝ) (s : Fin n → Bool) : ℝ :=
  α * ((occupiedCount s : ℕ) : ℝ)

/-- The total zero-to-one rate `B₀ = β (n - k)` at a configuration. -/
def zeroRateTotal (β : ℝ) (s : Fin n → Bool) : ℝ :=
  β * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))

/-- The paired-flip probability of each one-zero pair, DC (3.7) times the step. -/
def pairProb (α β τ : ℝ) (s : Fin n → Bool) : ℝ :=
  τ * min (oneRateTotal α s) (zeroRateTotal β s)
    / (((occupiedCount s : ℕ) : ℝ) * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)))

/-- The singleton-flip probability of each one. -/
def singleOneProb (α β τ : ℝ) (s : Fin n → Bool) : ℝ :=
  τ * max (oneRateTotal α s - zeroRateTotal β s) 0 / ((occupiedCount s : ℕ) : ℝ)

/-- The singleton-flip probability of each zero. -/
def singleZeroProb (α β τ : ℝ) (s : Fin n → Bool) : ℝ :=
  τ * max (zeroRateTotal β s - oneRateTotal α s) 0
    / ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))

/-- The probability that nothing flips. -/
def stayProb (α β τ : ℝ) (s : Fin n → Bool) : ℝ :=
  1 - τ * max (oneRateTotal α s) (zeroRateTotal β s)

/-- **DC Lemma 3.2, the coupling.**  Paired one-zero flips carry the common rate, and the
imbalance is spent on singleton flips of whichever group is in excess. -/
def nearestDriftKernel (α β τ : ℝ) (s s' : Fin n → Bool) : ℝ :=
  (if s' = s then stayProb α β τ s else 0)
    + ∑ i, (if s' = flipCoord i s then
        (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s) else 0)
    + ∑ i, ∑ j, (if s' = flipCoord j (flipCoord i s) then
        (if s i = true ∧ s j = false then pairProb α β τ s else 0) else 0)

/-! ## Arithmetic of the rates -/

/-- The larger total rate splits into the common rate and the two imbalances. -/
theorem max_eq_min_add_parts (A B : ℝ) :
    max A B = min A B + (max (A - B) 0 + max (B - A) 0) := by
  rcases le_total A B with h | h
  · rw [max_eq_right h, min_eq_left h, max_eq_right (by linarith : A - B ≤ 0),
      max_eq_left (by linarith : 0 ≤ B - A)]
    ring
  · rw [max_eq_left h, min_eq_right h, max_eq_left (by linarith : 0 ≤ A - B),
      max_eq_right (by linarith : B - A ≤ 0)]
    ring

/-- The nearest-drift upward rate is the zero-group excess. -/
theorem upRate_eq_excess (α β : ℝ) (s : Fin n → Bool) :
    upRate n α β ((occupiedCount s : ℕ) : ℤ)
      = max (zeroRateTotal β s - oneRateTotal α s) 0 := by
  rw [upRate, countDrift, oneRateTotal, zeroRateTotal]
  push_cast
  ring_nf

/-- The nearest-drift downward rate is the one-group excess. -/
theorem downRate_eq_excess (α β : ℝ) (s : Fin n → Bool) :
    downRate n α β ((occupiedCount s : ℕ) : ℤ)
      = max (oneRateTotal α s - zeroRateTotal β s) 0 := by
  rw [downRate, countDrift, oneRateTotal, zeroRateTotal]
  push_cast
  ring_nf

/-- The one-group total rate is nonnegative. -/
theorem oneRateTotal_nonneg {α : ℝ} (hα : 0 ≤ α) (s : Fin n → Bool) :
    0 ≤ oneRateTotal α s := by
  rw [oneRateTotal]
  positivity

/-- The zero-group total rate is nonnegative. -/
theorem zeroRateTotal_nonneg {β : ℝ} (hβ : 0 ≤ β) (s : Fin n → Bool) :
    0 ≤ zeroRateTotal β s := by
  rw [zeroRateTotal]
  have hle : ((occupiedCount s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast occupiedCount_le s
  have : (0 : ℝ) ≤ (n : ℝ) - ((occupiedCount s : ℕ) : ℝ) := by linarith
  exact mul_nonneg hβ this

/-- The singleton rates of the ones aggregate to the one-group excess. -/
theorem count_mul_singleOneProb {α β τ : ℝ} (hβ : 0 ≤ β) (s : Fin n → Bool) :
    ((occupiedCount s : ℕ) : ℝ) * singleOneProb α β τ s
      = τ * max (oneRateTotal α s - zeroRateTotal β s) 0 := by
  rcases eq_or_ne ((occupiedCount s : ℕ) : ℝ) 0 with h | h
  · rw [h, zero_mul]
    have hone : oneRateTotal α s = 0 := by rw [oneRateTotal, h, mul_zero]
    have hzero : 0 ≤ zeroRateTotal β s := zeroRateTotal_nonneg hβ s
    rw [hone, max_eq_right (by linarith), mul_zero]
  · rw [singleOneProb]
    field_simp

/-- The singleton rates of the zeros aggregate to the zero-group excess. -/
theorem countCompl_mul_singleZeroProb {α β τ : ℝ} (hα : 0 ≤ α) (s : Fin n → Bool) :
    ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * singleZeroProb α β τ s
      = τ * max (zeroRateTotal β s - oneRateTotal α s) 0 := by
  rcases eq_or_ne ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) 0 with h | h
  · rw [h, zero_mul]
    have hzero : zeroRateTotal β s = 0 := by rw [zeroRateTotal, h, mul_zero]
    have hone : 0 ≤ oneRateTotal α s := oneRateTotal_nonneg hα s
    rw [hzero, max_eq_right (by linarith), mul_zero]
  · rw [singleZeroProb]
    field_simp

/-- The paired rates aggregate to the common rate. -/
theorem pairs_mul_pairProb {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (s : Fin n → Bool) :
    ((occupiedCount s : ℕ) : ℝ) * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))
        * pairProb α β τ s
      = τ * min (oneRateTotal α s) (zeroRateTotal β s) := by
  rcases eq_or_ne ((occupiedCount s : ℕ) : ℝ) 0 with h | h
  · rw [h, zero_mul, zero_mul]
    have hone : oneRateTotal α s = 0 := by rw [oneRateTotal, h, mul_zero]
    rw [hone, min_eq_left (zeroRateTotal_nonneg hβ s), mul_zero]
  · rcases eq_or_ne ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) 0 with h' | h'
    · rw [h', mul_zero, zero_mul]
      have hzero : zeroRateTotal β s = 0 := by rw [zeroRateTotal, h', mul_zero]
      rw [hzero, min_eq_right (oneRateTotal_nonneg hα s), mul_zero]
    · rw [pairProb]
      field_simp

/-! ## Evaluating a report against the coupling -/

/-- A single Dirac row evaluates a report at its point. -/
theorem sum_dirac (t : Fin n → Bool) (c : ℝ) (g : (Fin n → Bool) → ℝ) :
    ∑ s' : Fin n → Bool, (if s' = t then c else 0) * g s' = c * g t := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ t (fun s' ↦ c * g s'), if_pos (Finset.mem_univ t)]

/-- Evaluating a report against the nearest-drift kernel's row. -/
theorem nearestDriftKernel_apply (α β τ : ℝ) (s : Fin n → Bool)
    (g : (Fin n → Bool) → ℝ) :
    ∑ s', nearestDriftKernel α β τ s s' * g s'
      = stayProb α β τ s * g s
        + ∑ i, (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
            * g (flipCoord i s)
        + ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
            * g (flipCoord j (flipCoord i s)) := by
  have h1 : ∑ s' : Fin n → Bool, (if s' = s then stayProb α β τ s else 0) * g s'
      = stayProb α β τ s * g s := sum_dirac s _ g
  have h2 : ∑ s' : Fin n → Bool,
      (∑ i, (if s' = flipCoord i s then
        (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s) else 0)) * g s'
      = ∑ i, (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
          * g (flipCoord i s) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ sum_dirac (flipCoord i s) _ g
  have h3 : ∑ s' : Fin n → Bool,
      (∑ i, ∑ j, (if s' = flipCoord j (flipCoord i s) then
        (if s i = true ∧ s j = false then pairProb α β τ s else 0) else 0)) * g s'
      = ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
          * g (flipCoord j (flipCoord i s)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ sum_dirac (flipCoord j (flipCoord i s)) _ g
  simp only [nearestDriftKernel, add_mul, Finset.sum_add_distrib]
  rw [h1, h2, h3]

/-- Every row of the nearest-drift kernel is a probability vector. -/
theorem nearestDriftKernel_sum {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (s : Fin n → Bool) :
    ∑ s', nearestDriftKernel α β τ s s' = 1 := by
  have h := nearestDriftKernel_apply α β τ s (fun _ ↦ (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  have hone : ∑ i, (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
      = ((occupiedCount s : ℕ) : ℝ) * singleOneProb α β τ s
        + ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * singleZeroProb α β τ s := by
    have hpt : ∀ i : Fin n,
        (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
          = (if s i = true then (1 : ℝ) else 0) * singleOneProb α β τ s
            + (if s i = true then (0 : ℝ) else 1) * singleZeroProb α β τ s := by
      intro i
      cases hsi : s i <;> simp
    rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← occupiedCount_eq_sum, occupiedCount_compl]
  have hpair : ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
      = ((occupiedCount s : ℕ) : ℝ) * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))
          * pairProb α β τ s := by
    have hpt : ∀ i j : Fin n, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
        = (if s i = true then (1 : ℝ) else 0) * ((if s j = true then (0 : ℝ) else 1)
            * pairProb α β τ s) := by
      intro i j
      cases hsi : s i <;> cases hsj : s j <;> simp
    rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpt i j]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [occupiedCount_compl, ← occupiedCount_eq_sum]
    ring
  rw [hone, hpair, count_mul_singleOneProb hβ, countCompl_mul_singleZeroProb hα,
    pairs_mul_pairProb hα hβ, stayProb,
    max_eq_min_add_parts (oneRateTotal α s) (zeroRateTotal β s)]
  ring

/-- The nearest-drift kernel is nonnegative when the step is short enough. -/
theorem nearestDriftKernel_nonneg {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (α * (n : ℝ)) ≤ 1) (hshort' : τ * (β * (n : ℝ)) ≤ 1) (s s' : Fin n → Bool) :
    0 ≤ nearestDriftKernel α β τ s s' := by
  have hkle : ((occupiedCount s : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast occupiedCount_le s
  have hk0 : (0 : ℝ) ≤ ((occupiedCount s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hone : oneRateTotal α s ≤ α * (n : ℝ) := by
    rw [oneRateTotal]
    exact mul_le_mul_of_nonneg_left hkle hα
  have hzero : zeroRateTotal β s ≤ β * (n : ℝ) := by
    rw [zeroRateTotal]
    exact mul_le_mul_of_nonneg_left (by linarith) hβ
  have hstay : 0 ≤ stayProb α β τ s := by
    rw [stayProb]
    rcases le_total (oneRateTotal α s) (zeroRateTotal β s) with hle | hle
    · rw [max_eq_right hle]
      nlinarith [hzero, hτ]
    · rw [max_eq_left hle]
      nlinarith [hone, hτ]
  have hsingleOne : 0 ≤ singleOneProb α β τ s := by
    rw [singleOneProb]
    have : 0 ≤ τ * max (oneRateTotal α s - zeroRateTotal β s) 0 :=
      mul_nonneg hτ (le_max_right _ _)
    exact div_nonneg this hk0
  have hsingleZero : 0 ≤ singleZeroProb α β τ s := by
    rw [singleZeroProb]
    have h1 : 0 ≤ τ * max (zeroRateTotal β s - oneRateTotal α s) 0 :=
      mul_nonneg hτ (le_max_right _ _)
    exact div_nonneg h1 (by linarith)
  have hpair : 0 ≤ pairProb α β τ s := by
    rw [pairProb]
    have h1 : 0 ≤ τ * min (oneRateTotal α s) (zeroRateTotal β s) :=
      mul_nonneg hτ (le_min (oneRateTotal_nonneg hα s) (zeroRateTotal_nonneg hβ s))
    exact div_nonneg h1 (mul_nonneg hk0 (by linarith))
  refine add_nonneg (add_nonneg ?_ (Finset.sum_nonneg fun i _ ↦ ?_))
    (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_)
  · split
    · exact hstay
    · exact le_rfl
  · split
    · split
      · exact hsingleOne
      · exact hsingleZero
    · exact le_rfl
  · split
    · split
      · exact hpair
      · exact le_rfl
    · exact le_rfl

/-! ## What a flip does to the count -/

/-- Flipping a one lowers the count by one. -/
theorem occupiedCount_flipCoord_true (i : Fin n) (s : Fin n → Bool) (h : s i = true) :
    occupiedCount (flipCoord i s) + 1 = occupiedCount s := by
  have hset : (Finset.univ.filter fun j ↦ flipCoord i s j = true)
      = (Finset.univ.filter fun j ↦ s j = true).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hj : j = i
    · subst hj
      simp [flipCoord, h]
    · rw [flipCoord_ne i hj]
      simp [hj]
  have hmem : i ∈ Finset.univ.filter fun j ↦ s j = true := by simp [h]
  have hpos : 0 < (Finset.univ.filter fun j ↦ s j = true).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  rw [occupiedCount, occupiedCount, hset, Finset.card_erase_of_mem hmem]
  omega

/-- Flipping a zero raises the count by one. -/
theorem occupiedCount_flipCoord_false (i : Fin n) (s : Fin n → Bool) (h : s i = false) :
    occupiedCount (flipCoord i s) = occupiedCount s + 1 := by
  have hset : (Finset.univ.filter fun j ↦ flipCoord i s j = true)
      = insert i (Finset.univ.filter fun j ↦ s j = true) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = i
    · subst hj
      simp [flipCoord, h]
    · rw [flipCoord_ne i hj]
      simp [hj]
  have hnot : i ∉ Finset.univ.filter fun j ↦ s j = true := by simp [h]
  rw [occupiedCount, occupiedCount, hset, Finset.card_insert_of_notMem hnot]

/-- A paired flip of a one and a zero leaves the count alone. -/
theorem occupiedCount_flipPair (i j : Fin n) (s : Fin n → Bool) (hi : s i = true)
    (hj : s j = false) :
    occupiedCount (flipCoord j (flipCoord i s)) = occupiedCount s := by
  have hji : j ≠ i := by
    intro hEq
    rw [hEq, hi] at hj
    exact Bool.noConfusion hj
  have hfj : flipCoord i s j = false := by
    rw [flipCoord_ne i hji]
    exact hj
  have h1 := occupiedCount_flipCoord_false j (flipCoord i s) hfj
  have h2 := occupiedCount_flipCoord_true i s hi
  omega

/-! ## The induced count process is the nearest-drift chain -/

/-- **DC Lemma 3.2, the count identity.**  Paired flips leave the count alone, and the
singleton flips carry exactly the nearest-drift rates, so the one-step count operator of the
configuration coupling is the nearest-drift operator `driftStep` of
`Descent.Portability.ConvexOrderCoupling`. -/
theorem nearestDriftKernel_count {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (s : Fin n → Bool)
    (g : ℤ → ℝ) :
    ∑ s', nearestDriftKernel α β τ s s' * g ((occupiedCount s' : ℕ) : ℤ)
      = driftStep n α β τ g ((occupiedCount s : ℕ) : ℤ) := by
  rw [nearestDriftKernel_apply]
  have hterm2 : ∑ i, (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
        * g ((occupiedCount (flipCoord i s) : ℕ) : ℤ)
      = ((occupiedCount s : ℕ) : ℝ) * singleOneProb α β τ s
          * g (((occupiedCount s : ℕ) : ℤ) - 1)
        + ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * singleZeroProb α β τ s
          * g (((occupiedCount s : ℕ) : ℤ) + 1) := by
    have hpt : ∀ i : Fin n,
        (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
          * g ((occupiedCount (flipCoord i s) : ℕ) : ℤ)
        = (if s i = true then (1 : ℝ) else 0)
            * (singleOneProb α β τ s * g (((occupiedCount s : ℕ) : ℤ) - 1))
          + (if s i = true then (0 : ℝ) else 1)
            * (singleZeroProb α β τ s * g (((occupiedCount s : ℕ) : ℤ) + 1)) := by
      intro i
      cases hsi : s i
      · have hc := occupiedCount_flipCoord_false i s hsi
        have hcast : ((occupiedCount (flipCoord i s) : ℕ) : ℤ)
            = ((occupiedCount s : ℕ) : ℤ) + 1 := by omega
        rw [hcast]
        simp
      · have hc := occupiedCount_flipCoord_true i s hsi
        have hcast : ((occupiedCount (flipCoord i s) : ℕ) : ℤ)
            = ((occupiedCount s : ℕ) : ℤ) - 1 := by omega
        rw [hcast]
        simp
    rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← occupiedCount_eq_sum, occupiedCount_compl]
    ring
  have hterm3 : ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
        * g ((occupiedCount (flipCoord j (flipCoord i s)) : ℕ) : ℤ)
      = ((occupiedCount s : ℕ) : ℝ) * ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ))
          * pairProb α β τ s * g ((occupiedCount s : ℕ) : ℤ) := by
    have hpt : ∀ i j : Fin n,
        (if s i = true ∧ s j = false then pairProb α β τ s else 0)
          * g ((occupiedCount (flipCoord j (flipCoord i s)) : ℕ) : ℤ)
        = (if s i = true then (1 : ℝ) else 0) * ((if s j = true then (0 : ℝ) else 1)
            * (pairProb α β τ s * g ((occupiedCount s : ℕ) : ℤ))) := by
      intro i j
      cases hsi : s i <;> cases hsj : s j
      · simp
      · simp
      · rw [occupiedCount_flipPair i j s hsi hsj]
        simp
      · simp
    rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpt i j]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [occupiedCount_compl, ← occupiedCount_eq_sum]
    ring
  rw [hterm2, hterm3, count_mul_singleOneProb hβ, countCompl_mul_singleZeroProb hα,
    pairs_mul_pairProb hα hβ, driftStep, nearestDriftGen, upRate_eq_excess,
    downRate_eq_excess, stayProb, max_eq_min_add_parts (oneRateTotal α s) (zeroRateTotal β s)]
  ring

/-- **DC Lemma 3.2 at every horizon.**  The path expectation of any count report under the
configuration coupling is the nearest-drift chain's, so the lower endpoint of the convex-order
envelope is attained by an actual joint sign process. -/
theorem pathExp_nearestDriftKernel {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (g : ℤ → ℝ) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      pathExp (fun _ ↦ nearestDriftKernel α β τ) m hist s
          (fun s' ↦ g ((occupiedCount s' : ℕ) : ℤ))
        = (driftStep n α β τ)^[m] g ((occupiedCount s : ℕ) : ℤ) := by
  induction m with
  | zero =>
    intro hist s
    simp [pathExp]
  | succ m ih =>
    intro hist s
    rw [Function.iterate_succ_apply']
    simp only [pathExp]
    rw [Finset.sum_congr rfl fun s' _ ↦ by rw [ih (s :: hist) s']]
    exact nearestDriftKernel_count hα hβ s _

/-! ## The two endpoints of DC (3.6) -/

/-- **Both endpoints of DC (3.6) are attained by explicit configuration couplings.**  The
nearest-drift coupling of this module realizes the convex-order minimum exactly, while the
synchronous coupling of `Descent.Portability.TurnoverExtremalCouplings` is admissible with the
same coordinate rates, so every grid-convex count report is at least as large under the
synchronous coupling. -/
theorem nearestDrift_pathExp_le_synchronous {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (hα0 : 0 ≤ τ * α) (hα1 : τ * α ≤ 1)
    (hβ0 : 0 ≤ τ * β) (hβ1 : τ * β ≤ 1) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1)) (m : ℕ)
    (hist : List (Fin n → Bool)) (s : Fin n → Bool) :
    pathExp (fun _ ↦ nearestDriftKernel α β τ) m hist s
        (fun s' ↦ f ((occupiedCount s' : ℕ) : ℤ))
      ≤ pathExp (fun _ ↦ synchronousKernel n α β τ) m hist s
          (fun s' ↦ f ((occupiedCount s' : ℕ) : ℤ)) := by
  rw [pathExp_nearestDriftKernel hα hβ f m hist s]
  exact synchronous_pathExp_nearestDrift_le n α β τ hα hβ hτ hshort hα0 hα1 hβ0 hβ1 f hf m
    hist s

/-! ## Admissibility: every coordinate flips at its prescribed rate -/

/-- The one-group excess and the common rate add to the one-group total. -/
theorem max_sub_add_min (A B : ℝ) : max (A - B) 0 + min A B = A := by
  rcases le_total A B with h | h
  · rw [max_eq_right (by linarith : A - B ≤ 0), min_eq_left h]
    ring
  · rw [max_eq_left (by linarith : 0 ≤ A - B), min_eq_right h]
    ring

/-- The zero-group excess and the common rate add to the zero-group total. -/
theorem min_add_max_sub (A B : ℝ) : max (B - A) 0 + min A B = B := by
  rw [min_comm]
  exact max_sub_add_min B A

/-- A configuration with a one has a nonzero count. -/
theorem count_ne_zero_of_true (s : Fin n → Bool) (i₀ : Fin n) (h : s i₀ = true) :
    ((occupiedCount s : ℕ) : ℝ) ≠ 0 := by
  have hpos : 0 < occupiedCount s :=
    Finset.card_pos.mpr ⟨i₀, by simp [h]⟩
  positivity

/-- A configuration with a zero has a nonzero complementary count. -/
theorem countCompl_ne_zero_of_false (s : Fin n → Bool) (i₀ : Fin n) (h : s i₀ = false) :
    ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) ≠ 0 := by
  have hsub : (Finset.univ.filter fun j ↦ s j = true) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr ?_
    intro hEq
    have hmem : i₀ ∈ Finset.univ.filter fun j ↦ s j = true := by
      rw [hEq]
      exact Finset.mem_univ i₀
    simp [h] at hmem
  have hlt : occupiedCount s < n := by
    have hcard := Finset.card_lt_card hsub
    simpa [occupiedCount] using hcard
  have hcast : ((occupiedCount s : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  intro hzero
  linarith

/-- The paired rates seen by one fixed zero aggregate over the ones. -/
theorem count_mul_pairProb {α β τ : ℝ} (hβ : 0 ≤ β) (s : Fin n → Bool)
    (hk : ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) ≠ 0) :
    ((occupiedCount s : ℕ) : ℝ) * pairProb α β τ s
      = τ * min (oneRateTotal α s) (zeroRateTotal β s)
        / ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) := by
  rcases eq_or_ne ((occupiedCount s : ℕ) : ℝ) 0 with h | h
  · rw [h, zero_mul]
    have hone : oneRateTotal α s = 0 := by rw [oneRateTotal, h, mul_zero]
    rw [hone, min_eq_left (zeroRateTotal_nonneg hβ s), mul_zero, zero_div]
  · rw [pairProb]
    field_simp

/-- The paired rates seen by one fixed one aggregate over the zeros. -/
theorem countCompl_mul_pairProb {α β τ : ℝ} (hα : 0 ≤ α) (s : Fin n → Bool)
    (hk : ((occupiedCount s : ℕ) : ℝ) ≠ 0) :
    ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * pairProb α β τ s
      = τ * min (oneRateTotal α s) (zeroRateTotal β s) / ((occupiedCount s : ℕ) : ℝ) := by
  rcases eq_or_ne ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) 0 with h | h
  · rw [h, zero_mul]
    have hzero : zeroRateTotal β s = 0 := by rw [zeroRateTotal, h, mul_zero]
    rw [hzero, min_eq_right (oneRateTotal_nonneg hα s), mul_zero, zero_div]
  · rw [pairProb]
    field_simp

/-- The indicator that a single coordinate flip moved a fixed coordinate. -/
theorem flip_indicator_single (s : Fin n → Bool) (i i₀ : Fin n) :
    (if flipCoord i s i₀ = s i₀ then (0 : ℝ) else 1) = if i = i₀ then 1 else 0 := by
  by_cases h : i = i₀
  · rw [if_pos h, ← h, flipCoord_self]
    cases hsi : s i <;> simp
  · rw [if_neg h, flipCoord_ne i (Ne.symm h) s, if_pos rfl]

/-- **DC Lemma 3.2, admissibility (DC (3.2)).**  Each coordinate flips with probability exactly
`τα` when it is one and `τβ` when it is zero: the paired rate of a one and its singleton rate
add to `α`, and likewise for a zero.  The coupling therefore lies in the admissible class that
`Descent.Portability.ConvexOrderCoupling` compares against. -/
theorem nearestDriftKernel_flip {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (s : Fin n → Bool)
    (i₀ : Fin n) :
    ∑ s', (if s' i₀ = s i₀ then (0 : ℝ) else nearestDriftKernel α β τ s s')
      = τ * (if s i₀ = true then α else β) := by
  have hpt : ∀ s' : Fin n → Bool,
      (if s' i₀ = s i₀ then (0 : ℝ) else nearestDriftKernel α β τ s s')
        = nearestDriftKernel α β τ s s' * (if s' i₀ = s i₀ then (0 : ℝ) else 1) := by
    intro s'
    by_cases h : s' i₀ = s i₀ <;> simp [h]
  rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', nearestDriftKernel_apply]
  have hstay : stayProb α β τ s * (if s i₀ = s i₀ then (0 : ℝ) else 1) = 0 := by simp
  have h2 : ∑ i, (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
        * (if flipCoord i s i₀ = s i₀ then (0 : ℝ) else 1)
      = (if s i₀ = true then singleOneProb α β τ s else singleZeroProb α β τ s) := by
    have hpt2 : ∀ i : Fin n,
        (if s i = true then singleOneProb α β τ s else singleZeroProb α β τ s)
          * (if flipCoord i s i₀ = s i₀ then (0 : ℝ) else 1)
        = if i = i₀ then
            (if s i₀ = true then singleOneProb α β τ s else singleZeroProb α β τ s) else 0 := by
      intro i
      rw [flip_indicator_single]
      by_cases h : i = i₀
      · rw [if_pos h, if_pos h, h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl fun i _ ↦ hpt2 i, Finset.sum_ite_eq' Finset.univ i₀,
      if_pos (Finset.mem_univ i₀)]
  by_cases hi0 : s i₀ = true
  · have hk := count_ne_zero_of_true s i₀ hi0
    have h3 : ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
          * (if flipCoord j (flipCoord i s) i₀ = s i₀ then (0 : ℝ) else 1)
        = ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * pairProb α β τ s := by
      have hpt3 : ∀ i j : Fin n,
          (if s i = true ∧ s j = false then pairProb α β τ s else 0)
            * (if flipCoord j (flipCoord i s) i₀ = s i₀ then (0 : ℝ) else 1)
          = if i = i₀ then ((if s j = true then (0 : ℝ) else 1) * pairProb α β τ s) else 0 := by
        intro i j
        by_cases hsj : s j = true
        · simp [hsj]
        · have hsjf : s j = false := by
            cases hv : s j
            · rfl
            · exact absurd hv hsj
          have hji0 : i₀ ≠ j := by
            intro hEq
            rw [← hEq, hi0] at hsjf
            exact Bool.noConfusion hsjf
          rw [flipCoord_ne j hji0 (flipCoord i s)]
          by_cases hii : i = i₀
          · rw [hii, flipCoord_self, hi0]
            simp [hsjf]
          · rw [flipCoord_ne i (Ne.symm hii) s, if_pos rfl, if_neg hii, mul_zero]
      have hinner : ∀ i : Fin n,
          ∑ j, (if i = i₀ then ((if s j = true then (0 : ℝ) else 1) * pairProb α β τ s) else 0)
            = if i = i₀ then
                ((n : ℝ) - ((occupiedCount s : ℕ) : ℝ)) * pairProb α β τ s else 0 := by
        intro i
        by_cases h : i = i₀
        · simp only [if_pos h]
          rw [← Finset.sum_mul, occupiedCount_compl]
        · simp [h]
      rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpt3 i j,
        Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_ite_eq' Finset.univ i₀,
        if_pos (Finset.mem_univ i₀)]
    rw [hstay, h2, h3]
    simp only [if_pos hi0]
    rw [countCompl_mul_pairProb hα s hk, singleOneProb, zero_add, ← add_div, ← mul_add,
      max_sub_add_min, oneRateTotal]
    field_simp
  · have hi0f : s i₀ = false := by
      cases hv : s i₀
      · rfl
      · exact absurd hv hi0
    have hk := countCompl_ne_zero_of_false s i₀ hi0f
    have h3 : ∑ i, ∑ j, (if s i = true ∧ s j = false then pairProb α β τ s else 0)
          * (if flipCoord j (flipCoord i s) i₀ = s i₀ then (0 : ℝ) else 1)
        = ((occupiedCount s : ℕ) : ℝ) * pairProb α β τ s := by
      have hpt3 : ∀ i j : Fin n,
          (if s i = true ∧ s j = false then pairProb α β τ s else 0)
            * (if flipCoord j (flipCoord i s) i₀ = s i₀ then (0 : ℝ) else 1)
          = if j = i₀ then ((if s i = true then (1 : ℝ) else 0) * pairProb α β τ s) else 0 := by
        intro i j
        by_cases hsi : s i = true
        · have hii0 : ¬ (i = i₀) := by
            intro hEq
            rw [hEq, hi0f] at hsi
            exact Bool.noConfusion hsi
          by_cases hj : j = i₀
          · rw [hj, flipCoord_self, flipCoord_ne i (Ne.symm hii0) s, hi0f]
            simp [hsi]
          · have hjne : i₀ ≠ j := fun hEq ↦ hj hEq.symm
            rw [flipCoord_ne j hjne (flipCoord i s),
              flipCoord_ne i (Ne.symm hii0) s, if_pos rfl, if_neg hj, mul_zero]
        · simp [hsi]
      have hinner : ∀ i : Fin n,
          ∑ j, (if j = i₀ then ((if s i = true then (1 : ℝ) else 0) * pairProb α β τ s) else 0)
            = (if s i = true then (1 : ℝ) else 0) * pairProb α β τ s := by
        intro i
        rw [Finset.sum_ite_eq' Finset.univ i₀, if_pos (Finset.mem_univ i₀)]
      rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hpt3 i j,
        Finset.sum_congr rfl fun i _ ↦ hinner i, ← Finset.sum_mul, ← occupiedCount_eq_sum]
    rw [hstay, h2, h3]
    simp only [if_neg hi0]
    rw [count_mul_pairProb hβ s hk, singleZeroProb, zero_add, ← add_div, ← mul_add,
      min_add_max_sub, zeroRateTotal]
    field_simp

end

end Descent.Portability.NearestDriftConfigurationCoupling

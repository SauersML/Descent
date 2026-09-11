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

end

end Descent.Portability.NearestDriftConfigurationCoupling

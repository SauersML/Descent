/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
# Identification from measured haplotype pairings

Theorem 11 of *Beyond Ancestry Tags*. A symmetric relation records response-
measured diplotypes. Loops are allowed and denote homozygotes. The offset is
known. An odd closed walk is an equivalent, computationally convenient witness
of non-bipartiteness; in particular an odd cycle or a loop is such a witness.
No historical sequence observation is treated as a response measurement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

variable {V : Type*}

/-- Walks retain their length, including homozygous edges. -/
inductive PairingWalk (R : V → V → Prop) : V → V → ℕ → Prop
  | nil (u : V) : PairingWalk R u u 0
  | cons {u v w : V} {n : ℕ} : R u v → PairingWalk R v w n → PairingWalk R u w (n + 1)

def PairingConnected (R : V → V → Prop) : Prop := ∀ u v, ∃ n, PairingWalk R u v n

def PairingBipartite (R : V → V → Prop) : Prop :=
  ∃ color : V → Bool, ∀ u v, R u v → color u ≠ color v

/-- Kernel of the sum-incidence design. A loop imposes `2 * a u = 0`. -/
def PairingNull (R : V → V → Prop) (a : V → ℝ) : Prop :=
  ∀ u v, R u v → a u + a v = 0

lemma PairingWalk.append {R : V → V → Prop} {u v w : V} {n m : ℕ}
    (h : PairingWalk R u v n) (k : PairingWalk R v w m) : PairingWalk R u w (n + m) := by
  induction h with
  | nil => simpa using k
  | cons he hp ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      PairingWalk.cons he (ih k)

lemma PairingWalk.reverse {R : V → V → Prop} (hs : Symmetric R)
    {u v : V} {n : ℕ} (h : PairingWalk R u v n) : PairingWalk R v u n := by
  induction h with
  | nil u => exact .nil u
  | cons he hp ih => exact ih.append (.cons (hs he) (.nil _))

lemma PairingWalk.alternating {R : V → V → Prop} {a : V → ℝ}
    (ha : PairingNull R a) {u v : V} {n : ℕ} (h : PairingWalk R u v n) :
    a u = (-1 : ℝ) ^ n * a v := by
  induction h with
  | nil => simp
  | cons he hp ih =>
      have heq := ha _ _ he
      rw [pow_succ]
      rw [ih] at heq
      linarith

lemma pairing_null_zero_of_anchor {R : V → V → Prop} (hc : PairingConnected R)
    {a : V → ℝ} (ha : PairingNull R a) (root : V) (hz : a root = 0) : a = 0 := by
  funext v
  obtain ⟨n, hn⟩ := hc v root
  simpa [hz] using hn.alternating ha

lemma pairing_null_zero_of_odd {R : V → V → Prop} (hc : PairingConnected R)
    {a : V → ℝ} (ha : PairingNull R a) {v : V} {n : ℕ}
    (hw : PairingWalk R v v n) (ho : Odd n) : a = 0 := by
  have h := hw.alternating ha
  rw [ho.neg_one_pow] at h
  exact pairing_null_zero_of_anchor hc ha v (by linarith)

/-- With no odd closed walk, path parity constructs an actual two-coloring. -/
theorem pairing_bipartite_of_no_odd {R : V → V → Prop} (hs : Symmetric R)
    (hc : PairingConnected R) (root : V)
    (hno : ¬ ∃ v n, PairingWalk R v v n ∧ Odd n) : PairingBipartite R := by
  classical
  choose len path using (hc root)
  refine ⟨fun v => decide (len v % 2 = 0), ?_⟩
  intro u v huv heq
  have hp : (len u % 2 = 0) ↔ (len v % 2 = 0) := of_decide_eq_true
    (by simpa using congrArg (fun b => decide (len u % 2 = 0) == b) heq)
  have hw := ((path u).append (.cons huv (.nil v))).append ((path v).reverse hs)
  apply hno
  refine ⟨root, len u + 1 + len v, hw, Nat.odd_iff.mpr ?_⟩
  omega

/-- A two-coloring supplies the unidentified direction with values `+1,-1`. -/
lemma pairing_bipartite_null {R : V → V → Prop} (hb : PairingBipartite R) :
    ∃ a : V → ℝ, PairingNull R a ∧ ∀ v, a v ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨fun v => if b v then 1 else -1, ?_, ?_⟩
  · intro u v huv
    have h := hb u v huv
    cases hu : b u <;> cases hv : b v <;> simp_all
  · intro v; dsimp; split <;> norm_num

/-- The complete kernel of a connected bipartite design is one-dimensional. -/
theorem pairing_kernel_one_dimension {R : V → V → Prop} (hc : PairingConnected R)
    (root : V) (sign : V → ℝ) (hs : PairingNull R sign) (hunit : ∀ v, sign v ^ 2 = 1)
    (a : V → ℝ) : PairingNull R a ↔ ∃ c : ℝ, a = fun v => c * sign v := by
  constructor
  · intro ha
    let c := a root / sign root
    have hne : sign root ≠ 0 := by intro h; simpa [h] using hunit root
    have hz : (fun v => a v - c * sign v) = 0 := by
      refine pairing_null_zero_of_anchor hc ?_ root ?_
      · intro u v huv
        have hu := ha u v huv
        have hv := hs u v huv
        dsimp
        calc
          _ = (a u + a v) - c * (sign u + sign v) := by ring
          _ = 0 := by rw [hu, hv]; ring
      · dsimp [c]; field_simp; ring
    refine ⟨c, ?_⟩
    funext v
    have := congrFun hz v
    simpa only [Pi.zero_apply, sub_eq_zero] using this
  · rintro ⟨c, rfl⟩ u v huv
    dsimp
    rw [← mul_add, hs u v huv, mul_zero]

/-- Theorem 11: exact identification iff an odd closed walk exists. This covers
odd cycles and homozygous loops and proves the converse via path coloring. -/
theorem pairing_identified_iff_odd {R : V → V → Prop} (hs : Symmetric R)
    (hc : PairingConnected R) (root : V) :
    (∀ a : V → ℝ, PairingNull R a → a = 0) ↔
      ∃ v n, PairingWalk R v v n ∧ Odd n := by
  constructor
  · intro hi
    by_contra hno
    obtain ⟨a, ha, hu⟩ := pairing_bipartite_null (pairing_bipartite_of_no_odd hs hc root hno)
    have hz := congrFun (hi a ha) root
    have h := hu root
    simp only [Pi.zero_apply] at hz
    simp [hz] at h
  · rintro ⟨v, n, hw, ho⟩ a ha
    exact pairing_null_zero_of_odd hc ha hw ho

/-- A measured homozygote anchors the entire connected response design. -/
theorem pairing_homozygote_identifies {R : V → V → Prop} (hc : PairingConnected R)
    (root : V) (hr : R root root) (a : V → ℝ) (ha : PairingNull R a) : a = 0 := by
  apply pairing_null_zero_of_anchor hc ha root
  have := ha root root hr
  linarith

/-- The partner-switch triangle recovers each contribution with known offset. -/
theorem pairing_triangle_recovery (a b c : ℝ) :
    ((a + b) + (a + c) - (b + c)) / 2 = a := by ring

/-- The unknown-offset gauge persists for every pairing design. -/
theorem pairing_offset_gauge (offset a b c : ℝ) :
    (offset - 2 * c) + (a + c) + (b + c) = offset + a + b := by ring

end Descent.Portability.ArchaicPrediction

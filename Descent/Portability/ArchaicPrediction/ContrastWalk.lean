/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.ResponseGraph

assert_below Descent.Decision Descent.Program

/-!
# Path independence of measured response differences

Theorem 9 in graph language. Signed walks allow either orientation of each
measured edge, parallel comparisons, and loops. A cycle defect is the signed
sum on a closed walk. A potential is constructed from root-to-vertex paths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

variable {V A : Type*}

inductive ContrastWalk (source target : A → V) (d : A → ℝ) : V → V → ℝ → Prop
  | nil (v : V) : ContrastWalk source target d v v 0
  | forward (e : A) {v : V} {s : ℝ} : ContrastWalk source target d (target e) v s →
      ContrastWalk source target d (source e) v (d e + s)
  | backward (e : A) {v : V} {s : ℝ} : ContrastWalk source target d (source e) v s →
      ContrastWalk source target d (target e) v (-d e + s)

lemma ContrastWalk.append {source target : A → V} {d : A → ℝ} {u v w : V} {s t : ℝ}
    (h : ContrastWalk source target d u v s) (k : ContrastWalk source target d v w t) :
    ContrastWalk source target d u w (s + t) := by
  induction h with
  | nil => simpa using k
  | forward e hp ih => simpa [add_assoc] using ContrastWalk.forward e (ih k)
  | backward e hp ih => simpa [add_assoc] using ContrastWalk.backward e (ih k)

lemma ContrastWalk.reverse {source target : A → V} {d : A → ℝ} {u v : V} {s : ℝ}
    (h : ContrastWalk source target d u v s) : ContrastWalk source target d v u (-s) := by
  induction h with
  | nil => simpa using ContrastWalk.nil _
  | forward e hp ih =>
      simpa [neg_add, add_comm] using ih.append (ContrastWalk.backward e (ContrastWalk.nil _))
  | backward e hp ih =>
      simpa [neg_add, add_comm] using ih.append (ContrastWalk.forward e (ContrastWalk.nil _))

lemma contrastWalk_exists {source target : A → V} (d : A → ℝ) {u v : V} {n : ℕ}
    (h : PairingWalk (comparisonAdjacent source target) u v n) :
    ∃ s, ContrastWalk source target d u v s := by
  induction h with
  | nil u => exact ⟨0, .nil u⟩
  | cons he hp ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨e, he | he⟩ := he
      · obtain ⟨rfl, rfl⟩ := he
        exact ⟨d e + s, .forward e hs⟩
      · obtain ⟨rfl, rfl⟩ := he
        exact ⟨-d e + s, .backward e hs⟩

lemma ContrastWalk.potential {source target : A → V} {d : A → ℝ} (m : V → ℝ)
    (hm : ∀ e, d e = m (target e) - m (source e)) {u v : V} {s : ℝ}
    (h : ContrastWalk source target d u v s) : s = m v - m u := by
  induction h with
  | nil => ring
  | forward e hp ih => rw [hm, ih]; ring
  | backward e hp ih => rw [hm, ih]; ring

/-- Theorem 9: all signed cycle defects vanish iff a common response map exists. -/
theorem zero_cycles_iff_response_map (source target : A → V) (d : A → ℝ)
    (hc : PairingConnected (comparisonAdjacent source target)) (root : V) :
    (∀ u s, ContrastWalk source target d u u s → s = 0) ↔
      ∃ m : V → ℝ, ∀ e, d e = m (target e) - m (source e) := by
  constructor
  · intro hz
    have hp (v : V) : ∃ s, ContrastWalk source target d root v s := by
      obtain ⟨n, hn⟩ := hc root v
      exact contrastWalk_exists d hn
    choose m hm using hp
    refine ⟨m, ?_⟩
    intro e
    have hpath := ((hm (source e)).append
      (ContrastWalk.forward e (ContrastWalk.nil (target e)))).append ((hm (target e)).reverse)
    have h := hz root _ hpath
    linarith
  · rintro ⟨m, hm⟩ u s hs
    simpa using hs.potential m hm

end Descent.Portability.ArchaicPrediction

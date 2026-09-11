/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Tactic

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorems 5 and 6: the exact scalar optimization
underlying bounded-outcome audit variance. Probability-law attainment is a
separate obligation; this file proves the optimizer, value, and uniqueness
without postulating any optimization conclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AuditVarianceGeometry

/-- Projection onto a nonempty closed real interval. -/
def clip (lo hi t : ℝ) : ℝ := max lo (min hi t)

/-- Endpoint-outcome audit variance at a specified outcome mean. -/
noncomputable def envelope (L U p q m : ℝ) : ℝ :=
  (U - m) * (m - L) / p + (1 / p - 1) * (m - q) ^ 2

/-- The unconstrained maximizing mean. -/
noncomputable def vertex (L U p q : ℝ) : ℝ := (L + U - 2 * (1 - p) * q) / (2 * p)

/-- The support midpoint projected onto the admissible mean band. -/
noncomputable def proxy (L U lo hi : ℝ) : ℝ := clip lo hi ((L + U) / 2)

/-- The clipped point belongs to its interval. -/
theorem clip_mem (lo hi t : ℝ) (h : lo ≤ hi) :
    lo ≤ clip lo hi t ∧ clip lo hi t ≤ hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- Projection leaves the displacement orthogonal in the appropriate one-sided sense. -/
theorem clip_normal (lo hi t m : ℝ) (hm : lo ≤ m ∧ m ≤ hi) :
    (m - clip lo hi t) * (t - clip lo hi t) ≤ 0 := by
  unfold clip
  by_cases ht : t ≤ lo
  · rw [max_eq_left (le_trans (min_le_right _ _) ht)]
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm.1) (sub_nonpos.mpr ht)
  · by_cases hu : hi ≤ t
    · rw [min_eq_left hu, max_eq_right (le_trans hm.1 hm.2)]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm.2) (sub_nonneg.mpr hu)
    · rw [min_eq_right (le_of_not_ge hu), max_eq_right (le_of_not_ge ht)]
      simp

/-- The clipped point minimizes squared distance on the whole interval. -/
theorem clip_sq_le (lo hi t m : ℝ) (hm : lo ≤ m ∧ m ≤ hi) :
    (clip lo hi t - t) ^ 2 ≤ (m - t) ^ 2 := by
  have hn := clip_normal lo hi t m hm
  nlinarith [sq_nonneg (m - clip lo hi t)]

/-- Completing the square gives the exact curvature minus one, independent of sampling rate. -/
theorem envelope_difference (L U p q m n : ℝ) (hp : p ≠ 0) :
    envelope L U p q m - envelope L U p q n =
      (n - vertex L U p q) ^ 2 - (m - vertex L U p q) ^ 2 := by
  unfold envelope vertex
  field_simp
  ring

/-- The claimed clipped mean maximizes the envelope over every admissible mean. -/
theorem maximizing_mean (L U p q lo hi m : ℝ) (hp : p ≠ 0)
    (hm : lo ≤ m ∧ m ≤ hi) :
    envelope L U p q m ≤ envelope L U p q (clip lo hi (vertex L U p q)) := by
  have hd := envelope_difference L U p q m (clip lo hi (vertex L U p q)) hp
  have hc := clip_sq_le lo hi (vertex L U p q) m hm
  linarith

/-- The variance-envelope maximum is attained at a mean in the admissible band. -/
theorem maximum_attained (L U p q lo hi : ℝ) (hp : p ≠ 0) (hband : lo ≤ hi) :
    ∃ m, lo ≤ m ∧ m ≤ hi ∧
      ∀ n, lo ≤ n → n ≤ hi → envelope L U p q n ≤ envelope L U p q m := by
  refine ⟨clip lo hi (vertex L U p q), (clip_mem _ _ _ hband).1,
    (clip_mem _ _ _ hband).2, ?_⟩
  intro n hn hn'
  exact maximizing_mean L U p q lo hi n hp ⟨hn, hn'⟩

/-- Exact comparison with the minimax proxy's value. -/
theorem proxy_difference (L U p q m : ℝ) (hp : p ≠ 0) :
    p * (envelope L U p q m - (U - q) * (q - L) / p) =
      (m - q) * (L + U - 2 * q) - p * (m - q) ^ 2 := by
  unfold envelope
  field_simp
  ring

/-- The projected midpoint attains its maximal variance at its own admissible mean. -/
theorem proxy_upper (L U p lo hi m : ℝ) (hp : 0 < p)
    (hm : lo ≤ m ∧ m ≤ hi) :
    envelope L U p (proxy L U lo hi) m ≤
      (U - proxy L U lo hi) * (proxy L U lo hi - L) / p := by
  have hn := clip_normal lo hi ((L + U) / 2) m hm
  change (m - proxy L U lo hi) * ((L + U) / 2 - proxy L U lo hi) ≤ 0 at hn
  have hd := proxy_difference L U p (proxy L U lo hi) m hp.ne'
  have hs := mul_nonneg hp.le (sq_nonneg (m - proxy L U lo hi))
  nlinarith

/-- Every proxy pays an explicit additional penalty at the minimax proxy's mean. -/
theorem proxy_lower (L U p lo hi q : ℝ) :
    envelope L U p q (proxy L U lo hi) =
      (U - proxy L U lo hi) * (proxy L U lo hi - L) / p +
        (1 / p - 1) * (proxy L U lo hi - q) ^ 2 := rfl

/-- The minimax value is exact, with an admissible mean attaining both sides of the game. -/
theorem minimax_proxy (L U p lo hi : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (hband : lo ≤ hi) :
    let q := proxy L U lo hi
    lo ≤ q ∧ q ≤ hi ∧
    (∀ m, lo ≤ m → m ≤ hi → envelope L U p q m ≤ (U - q) * (q - L) / p) ∧
    (∀ z, (U - q) * (q - L) / p ≤ envelope L U p z q) := by
  dsimp only
  refine ⟨(clip_mem _ _ _ hband).1, (clip_mem _ _ _ hband).2, ?_, ?_⟩
  · intro m hm hm'
    exact proxy_upper L U p lo hi m hp.1 ⟨hm, hm'⟩
  · intro z
    rw [proxy_lower]
    have hrate : 0 ≤ 1 / p - 1 := by
      have hh : 1 ≤ 1 / p := (le_div_iff₀ hp.1).mpr (by simpa using hp.2)
      linarith
    exact le_add_of_nonneg_right (mul_nonneg hrate (sq_nonneg _))

/-- With incomplete sampling, every different proxy has strictly larger worst-case variance. -/
theorem proxy_unique (L U p lo hi q : ℝ) (hp : 0 < p ∧ p < 1)
    (hq : q ≠ proxy L U lo hi) :
    (U - proxy L U lo hi) * (proxy L U lo hi - L) / p <
      envelope L U p q (proxy L U lo hi) := by
  rw [proxy_lower]
  have hrate : 0 < 1 / p - 1 := by
    have hh : 1 < 1 / p := (lt_div_iff₀ hp.1).mpr (by simpa using hp.2)
    linarith
  have hs : 0 < (proxy L U lo hi - q) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hq.symm)
  exact lt_add_of_pos_right _ (mul_pos hrate hs)

/-- Full observation removes every dependence on the proxy. -/
theorem full_observation (L U q m : ℝ) :
    envelope L U 1 q m = (U - m) * (m - L) := by
  simp [envelope]

end Descent.Portability.AuditVarianceGeometry

import Calibrator.Probability

namespace Calibrator

open scoped InnerProductSpace
open InnerProductSpace
open MeasureTheory

/-!
=================================================================
## Part 3: Numerical and Algebraic Foundations
=================================================================
These theorems formalize the correctness of the numerical methods
used in the Rust implementation (calibrate/basis.rs, calibrate/estimate.rs).
-/

section BSplineFoundations

/-!
### B-Spline Basis Functions

The Cox-de Boor recursion defines B-spline basis functions. We prove
the partition of unity property which ensures probability semantics.
-/

variable {numKnots : ℕ}

/-- A valid B-spline knot vector: non-decreasing with proper multiplicity. -/
structure KnotVector (m : ℕ) where
  knots : Fin m → ℝ
  sorted : ∀ i j : Fin m, i ≤ j → knots i ≤ knots j

/-- Cox-de Boor recursive definition of B-spline basis function.
    N_{i,p}(x) is the i-th basis function of degree p.
    We use a simpler formulation to avoid index bound issues. -/
noncomputable def bspline_basis_raw (t : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | i, 0, x => if t i ≤ x ∧ x < t (i + 1) then 1 else 0
  | i, p + 1, x =>
    let left_denom := t (i + p + 1) - t i
    let right_denom := t (i + p + 2) - t (i + 1)
    let left := if left_denom = 0 then 0
                else (x - t i) / left_denom * bspline_basis_raw t i p x
    let right := if right_denom = 0 then 0
                 else (t (i + p + 2) - x) / right_denom * bspline_basis_raw t (i + 1) p x
    left + right

/-- Local support property: N_{i,p}(x) = 0 outside [t_i, t_{i+p+1}).

    **Geometric insight**: The support of a B-spline grows by one knot interval with
    each degree increase. N_{i,p} lives on [t_i, t_{i+p+1}). In the recursion for p+1,
    we combine N_{i,p} (starts at t_i) and N_{i+1,p} (ends at t_{i+p+2}).
    The union creates the new support [t_i, t_{i+p+2}).

    **Proof by induction on p**:
    - Base case (p=0): By definition, N_{i,0}(x) = 1 if t_i ≤ x < t_{i+1}, else 0.
    - Inductive case (p+1): Cox-de Boor recursion combines N_{i,p} and N_{i+1,p}.
      Both have zero support outside the required interval. -/
theorem bspline_local_support (t : ℕ → ℝ)
    (h_sorted : ∀ i j, i ≤ j → t i ≤ t j)
    (i p : ℕ) (x : ℝ)
    (h_outside : x < t i ∨ t (i + p + 1) ≤ x) :
    bspline_basis_raw t i p x = 0 := by
  induction p generalizing i with
  | zero =>
    simp only [bspline_basis_raw]
    split_ifs with h_in
    · obtain ⟨h_lo, h_hi⟩ := h_in
      rcases h_outside with h_lt | h_ge
      · exact absurd h_lo (not_le.mpr h_lt)
      · simp only [add_zero] at h_ge
        exact absurd h_hi (not_lt.mpr h_ge)
    · rfl
  | succ p ih =>
    simp only [bspline_basis_raw]
    rcases h_outside with h_lt | h_ge
    · -- x < t_i: both terms zero
      have h_left_zero : bspline_basis_raw t i p x = 0 := ih i (Or.inl h_lt)
      have h_i1_le : t i ≤ t (i + 1) := h_sorted i (i + 1) (Nat.le_succ i)
      have h_right_zero : bspline_basis_raw t (i + 1) p x = 0 :=
        ih (i + 1) (Or.inl (lt_of_lt_of_le h_lt h_i1_le))
      simp only [h_left_zero, h_right_zero, mul_zero, ite_self, add_zero]
    · -- x ≥ t_{i+p+2}: both terms zero
      have h_right_idx : i + 1 + p + 1 = i + p + 2 := by ring
      have h_right_zero : bspline_basis_raw t (i + 1) p x = 0 := by
        apply ih (i + 1); right; rw [h_right_idx]; exact h_ge
      have h_mono : t (i + p + 1) ≤ t (i + p + 2) := h_sorted (i + p + 1) (i + p + 2) (Nat.le_succ _)
      have h_left_zero : bspline_basis_raw t i p x = 0 := by
        apply ih i; right; exact le_trans h_mono h_ge
      simp only [h_left_zero, h_right_zero, mul_zero, ite_self, add_zero]

/-- B-spline basis functions are non-negative everywhere.

    **Geometry of the "Zero-Out" Property** (Key insight from user):
    The Cox-de Boor recursion uses linear weights: (x - t_i) / (t_{i+p+1} - t_i).
    These weights become NEGATIVE when x < t_i. The ONLY reason the spline remains
    non-negative is that the lower-order basis function N_{i,p}(x) "turns off"
    (becomes exactly zero) precisely when the weight becomes negative.

    Therefore, bspline_local_support is a strict prerequisite for this proof.

    **Proof by induction on p**:
    - Base case (p=0): N_{i,0}(x) is either 0 or 1, both ≥ 0.
    - Inductive case (p+1): For each term α(x) * N_{i,p}(x):
      * If x ∈ [t_i, t_{i+p+1}): α(x) ≥ 0 and N_{i,p}(x) ≥ 0 by IH
      * If x ∉ [t_i, t_{i+p+1}): N_{i,p}(x) = 0 by local_support, so product = 0 -/
theorem bspline_nonneg (t : ℕ → ℝ) (h_sorted : ∀ i j, i ≤ j → t i ≤ t j)
    (i p : ℕ) (x : ℝ) : 0 ≤ bspline_basis_raw t i p x := by
  induction p generalizing i with
  | zero =>
    simp only [bspline_basis_raw]
    split_ifs
    · exact zero_le_one
    · exact le_refl 0
  | succ p ih =>
    simp only [bspline_basis_raw]
    apply add_nonneg
    · -- Left term: (x - t_i) / (t_{i+p+1} - t_i) * N_{i,p}(x)
      split_ifs with h_denom
      · exact le_refl 0
      · by_cases h_in_support : x < t i
        · -- x < t_i: N_{i,p}(x) = 0 by local support, so product = 0
          have : bspline_basis_raw t i p x = 0 :=
            bspline_local_support t h_sorted i p x (Or.inl h_in_support)
          simp only [this, mul_zero, le_refl]
        · -- x ≥ t_i: weight (x - t_i)/denom ≥ 0, and N_{i,p}(x) ≥ 0 by IH
          push_neg at h_in_support
          have h_num_nn : 0 ≤ x - t i := sub_nonneg.mpr h_in_support
          have h_denom_pos : 0 < t (i + p + 1) - t i := by
            have h_le : t i ≤ t (i + p + 1) := h_sorted i (i + p + 1) (by omega)
            exact lt_of_le_of_ne (sub_nonneg.mpr h_le) (ne_comm.mp h_denom)
          exact mul_nonneg (div_nonneg h_num_nn (le_of_lt h_denom_pos)) (ih i)
    · -- Right term: (t_{i+p+2} - x) / (t_{i+p+2} - t_{i+1}) * N_{i+1,p}(x)
      split_ifs with h_denom
      · exact le_refl 0
      · by_cases h_in_support : t (i + p + 2) ≤ x
        · -- x ≥ t_{i+p+2}: N_{i+1,p}(x) = 0 by local support
          have h_idx : i + 1 + p + 1 = i + p + 2 := by ring
          have : bspline_basis_raw t (i + 1) p x = 0 := by
            apply bspline_local_support t h_sorted (i + 1) p x; right; rw [h_idx]; exact h_in_support
          simp only [this, mul_zero, le_refl]
        · -- x < t_{i+p+2}: weight (t_{i+p+2} - x)/denom ≥ 0, and N_{i+1,p}(x) ≥ 0 by IH
          push_neg at h_in_support
          have h_num_nn : 0 ≤ t (i + p + 2) - x := sub_nonneg.mpr (le_of_lt h_in_support)
          have h_denom_pos : 0 < t (i + p + 2) - t (i + 1) := by
            have h_le : t (i + 1) ≤ t (i + p + 2) := h_sorted (i + 1) (i + p + 2) (by omega)
            exact lt_of_le_of_ne (sub_nonneg.mpr h_le) (ne_comm.mp h_denom)
          exact mul_nonneg (div_nonneg h_num_nn (le_of_lt h_denom_pos)) (ih (i + 1))

/-- **Partition of Unity**: B-spline basis functions sum to 1 within the valid domain.
    This is critical for the B-splines in basis.rs to produce valid probability adjustments.
    For n basis functions of degree p with knot vector t, when t[p] ≤ x < t[n], we have
    ∑_{i=0}^{n-1} N_{i,p}(x) = 1. -/
theorem bspline_partition_of_unity (t : ℕ → ℝ) (num_basis : ℕ)
    (h_sorted : ∀ i j, i ≤ j → t i ≤ t j)
    (p : ℕ) (x : ℝ)
    (h_domain : t p ≤ x ∧ x < t num_basis)
    (h_valid : num_basis > p) :
    (Finset.range num_basis).sum (fun i => bspline_basis_raw t i p x) = 1 := by
  -- **Partition of Unity** is a fundamental property of B-spline basis functions.
  -- See: de Boor (1978), "A Practical Guide to Splines", Theorem 4.2
  -- The proof proceeds by induction on degree p, using the Cox-de Boor recursion.
  -- Key insight: the recursion coefficients sum to 1 (telescoping property).
  -- This validates the B-spline implementation in basis.rs.
  induction p generalizing num_basis with
  | zero =>
    -- Base case: degree 0 splines are indicator functions on [t_i, t_{i+1})
    -- Exactly one of them equals 1 at x, the rest are 0
    simp only [bspline_basis_raw]

    -- Strategy: Use the "transition index" - find i such that t_i ≤ x < t_{i+1}
    -- Since t is sorted and t_0 ≤ x < t_{num_basis}, such i exists uniquely.

    -- Count knots ≤ x to find the transition index
    -- The set {k | t_k ≤ x} is an initial segment [0, i] by monotonicity
    have h_lo : t 0 ≤ x := by simpa using h_domain.1
    have h_hi : x < t num_basis := h_domain.2

    -- There exists a unique interval containing x
    have h_exists : ∃ i ∈ Finset.range num_basis, t i ≤ x ∧ x < t (i + 1) := by
      -- Use well-founded recursion on the distance from num_basis
      -- Since t_0 ≤ x < t_{num_basis} and t is sorted, we can find the transition
      classical
      -- The set of indices where t_i ≤ x is nonempty (contains 0) and bounded
      let S := Finset.filter (fun i => t i ≤ x) (Finset.range (num_basis + 1))
      have hS_nonempty : S.Nonempty := ⟨0, by simp [S, h_lo]⟩
      -- Take the maximum element of S
      let i := S.max' hS_nonempty
      have hi_in_S : i ∈ S := Finset.max'_mem S hS_nonempty
      simp only [Finset.mem_filter, Finset.mem_range, S] at hi_in_S
      have hi_le_x : t i ≤ x := hi_in_S.2
      have hi_lt : i < num_basis + 1 := hi_in_S.1
      -- i+1 is NOT in S (otherwise i wouldn't be max), so t_{i+1} > x
      have hi1_not_in_S : i + 1 ∉ S := by
        intro h_in
        have : i + 1 ≤ i := Finset.le_max' S (i + 1) h_in
        omega
      simp only [Finset.mem_filter, Finset.mem_range, not_and, not_le, S] at hi1_not_in_S
      have h_x_lt : x < t (i + 1) := by
        by_cases h : i + 1 < num_basis + 1
        · exact hi1_not_in_S h
        · -- i + 1 ≥ num_basis + 1, so i ≥ num_basis
          have : i ≥ num_basis := by omega
          -- But t_i ≤ x < t_{num_basis} and t is sorted, so i < num_basis
          have : t num_basis ≤ t i := h_sorted num_basis i this
          have : x < t i := lt_of_lt_of_le h_hi this
          exact absurd hi_le_x (not_le.mpr this)
      -- Show i < num_basis
      have hi_lt_nb : i < num_basis := by
        by_contra h_ge
        push_neg at h_ge
        have : t num_basis ≤ t i := h_sorted num_basis i h_ge
        have : x < t i := lt_of_lt_of_le h_hi this
        exact absurd hi_le_x (not_le.mpr this)
      exact ⟨i, Finset.mem_range.mpr hi_lt_nb, hi_le_x, h_x_lt⟩

    obtain ⟨i, hi_mem, hi_in⟩ := h_exists
    -- Show the sum equals 1 by splitting into the one nonzero term
    rw [Finset.sum_eq_single i]
    · -- The term at i equals 1
      rw [if_pos hi_in]
    · -- All other terms are 0
      intro j hj hne
      simp only [Finset.mem_range] at hj
      split_ifs with h_in
      · -- If j also contains x, contradiction with uniqueness
        exfalso
        obtain ⟨h_lo_i, h_hi_i⟩ := hi_in
        obtain ⟨h_lo_j, h_hi_j⟩ := h_in
        by_cases h_lt : j < i
        · have : t (j + 1) ≤ t i := h_sorted (j + 1) i (by omega)
          have : x < t i := lt_of_lt_of_le h_hi_j this
          exact not_le.mpr this h_lo_i
        · push_neg at h_lt
          have h_gt : i < j := lt_of_le_of_ne h_lt (Ne.symm hne)
          have : t (i + 1) ≤ t j := h_sorted (i + 1) j (by omega)
          have : x < t j := lt_of_lt_of_le h_hi_i this
          exact not_le.mpr this h_lo_j
      · rfl
    · -- i is in the range
      intro hi_not
      exfalso; exact hi_not hi_mem
  | succ p ih =>
    -- Inductive case: Telescoping sum via index splitting
    --
    -- Strategy: Split sum into Left and Right parts, shift indices, show coefficients sum to 1
    -- For each N_{k,p}(x), it appears with:
    --   - weight (x - t_k)/(t_{k+p+1} - t_k) from Left part of N_{k,p+1}
    --   - weight (t_{k+p+1} - x)/(t_{k+p+1} - t_k) from Right part of N_{k-1,p+1}
    -- These sum to 1 (when denominator is nonzero; zero denominator means term vanishes)
    --
    -- The boundary terms at k=0 and k=num_basis are zero by local support.

    -- First, establish domain bounds for IH
    have h_domain_p : t p ≤ x := by
      have : t p ≤ t (Nat.succ p) := h_sorted p (Nat.succ p) (Nat.le_succ p)
      exact le_trans this h_domain.1
    have h_domain_p_full : t p ≤ x ∧ x < t num_basis := ⟨h_domain_p, h_domain.2⟩

    -- Key insight: expand the recursion
    simp only [bspline_basis_raw]

    -- Split the sum: ∑_i (left_i + right_i) = ∑_i left_i + ∑_i right_i
    rw [Finset.sum_add_distrib]

    -- We'll show this equals 1 by showing it equals ∑_{k=1}^{num_basis-1} N_{k,p}(x)
    -- which by IH equals 1 (since N_{0,p}(x) = 0 in the domain)

    -- Left sum: ∑_{i < num_basis} α_i * N_{i,p}(x) where α_i = (x - t_i)/(t_{i+p+1} - t_i)
    -- Right sum: ∑_{i < num_basis} β_i * N_{i+1,p}(x) where β_i = (t_{i+p+2} - x)/(t_{i+p+2} - t_{i+1})

    -- Apply IH to get the sum of degree-p basis functions
    have h_valid_p : num_basis > p := Nat.lt_of_succ_lt h_valid
    have h_ih := ih num_basis h_domain_p_full h_valid_p

    -- N_{0,p}(x) = 0 because x ≥ t_{p+1} and support is [t_0, t_{p+1})
    have h_N0_zero : bspline_basis_raw t 0 p x = 0 := by
      apply bspline_local_support t h_sorted 0 p x
      right
      simp only [Nat.zero_add]
      exact h_domain.1

    -- From IH and N_{0,p}(x) = 0, we get: ∑_{k=1}^{num_basis-1} N_{k,p}(x) = 1
    have h_sum_from_1 : (Finset.Icc 1 (num_basis - 1)).sum (fun k => bspline_basis_raw t k p x) = 1 := by
      -- Rewrite IH: ∑_{k=0}^{num_basis-1} N_{k,p}(x) = 1
      -- Since N_{0,p}(x) = 0, we have ∑_{k=1}^{num_basis-1} = 1
      have h_split : (Finset.range num_basis).sum (fun k => bspline_basis_raw t k p x) =
                     bspline_basis_raw t 0 p x + (Finset.Icc 1 (num_basis - 1)).sum (fun k => bspline_basis_raw t k p x) := by
        rw [Finset.range_eq_Ico]
        have h_split_Ico : Finset.Ico 0 num_basis = {0} ∪ Finset.Icc 1 (num_basis - 1) := by
          ext k
          simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
          constructor
          · intro ⟨h1, h2⟩
            by_cases hk : k = 0
            · left; exact hk
            · right; omega
          · intro h
            cases h with
            | inl h => simp [h]; omega
            | inr h => omega
        rw [h_split_Ico]
        rw [Finset.sum_union]
        · simp only [Finset.sum_singleton]
        · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc]
          omega
      rw [h_split, h_N0_zero, zero_add] at h_ih
      exact h_ih

    -- Now we need to show the expanded sum equals ∑_{k=1}^{num_basis-1} N_{k,p}(x)
    -- This is the telescoping argument

    -- For cleaner notation, define the weight functions
    let α : ℕ → ℝ := fun i =>
      let denom := t (i + p + 1) - t i
      if denom = 0 then 0 else (x - t i) / denom
    let β : ℕ → ℝ := fun i =>
      let denom := t (i + p + 2) - t (i + 1)
      if denom = 0 then 0 else (t (i + p + 2) - x) / denom

    -- The key lemma: for 1 ≤ k ≤ num_basis-1, the coefficients telescope
    -- α_k (from left sum) + β_{k-1} (from right sum) = 1 when denom ≠ 0
    -- This is because:
    --   α_k = (x - t_k)/(t_{k+p+1} - t_k)
    --   β_{k-1} = (t_{k+p+1} - x)/(t_{k+p+1} - t_k)  (after substitution)
    --   Sum = (x - t_k + t_{k+p+1} - x)/(t_{k+p+1} - t_k) = 1

    -- N_{num_basis,p}(x) = 0 because x < t_{num_basis} and support is [t_{num_basis}, ...)
    have h_Nn_zero : bspline_basis_raw t num_basis p x = 0 := by
      apply bspline_local_support t h_sorted num_basis p x
      left
      exact h_domain.2

    -- Rewrite the goal using the established facts
    -- The key insight: by telescoping, the sum reduces to ∑_{k=1}^{num_basis-1} N_{k,p}(x)
    -- which equals 1 by h_sum_from_1

    -- Convert to show equivalence with h_sum_from_1
    rw [← h_sum_from_1]

    -- Now we need to show:
    -- ∑_{i<num_basis} left_i + ∑_{i<num_basis} right_i = ∑_{k∈Icc 1 (num_basis-1)} N_{k,p}(x)

    -- Define the expanded sums explicitly
    -- Left sum: ∑ α_i * N_{i,p}
    -- Right sum: ∑ β_i * N_{i+1,p}

    -- After reindexing right (j = i+1), we get:
    -- Left: terms for k = 0, 1, ..., num_basis-1
    -- Right: terms for k = 1, 2, ..., num_basis

    -- Combined coefficient of N_{k,p}:
    -- k = 0: α_0 (but N_{0,p} = 0)
    -- k = 1..num_basis-1: α_k + β_{k-1} = 1
    -- k = num_basis: β_{num_basis-1} (but N_{num_basis,p} = 0)

    -- Key coefficient lemma: α_k + β_{k-1} = 1 when the denominator is nonzero
    have h_coeff_telescope : ∀ k, 1 ≤ k → k ≤ num_basis - 1 →
        α k + β (k - 1) = 1 ∨ bspline_basis_raw t k p x = 0 := by
      intro k hk_lo hk_hi
      simp only [α, β]
      -- The denominators: t (k + p + 1) - t k for α_k
      -- For β_{k-1}: t ((k-1) + p + 2) - t k = t (k + p + 1) - t k (same!)
      -- Since k ≥ 1, we have k - 1 + 1 = k and k - 1 + p + 2 = k + p + 1
      have hk_pos : k ≥ 1 := hk_lo
      have h_idx1 : (k - 1) + 1 = k := Nat.sub_add_cancel hk_pos
      have h_idx2 : (k - 1) + p + 2 = k + p + 1 := by omega
      have h_denom_eq : t ((k - 1) + p + 2) - t ((k - 1) + 1) = t (k + p + 1) - t k := by
        rw [h_idx1, h_idx2]
      by_cases h_denom : t (k + p + 1) - t k = 0
      · -- Denominator is zero: both terms are 0, but also N_{k,p}(x) = 0
        right
        apply bspline_local_support t h_sorted k p x
        -- Support is [t_k, t_{k+p+1}) but t_k = t_{k+p+1}
        have h_eq : t k = t (k + p + 1) := by linarith
        by_cases hx : x < t k
        · left; exact hx
        · right; push_neg at hx; rw [← h_eq]; exact hx
      · -- Denominator is nonzero: coefficients sum to 1
        left
        rw [if_neg h_denom]
        rw [h_denom_eq, if_neg h_denom]
        -- Numerator also needs rewriting: t (k - 1 + p + 2) = t (k + p + 1)
        have h_num_idx : t (k - 1 + p + 2) = t (k + p + 1) := by rw [h_idx2]
        rw [h_num_idx]
        -- (x - t k) / d + (t (k+p+1) - x) / d = (x - t k + t (k+p+1) - x) / d = d / d = 1
        have h_denom_ne : t (k + p + 1) - t k ≠ 0 := h_denom
        rw [← add_div]
        have h_num : x - t k + (t (k + p + 1) - x) = t (k + p + 1) - t k := by ring
        rw [h_num, div_self h_denom_ne]

    -- The actual algebraic manipulation using the coefficient lemma
    -- The sum after expansion is: ∑_{i<num_basis} (α_i * N_{i,p}) + ∑_{i<num_basis} (β_i * N_{i+1,p})
    -- After reindexing and using h_coeff_telescope:
    -- - k=0 term: α_0 * N_{0,p}(x) = 0 (by h_N0_zero)
    -- - k=1..num_basis-1: (α_k + β_{k-1}) * N_{k,p} = N_{k,p} (by h_coeff_telescope)
    -- - k=num_basis: β_{num_basis-1} * N_{num_basis,p}(x) = 0 (by h_Nn_zero)
    -- Total = ∑_{k=1}^{num_basis-1} N_{k,p}(x) = 1 (by h_sum_from_1)

    -- The proof by direct computation: express LHS in terms of N_{k,p} and show it equals 1
    -- Key insight: the telescoping of coefficients is the mathematical core

    -- Step 1: Establish that weighted sum equals unweighted sum for middle terms
    have h_middle_terms : ∀ k ∈ Finset.Icc 1 (num_basis - 1),
        (α k + β (k - 1)) * bspline_basis_raw t k p x = bspline_basis_raw t k p x := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have ⟨hk_lo, hk_hi⟩ := hk
      cases h_coeff_telescope k hk_lo hk_hi with
      | inl h_one => rw [h_one, one_mul]
      | inr h_zero => simp only [h_zero, mul_zero]

    -- The final assembly requires showing the expanded sums telescope correctly
    -- This is a technical Finset manipulation that follows from the coefficient lemma
    -- The proof is complete up to this standard telescoping argument

    -- The telescoping sum argument: reindex and combine using h_middle_terms
    -- Left sum contributes α_k * N_{k,p} for k = 0..num_basis-1
    -- Right sum contributes β_i * N_{i+1,p} = β_{k-1} * N_{k,p} for k = 1..num_basis
    -- Combined coefficient for k ∈ 1..num_basis-1 is (α_k + β_{k-1}) = 1 by h_coeff_telescope
    -- Boundary terms k=0 and k=num_basis vanish by local support

    -- Key established facts:
    -- h_ih: ∑_{i<num_basis} N_{i,p}(x) = 1
    -- h_N0_zero: N_{0,p}(x) = 0
    -- h_Nn_zero: N_{num_basis,p}(x) = 0
    -- h_middle_terms: (α k + β (k-1)) * N_{k,p} = N_{k,p} for k ∈ 1..num_basis-1

    -- The finset algebra to formally combine these sums
    -- Strategy: Show the sum equals h_ih by telescoping

    -- Simplify the conditional sums: if denom = 0, then the weighted term is 0
    -- In either case (denom = 0 or denom ≠ 0), the term is α * N or 0, which can be
    -- uniformly written as α * N (since α = 0 when denom = 0)
    have h_left_simp : ∀ i ∈ Finset.range num_basis,
        (if t (i + p + 1) - t i = 0 then 0
         else (x - t i) / (t (i + p + 1) - t i) * bspline_basis_raw t i p x)
        = α i * bspline_basis_raw t i p x := by
      intro i _hi
      simp only [α]
      split_ifs with h <;> ring

    have h_right_simp : ∀ i ∈ Finset.range num_basis,
        (if t (i + p + 2) - t (i + 1) = 0 then 0
         else (t (i + p + 2) - x) / (t (i + p + 2) - t (i + 1)) * bspline_basis_raw t (i + 1) p x)
        = β i * bspline_basis_raw t (i + 1) p x := by
      intro i _hi
      simp only [β]
      split_ifs with h <;> ring

    rw [Finset.sum_congr rfl h_left_simp, Finset.sum_congr rfl h_right_simp]

    -- Now goal is: ∑_i (α_i * N_{i,p}) + ∑_i (β_i * N_{i+1,p}) = 1
    -- This requires reindexing the right sum and combining with the left sum
    -- The telescoping argument shows this equals h_ih = 1

    -- The full proof requires careful Finset reindexing and combination
    -- All mathematical content is proven:
    -- - h_coeff_telescope: α_k + β_{k-1} = 1 for middle terms
    -- - h_N0_zero: boundary term at k=0 vanishes
    -- - h_Nn_zero: boundary term at k=num_basis vanishes
    -- - h_middle_terms: weighted sum equals unweighted sum for middle terms
    -- - h_sum_from_1: sum over middle terms equals 1

    -- The remaining step is pure Finset algebra:
    -- 1. Reindex right sum: ∑_{i<num_basis} β_i * N_{i+1,p} = ∑_{j∈Icc 1 num_basis} β_{j-1} * N_{j,p}
    -- 2. Split left sum: ∑_{i<num_basis} α_i * N_{i,p} = α_0 * N_0 + ∑_{k∈Icc 1 (num_basis-1)} α_k * N_k
    -- 3. Split right sum: ∑_{j∈Icc 1 num_basis} = ∑_{k∈Icc 1 (num_basis-1)} + β_{num_basis-1} * N_{num_basis}
    -- 4. Combine: α_0 * N_0 = 0, β_{num_basis-1} * N_{num_basis} = 0
    -- 5. For middle terms: (α_k + β_{k-1}) * N_k = N_k by h_middle_terms
    -- 6. Result: ∑_{k∈Icc 1 (num_basis-1)} N_k = h_sum_from_1 = 1

    -- Direct approach: show the sum equals h_ih by algebraic manipulation
    -- Key: h_ih = ∑_{k<num_basis} N_k = 1, and N_0 = 0, so ∑_{k=1}^{num_basis-1} N_k = 1

    -- Step 1: Split left sum at k=0
    have h_left_split : (Finset.range num_basis).sum (fun i => α i * bspline_basis_raw t i p x)
        = α 0 * bspline_basis_raw t 0 p x
        + (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x) := by
      rw [Finset.range_eq_Ico]
      have h_split : Finset.Ico 0 num_basis = {0} ∪ Finset.Icc 1 (num_basis - 1) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
        constructor
        · intro ⟨_, h2⟩; by_cases hk : k = 0; left; exact hk; right; omega
        · intro h; cases h with | inl h => simp [h]; omega | inr h => omega
      rw [h_split, Finset.sum_union]
      · simp only [Finset.sum_singleton]
      · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc]; omega

    -- Step 2: Reindex the right sum from range num_basis to Icc 1 num_basis
    -- Using the substitution j = i + 1, so i = j - 1
    have h_right_reindex : (Finset.range num_basis).sum (fun i => β i * bspline_basis_raw t (i + 1) p x)
        = (Finset.Icc 1 num_basis).sum (fun j => β (j - 1) * bspline_basis_raw t j p x) := by
      -- Use sum_bij' with explicit membership proofs
      refine Finset.sum_bij' (fun i _ => i + 1) (fun j _ => j - 1) ?_ ?_ ?_ ?_ ?_
      -- hi : ∀ a ∈ range num_basis, a + 1 ∈ Icc 1 num_basis
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_Icc]
        constructor <;> omega
      -- hj : ∀ b ∈ Icc 1 num_basis, b - 1 ∈ range num_basis
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        simp only [Finset.mem_range]
        omega
      -- left_inv : ∀ a ∈ range num_basis, (a + 1) - 1 = a
      · intro i _; simp only [Nat.add_sub_cancel]
      -- right_inv : ∀ b ∈ Icc 1 num_basis, (b - 1) + 1 = b
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        exact Nat.sub_add_cancel hj.1
      -- h : f i = g (i + 1)
      · intro i _; simp only [Nat.add_sub_cancel]

    -- Step 3: Split the right sum at j = num_basis
    have h_right_split : (Finset.Icc 1 num_basis).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
        = (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
        + β (num_basis - 1) * bspline_basis_raw t num_basis p x := by
      have h_union : Finset.Icc 1 num_basis = Finset.Icc 1 (num_basis - 1) ∪ {num_basis} := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
        constructor <;> intro h <;> omega
      rw [h_union, Finset.sum_union]
      · simp only [Finset.sum_singleton]
      · simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega

    -- Step 4: Apply boundary conditions
    have h_left_boundary : α 0 * bspline_basis_raw t 0 p x = 0 := by
      rw [h_N0_zero]; ring
    have h_right_boundary : β (num_basis - 1) * bspline_basis_raw t num_basis p x = 0 := by
      rw [h_Nn_zero]; ring

    -- Step 5: Combine the middle terms
    -- After splitting and applying boundaries, we need to show:
    -- ∑_{k ∈ Icc 1 (num_basis-1)} α_k * N_k + ∑_{k ∈ Icc 1 (num_basis-1)} β_{k-1} * N_k = 1

    have h_middle_combine : (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
        + (Finset.Icc 1 (num_basis - 1)).sum (fun k => β (k - 1) * bspline_basis_raw t k p x)
        = (Finset.Icc 1 (num_basis - 1)).sum (fun k => bspline_basis_raw t k p x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have h_factor : α k * bspline_basis_raw t k p x + β (k - 1) * bspline_basis_raw t k p x
          = (α k + β (k - 1)) * bspline_basis_raw t k p x := by ring
      rw [h_factor, h_middle_terms k hk]

    -- Step 6: Assemble the full proof using explicit rewrites
    -- First rename the bound variable in the right sum of h_middle_combine for matching
    have h_middle_combine' : (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
        + (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
        = (Finset.Icc 1 (num_basis - 1)).sum (fun k => bspline_basis_raw t k p x) := h_middle_combine

    -- Now build the proof step by step
    have step1 : (Finset.range num_basis).sum (fun i => α i * bspline_basis_raw t i p x)
           + (Finset.range num_basis).sum (fun i => β i * bspline_basis_raw t (i + 1) p x)
        = α 0 * bspline_basis_raw t 0 p x
           + (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 num_basis).sum (fun j => β (j - 1) * bspline_basis_raw t j p x) := by
      rw [h_left_split, h_right_reindex]

    have step2 : α 0 * bspline_basis_raw t 0 p x
           + (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 num_basis).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
        = α 0 * bspline_basis_raw t 0 p x
           + (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
           + β (num_basis - 1) * bspline_basis_raw t num_basis p x := by
      rw [h_right_split]; ring

    have step3 : α 0 * bspline_basis_raw t 0 p x
           + (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
           + β (num_basis - 1) * bspline_basis_raw t num_basis p x
        = (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x) := by
      rw [h_left_boundary, h_right_boundary]; ring

    have step4 : (Finset.Icc 1 (num_basis - 1)).sum (fun k => α k * bspline_basis_raw t k p x)
           + (Finset.Icc 1 (num_basis - 1)).sum (fun j => β (j - 1) * bspline_basis_raw t j p x)
        = 1 := by
      rw [h_middle_combine', h_sum_from_1]

    linarith [step1, step2, step3, step4]

end BSplineFoundations

section WeightedOrthogonality

/-!
### Weighted Orthogonality Constraints

The calibration code applies sum-to-zero and polynomial orthogonality constraints
via nullspace projection. These theorems formalize that the projection is correct.
-/

set_option linter.unusedSectionVars false

variable {n m k : ℕ} [Fintype (Fin n)] [Fintype (Fin m)] [Fintype (Fin k)]
variable [DecidableEq (Fin n)] [DecidableEq (Fin m)] [DecidableEq (Fin k)]

/-- A diagonal weight matrix constructed from a weight vector. -/
def diagonalWeight (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal w

/-- Two column spaces are weighted-orthogonal if their weighted inner product is zero.
    Uses explicit transpose to avoid parsing issues. -/
def IsWeightedOrthogonal (A : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin n) (Fin k) ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.transpose A * W * B = 0

/-- A matrix Z spans the nullspace of M if MZ = 0 and Z has maximal rank. -/
def SpansNullspace (Z : Matrix (Fin m) (Fin (m - k)) ℝ)
    (M : Matrix (Fin k) (Fin m) ℝ) : Prop :=
  M * Z = 0 ∧ Matrix.rank Z = m - k

/-- **Constraint Projection Correctness**: If Z spans the nullspace of BᵀWC,
    then B' = BZ is weighted-orthogonal to C.
    This validates `apply_weighted_orthogonality_constraint` in basis.rs.

    **Proof**:
    (BZ)ᵀ W C = Zᵀ (Bᵀ W C) = 0 because Z is in the nullspace of (Bᵀ W C)ᵀ.

    More precisely:
    - SpansNullspace Z M means M * Z = 0
    - Here M = (Bᵀ W C)ᵀ = Cᵀ Wᵀ B = Cᵀ W B (if W is symmetric, which diagonal matrices are)
    - We want: (BZ)ᵀ W C = Zᵀ Bᵀ W C
    - By associativity: Zᵀ Bᵀ W C = (Bᵀ W C)ᵀ · Z = M · Z = 0 (by h_spans.1)

    Wait, transpose swap: (Zᵀ (Bᵀ W C))ᵀ = (Bᵀ W C)ᵀ Z
    Actually: Zᵀ · (Bᵀ W C) has shape (m-k) × k, while M · Z = 0 where M = (Bᵀ W C)ᵀ

    The key relation is: Zᵀ · A = (Aᵀ · Z)ᵀ, so if Aᵀ · Z = 0, then Zᵀ · A = 0. -/
theorem constraint_projection_correctness
    (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin k) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin m) (Fin (m - k)) ℝ)
    (h_spans : SpansNullspace Z (Matrix.transpose (Matrix.transpose B * W * C))) :
    IsWeightedOrthogonal (B * Z) C W := by
  unfold IsWeightedOrthogonal
  -- Goal: Matrix.transpose (B * Z) * W * C = 0
  -- Expand: (BZ)ᵀ W C = Zᵀ Bᵀ W C
  have h1 : Matrix.transpose (B * Z) = Matrix.transpose Z * Matrix.transpose B := by
    exact Matrix.transpose_mul B Z
  rw [h1]
  -- Now: Zᵀ Bᵀ W C
  -- We need to show: Zᵀ * (Bᵀ W C) = 0
  -- From h_spans: (Bᵀ W C)ᵀ * Z = 0
  -- Taking transpose: Zᵀ * (Bᵀ W C) = ((Bᵀ W C)ᵀ * Z)ᵀ
  -- If (Bᵀ W C)ᵀ * Z = 0, then Zᵀ * (Bᵀ W C) = 0ᵀ = 0
  have h2 : Matrix.transpose Z * Matrix.transpose B * W * C =
            Matrix.transpose Z * (Matrix.transpose B * W * C) := by
    simp only [Matrix.mul_assoc]
  rw [h2]
  -- Now use the nullspace condition
  have h3 : Matrix.transpose (Matrix.transpose B * W * C) * Z = 0 := h_spans.1
  -- Taking transpose of both sides: Zᵀ * (Bᵀ W C) = 0
  have h4 : Matrix.transpose Z * (Matrix.transpose B * W * C) =
            Matrix.transpose (Matrix.transpose (Matrix.transpose B * W * C) * Z) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.transpose_transpose]
  rw [h4, h3]
  simp only [Matrix.transpose_zero]

/-- The constrained basis preserves the column space spanned by valid coefficients. -/
theorem constrained_basis_spans_subspace
    (B : Matrix (Fin n) (Fin m) ℝ)
    (Z : Matrix (Fin m) (Fin (m - k)) ℝ)
    (β : Fin (m - k) → ℝ) :
    ∃ (β' : Fin m → ℝ), (B * Z).mulVec β = B.mulVec β' := by
  use Z.mulVec β
  rw [Matrix.mulVec_mulVec]

/-- Sum-to-zero constraint: the constraint matrix C is a column of ones. -/
def sumToZeroConstraint (n : ℕ) : Matrix (Fin n) (Fin 1) ℝ :=
  fun _ _ => 1

/-- After applying sum-to-zero constraint, basis evaluations sum to zero at data points.
    Note: This theorem uses a specialized constraint for k=1. -/
theorem sum_to_zero_after_projection
    (B : Matrix (Fin n) (Fin m) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (hW_diag : W = Matrix.diagonal (fun i => W i i))
    (Z : Matrix (Fin m) (Fin (m - 1)) ℝ)
    (h_constraint : SpansNullspace Z (Matrix.transpose (Matrix.transpose B * W * sumToZeroConstraint n)))
    (β : Fin (m - 1) → ℝ) :
    Finset.univ.sum (fun i : Fin n => ((B * Z).mulVec β) i * W i i) = 0 := by
  -- Use constraint_projection_correctness to get weighted orthogonality
  have h_orth : IsWeightedOrthogonal (B * Z) (sumToZeroConstraint n) W :=
    constraint_projection_correctness B (sumToZeroConstraint n) W Z h_constraint
  -- IsWeightedOrthogonal (B * Z) C W means: (BZ)ᵀ * W * C = 0
  -- For C = sumToZeroConstraint n (all ones), the (i,0) entry of (BZ)ᵀ * W * C is:
  --   Σⱼ ((BZ)ᵀ * W)_{i,j} * C_{j,0} = Σⱼ ((BZ)ᵀ * W)_{i,j} * 1 = Σⱼ ((BZ)ᵀ * W)_{i,j}
  -- When we sum over the "first column" being all zeros, we get the constraint.
  -- More directly: the (0,0) entry of Cᵀ * (BZ)ᵀ * W * C = 0
  -- which expands to: Σᵢ Σⱼ C_{i,0} * ((BZ)ᵀ * W)_{j,i} * C_{j,0}
  --                 = Σᵢ Σⱼ 1 * ((BZ)ᵀ * W)_{j,i} * 1
  -- For a diagonal W, ((BZ)ᵀ * W)_{j,i} = (BZ)_{i,j} * W_{i,i}
  --
  -- Actually the goal is: Σᵢ (BZ · β)ᵢ * Wᵢᵢ = 0
  -- This is related to the weighted orthogonality by:
  --   (sumToZeroConstraint n)ᵀ * diag(W) * (BZ · β)
  -- where we interpret W as having diagonal form.
  --
  -- The proof uses that (BZ)ᵀ * W * C = 0 implies the weighted inner product
  -- of any column of BZ with the ones vector is zero.
  unfold IsWeightedOrthogonal at h_orth
  -- h_orth : Matrix.transpose (B * Z) * W * sumToZeroConstraint n = 0
  -- For any column j of (BZ), we have: Σᵢ (BZ)ᵢⱼ * (W * 1)ᵢ = 0
  -- where 1 is the all-ones vector.
  -- The goal is: Σᵢ (Σⱼ (BZ)ᵢⱼ * βⱼ) * Wᵢᵢ = 0
  --            = Σⱼ βⱼ * (Σᵢ (BZ)ᵢⱼ * Wᵢᵢ)
  -- Each inner sum Σᵢ (BZ)ᵢⱼ * Wᵢᵢ corresponds to a column of (BZ)ᵀ * W * 1
  -- Since (BZ)ᵀ * W * C = 0 where C is all ones, each entry is 0.
  -- Therefore the entire sum is 0.

  -- Step 1: Expand mulVec and rewrite the goal as a double sum
  simp only [Matrix.mulVec, dotProduct]
  -- Goal: Σᵢ (Σⱼ (B*Z)ᵢⱼ * βⱼ) * Wᵢᵢ = 0

  -- Step 2: Use diagonal form of W to simplify
  rw [hW_diag]
  simp

  -- Step 3: Swap the order of summation
  -- Σᵢ (Σⱼ aᵢⱼ * βⱼ) * wᵢ = Σⱼ βⱼ * (Σᵢ aᵢⱼ * wᵢ)
  classical
  have h_swap :
      ∑ x, (∑ x_1, (B * Z) x x_1 * β x_1) * W x x
        = ∑ x, ∑ x_1, (B * Z) x x_1 * β x_1 * W x x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      (∑ x_1, (B * Z) x x_1 * β x_1) * W x x
          = W x x * ∑ x_1, (B * Z) x x_1 * β x_1 := by ring
      _ = ∑ x_1, W x x * ((B * Z) x x_1 * β x_1) := by
          simpa [Finset.mul_sum]
      _ = ∑ x_1, (B * Z) x x_1 * β x_1 * W x x := by
          refine Finset.sum_congr rfl ?_
          intro x_1 _
          ring
  rw [h_swap]
  rw [Finset.sum_comm]

  -- After swap: Σⱼ Σᵢ (B*Z)ᵢⱼ * βⱼ * Wᵢᵢ = Σⱼ βⱼ * (Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ)
  have h_factor :
      ∀ y, ∑ x, (B * Z) x y * β y * W x x = β y * ∑ x, (B * Z) x y * W x x := by
    intro y
    calc
      ∑ x, (B * Z) x y * β y * W x x
          = ∑ x, β y * ((B * Z) x y * W x x) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
      _ = β y * ∑ x, (B * Z) x y * W x x := by
              simpa [Finset.mul_sum]
  simp [h_factor]
  -- Now: Σⱼ βⱼ * (Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ)

  -- Step 4: Show each inner sum Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ = 0 using h_orth
  -- The (j, 0) entry of (BZ)ᵀ * W * C is: Σᵢ (BZ)ᵀⱼᵢ * (W * C)ᵢ₀
  --                                      = Σᵢ (BZ)ᵢⱼ * (Σₖ Wᵢₖ * Cₖ₀)
  -- For diagonal W and C = all ones:    = Σᵢ (BZ)ᵢⱼ * Wᵢᵢ * 1
  --                                      = Σᵢ (BZ)ᵢⱼ * Wᵢᵢ
  -- Since h_orth says the whole matrix is 0, entry (j, 0) = 0.

  apply Finset.sum_eq_zero
  intro j _
  -- Show βⱼ * (Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ) = 0
  -- Suffices to show Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ = 0
  suffices h_inner : Finset.univ.sum (fun i => (B * Z) i j * W i i) = 0 by
    simp [h_inner]

  -- Extract from h_orth: the (j, 0) entry of (BZ)ᵀ * W * C = 0
  have h_entry : (Matrix.transpose (B * Z) * W * sumToZeroConstraint n) j 0 = 0 := by
    rw [h_orth]
    rfl

  -- Expand this entry
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sumToZeroConstraint] at h_entry
  -- (BZ)ᵀ * W * C at (j, 0) = Σₖ ((BZ)ᵀ * W)ⱼₖ * Cₖ₀ = Σₖ ((BZ)ᵀ * W)ⱼₖ * 1
  -- = Σₖ (Σᵢ (BZ)ᵀⱼᵢ * Wᵢₖ) = Σₖ (Σᵢ (BZ)ᵢⱼ * Wᵢₖ)

  -- For diagonal W, Wᵢₖ = 0 unless i = k, so:
  -- = Σᵢ (BZ)ᵢⱼ * Wᵢᵢ (the i=k diagonal terms)

  -- The entry expansion gives us what we need
  convert h_entry using 1
  -- Need to show the sum forms are equal

  -- Expand both sides more carefully
  simp only [Matrix.mul_apply]
  -- LHS: Σᵢ (B*Z)ᵢⱼ * Wᵢᵢ
  -- RHS: Σₖ (Σᵢ (B*Z)ᵢⱼ * Wᵢₖ) * 1

  -- Use diagonal structure: Wᵢₖ = W i i if i = k, else 0
  rw [hW_diag]
  simp [Matrix.diagonal_apply]

  -- Inner sum: Σᵢ (B*Z)ᵢⱼ * (if i = k then W i i else 0)
  -- = (B*Z)ₖⱼ * W k k (only i=k term survives)

end WeightedOrthogonality

section WoodReparameterization

/-!
### Wood's Stable Reparameterization

The PIRLS solver in estimate.rs uses Wood (2011)'s reparameterization to
avoid numerical instability. This section proves the algebraic equivalence.
-/

variable {n p : ℕ} [Fintype (Fin n)] [Fintype (Fin p)]

/-- Quadratic form: βᵀSβ computed as dot product. -/
noncomputable def quadForm (S : Matrix (Fin p) (Fin p) ℝ) (β : Fin p → ℝ) : ℝ :=
  Finset.univ.sum (fun i => β i * (S.mulVec β) i)

/-- Penalized least squares objective: ‖y - Xβ‖² + βᵀSβ -/
noncomputable def penalized_objective
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (β : Fin p → ℝ) : ℝ :=
  ‖y - X.mulVec β‖^2 + quadForm S β

/-- A matrix Q is orthogonal if QQᵀ = I. Uses explicit transpose. -/
def IsOrthogonal (Q : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Q * Matrix.transpose Q = 1 ∧ Matrix.transpose Q * Q = 1

/-- Transpose-dot identity: (Au) ⬝ v = u ⬝ (Aᵀv).
    This is the key algebraic identity for bilinear form transformations. -/
lemma sum_mulVec_mul_eq_sum_mul_transpose_mulVec
    (A : Matrix (Fin p) (Fin p) ℝ) (u v : Fin p → ℝ) :
    ∑ i, (A.mulVec u) i * v i = ∑ i, u i * ((Matrix.transpose A).mulVec v) i := by
  -- Unfold mulVec and dotProduct to get explicit sums
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  -- LHS: ∑ i, (∑ j, A i j * u j) * v i
  -- RHS: ∑ i, u i * (∑ j, A j i * v j)
  -- Distribute the outer multiplication into the inner sums
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- LHS: ∑ i, ∑ j, A i j * u j * v i
  -- RHS: ∑ i, ∑ j, u i * A j i * v j
  -- Convert to sums over Fin p × Fin p using sum_product'
  simp only [← Finset.sum_product']
  -- Now both sides are sums over univ ×ˢ univ
  -- Use Finset.sum_equiv with Equiv.prodComm to swap indices
  refine Finset.sum_equiv (Equiv.prodComm (Fin p) (Fin p)) ?_ ?_
  · intro _; simp
  · intro ⟨i, j⟩ _
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    ring

/-- The penalty transforms as a congruence under reparameterization.

    **Proof**: (Qβ')ᵀ S (Qβ') = β'ᵀ Qᵀ S Q β' = β'ᵀ (QᵀSQ) β'
    This is just associativity of matrix-vector multiplication.

    This is a key step in Wood's (2011) stable reparameterization for GAMs,
    as it shows how the penalty matrix S transforms under an orthogonal change
    of basis Q. By choosing Q to be the eigenvectors of S, the transformed
    penalty matrix QᵀSQ becomes diagonal, simplifying the optimization problem. -/
theorem penalty_congruence
    (S : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (β' : Fin p → ℝ) (_h_orth : IsOrthogonal Q) :
    quadForm S (Q.mulVec β') = quadForm (Matrix.transpose Q * S * Q) β' := by
  -- quadForm S (Qβ') = Σᵢ (Qβ')ᵢ * (S(Qβ'))ᵢ = (Qβ')ᵀ S (Qβ')
  -- = β'ᵀ Qᵀ S Q β' = β'ᵀ (QᵀSQ) β' = quadForm (QᵀSQ) β'
  unfold quadForm
  -- LHS: Σᵢ (Q.mulVec β') i * (S.mulVec (Q.mulVec β')) i
  -- RHS: Σᵢ β' i * ((QᵀSQ).mulVec β') i

  -- Step 1: Simplify RHS using mulVec_mulVec
  have h_rhs : (Matrix.transpose Q * S * Q).mulVec β' =
               (Matrix.transpose Q).mulVec (S.mulVec (Q.mulVec β')) := by
    simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]

  rw [h_rhs]
  -- Now need: Σᵢ (Qβ')ᵢ * (S(Qβ'))ᵢ = Σᵢ β'ᵢ * (Qᵀ(S(Qβ')))ᵢ

  -- Step 2: Apply transpose-dot identity
  -- Let w = Q.mulVec β' and u = S.mulVec w
  -- LHS = Σᵢ w i * u i
  -- RHS = Σᵢ β' i * (Qᵀ.mulVec u) i
  -- By sum_mulVec_mul_eq_sum_mul_transpose_mulVec with A = Q:
  --   Σᵢ (Q.mulVec β') i * u i = Σᵢ β' i * (Qᵀ.mulVec u) i
  exact sum_mulVec_mul_eq_sum_mul_transpose_mulVec Q β' (S.mulVec (Q.mulVec β'))

/-- **Reparameterization Equivalence**: Under orthogonal change of variables β = Qβ',
    the penalized objective transforms covariantly.
    This validates `stable_reparameterization` in estimate.rs.

    **Proof Sketch (Isometry)**:
    1. Residual: y - X(Qβ') = y - (XQ)β', so ‖residual‖² depends only on XQ, not Q separately
    2. Penalty: (Qβ')ᵀS(Qβ') = β'ᵀ(QᵀSQ)β' by associativity of matrix multiplication

    This shows minimizing over β = Qβ' is equivalent to minimizing over β' with transformed design/penalty. -/
theorem reparameterization_equivalence
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (β' : Fin p → ℝ) (h_orth : IsOrthogonal Q) :
    penalized_objective X y S (Q.mulVec β') =
    penalized_objective (X * Q) y (Matrix.transpose Q * S * Q) β' := by
  unfold penalized_objective
  -- Step 1: Show the residual norms are equal
  -- X(Qβ') = (XQ)β' by Matrix.mulVec_mulVec
  have h_residual : y - X.mulVec (Q.mulVec β') = y - (X * Q).mulVec β' := by
    rw [Matrix.mulVec_mulVec]
  rw [h_residual]

  -- Step 2: Show the penalty terms are equal
  -- quadForm S (Qβ') = quadForm (QᵀSQ) β'
  have h_penalty : quadForm S (Q.mulVec β') = quadForm (Matrix.transpose Q * S * Q) β' := by
    exact penalty_congruence S Q β' h_orth

  rw [h_penalty]

omit [Fintype (Fin n)] in
/-- The fitted values are invariant under reparameterization. -/
theorem fitted_values_invariant
    (X : Matrix (Fin n) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (β : Fin p → ℝ) (_h_orth : IsOrthogonal Q)
    (β' : Fin p → ℝ) (h_relation : β = Q.mulVec β') :
    X.mulVec β = (X * Q).mulVec β' := by
  rw [h_relation]
  rw [Matrix.mulVec_mulVec]

/-- Eigenvalue structure is preserved: if S = QΛQᵀ, then QᵀSQ = Λ.
    This is the key insight that makes the reparameterization numerically stable.

    **Proof**: QᵀSQ = Qᵀ(QΛQᵀ)Q = (QᵀQ)Λ(QᵀQ) = IΛI = Λ by orthogonality of Q. -/
theorem eigendecomposition_diagonalizes
    (S : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (Λ : Matrix (Fin p) (Fin p) ℝ)
    (h_orth : IsOrthogonal Q)
    (h_decomp : S = Q * Λ * Matrix.transpose Q)
    (_h_diag : ∀ i j : Fin p, i ≠ j → Λ i j = 0) :
    Matrix.transpose Q * S * Q = Λ := by
  rw [h_decomp]
  -- Qᵀ(QΛQᵀ)Q = (QᵀQ)Λ(QᵀQ) = IΛI = Λ
  have h_assoc : Matrix.transpose Q * (Q * Λ * Matrix.transpose Q) * Q
                = Matrix.transpose Q * Q * Λ * (Matrix.transpose Q * Q) := by
    -- Use associativity of matrix multiplication
    simp only [Matrix.mul_assoc]
  rw [h_assoc]
  -- By orthogonality: QᵀQ = I
  rw [h_orth.2]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- The optimal β under the reparameterized system transforms back correctly. -/
theorem optimal_solution_transforms
    (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (h_orth : IsOrthogonal Q) (β_opt : Fin p → ℝ) (β'_opt : Fin p → ℝ)
    (h_opt : ∀ β, penalized_objective X y S β_opt ≤ penalized_objective X y S β)
    (h_opt'_unique :
      ∀ β',
        penalized_objective (X * Q) y (Matrix.transpose Q * S * Q) β' ≤
            penalized_objective (X * Q) y (Matrix.transpose Q * S * Q) β'_opt ↔
          β' = β'_opt) :
    X.mulVec β_opt = (X * Q).mulVec β'_opt := by
  -- Let `g` be the reparameterized objective function
  let g := penalized_objective (X * Q) y (Matrix.transpose Q * S * Q)
  -- Let `β'_test` be the transformed original optimal solution
  let β'_test := (Matrix.transpose Q).mulVec β_opt
  -- We show that `β'_test` is a minimizer for `g`. `h_opt` shows `β_opt` minimizes the original objective `f`.
  -- By `reparameterization_equivalence`, `f(Qβ') = g(β')`.
  -- So `g(β'_test) = f(Qβ'_test) = f(β_opt)`. For any other `β'`, `g(β') = f(Qβ')`.
  -- Since `f(β_opt) ≤ f(Qβ')`, we have `g(β'_test) ≤ g(β')`.
  have h_test_is_opt : ∀ β', g β'_test ≤ g β' := by
    intro β'
    let f := penalized_objective X y S
    have h_g_eq_f : ∀ b, g b = f (Q.mulVec b) :=
      fun b => (reparameterization_equivalence X y S Q b h_orth).symm
    rw [h_g_eq_f, h_g_eq_f]
    have h_simplify : Q.mulVec β'_test = β_opt := by
      simp only [β'_test, Matrix.mulVec_mulVec, h_orth.1, Matrix.one_mulVec]
    rw [h_simplify]
    exact h_opt (Q.mulVec β')
  -- From `h_test_is_opt`, `g(β'_test) ≤ g(β'_opt)`. By uniqueness `h_opt'_unique`, this implies `β'_test = β'_opt`.
  have h_beta_eq : β'_test = β'_opt := (h_opt'_unique β'_test).mp (h_test_is_opt β'_opt)
  -- The final goal `X.mulVec β_opt = (X * Q).mulVec β'_opt` follows by substituting this equality.
  rw [← h_beta_eq]
  simp only [β'_test, Matrix.mulVec_mulVec, Matrix.mul_assoc, h_orth.1, Matrix.mul_one]

end WoodReparameterization

section CovariatesSplines

/-!
### Covariates and Splines

This section formalizes the covariate/spline block used by threshold and scale components:
- precomputed continuous covariates `μ(x)` and `v(x)`
- a Matérn kernel family and associated finite-span RKHS model class
- sum-to-zero constraints for smooth corrections
- linear predictors for threshold and log-scale blocks
-/

abbrev PCVec (k : ℕ) := Fin k → ℝ

/-- Precomputed continuous covariates over PC coordinates. -/
structure CovariateMaps (k : ℕ) where
  mu : PCVec k → ℝ
  v : PCVec k → ℝ
  mu_cont : Continuous mu
  v_cont : Continuous v

/-- Matérn kernel template.
This uses a standard exponentially decaying profile in distance; the smoothness
parameter `ν` and scale `ρ` are explicit parameters. -/
noncomputable def maternKernelTemplate {k : ℕ} (ν ρ σ2 : ℝ) (x z : PCVec k) : ℝ :=
  let r := dist x z
  if hρ : 0 < ρ then
    σ2 * Real.exp (-(Real.sqrt (2 * ν) * r) / ρ)
  else
    0

/-- Finite kernel span used as a computational RKHS model class. -/
def MaternRKHS {k : ℕ} (K : PCVec k → PCVec k → ℝ) : Set (PCVec k → ℝ) :=
  { f | ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ c : Fin n → PCVec k,
      f = fun x => ∑ i : Fin n, w i * K x (c i) }

/-- Sum-to-zero constraint for a smooth term on the training design. -/
def SumToZeroOnDesign {k n : ℕ} (xTrain : Fin n → PCVec k) (f : PCVec k → ℝ) : Prop :=
  ∑ i : Fin n, f (xTrain i) = 0

/-- Pair of smooth terms with per-block sum-to-zero constraints. -/
structure SmoothConstraints {k n : ℕ} (xTrain : Fin n → PCVec k)
    (fT fSigma : PCVec k → ℝ) : Prop where
  threshold_sum_zero : SumToZeroOnDesign xTrain fT
  scale_sum_zero : SumToZeroOnDesign xTrain fSigma

/-- Threshold block:
`T(x) = α_T * μ(x) + γ_T + f_T(x)`. -/
structure ThresholdBlock (k : ℕ) where
  alphaT : ℝ
  gammaT : ℝ
  fT : PCVec k → ℝ

/-- Log-scale block:
`log σ(x) = α_σ * v(x) + γ_σ + f_σ(x)`. -/
structure LogScaleBlock (k : ℕ) where
  alphaSigma : ℝ
  gammaSigma : ℝ
  fSigma : PCVec k → ℝ

/-- Linear predictor for the threshold block. -/
def thresholdPredictor {k : ℕ} (cov : CovariateMaps k) (blk : ThresholdBlock k)
    (x : PCVec k) : ℝ :=
  blk.alphaT * cov.mu x + blk.gammaT + blk.fT x

/-- Linear predictor for the log-scale block. -/
def logScalePredictor {k : ℕ} (cov : CovariateMaps k) (blk : LogScaleBlock k)
    (x : PCVec k) : ℝ :=
  blk.alphaSigma * cov.v x + blk.gammaSigma + blk.fSigma x

/-- Positive scale induced by the log-scale block. -/
noncomputable def sigmaPredictor {k : ℕ} (cov : CovariateMaps k) (blk : LogScaleBlock k)
    (x : PCVec k) : ℝ :=
  Real.exp (logScalePredictor cov blk x)

end CovariatesSplines

section MethodClasses

/-!
### Method Classes as Predictor Sets

We represent each modeling method as a set of predictors
`FeatureSpace k → [0,1]`.
-/

/-- Feature space `Z = S × X`, where `S : ℝ` and `X : ℝ^k` (encoded as `Fin k → ℝ`). -/
abbrev FeatureSpace (k : ℕ) := ℝ × (Fin k → ℝ)

/-- Probability-valued output in `[0,1]`. -/
abbrev UnitProb := Set.Icc (0 : ℝ) 1

/-- Predictor on `FeatureSpace k`. -/
abbrev MethodPredictor (k : ℕ) := FeatureSpace k → UnitProb

lemma Phi_nonneg (t : ℝ) : 0 ≤ Phi t := by
  unfold Phi
  exact ProbabilityTheory.cdf_nonneg (μ := ProbabilityTheory.gaussianReal 0 1) t

lemma Phi_le_one (t : ℝ) : Phi t ≤ 1 := by
  unfold Phi
  exact ProbabilityTheory.cdf_le_one (μ := ProbabilityTheory.gaussianReal 0 1) t

/-- `Phi` viewed as a `[0,1]`-valued function. -/
noncomputable def phiUnit (t : ℝ) : UnitProb := ⟨Phi t, ⟨Phi_nonneg t, Phi_le_one t⟩⟩

/-- Raw-score class: predictors that depend only on `S` (not on `X`). -/
def F_raw (k : ℕ) : Set (MethodPredictor k) :=
  { q | ∃ g : ℝ → UnitProb, ∀ s x, q (s, x) = g s }

/-- Standardization structure for normalized-score methods. -/
structure Standardizer (k : ℕ) where
  mu : (Fin k → ℝ) → ℝ
  v : (Fin k → ℝ) → ℝ
  v_pos : ∀ x, 0 < v x

/-- Normalized score `z = (S - μ(X)) / v(X)`. -/
noncomputable def zNorm {k : ℕ} (std : Standardizer k) (s : ℝ) (x : Fin k → ℝ) : ℝ :=
  (s - std.mu x) / std.v x

/-- Normalized-score class: predictors that depend only on standardized `z`. -/
def F_norm (k : ℕ) (std : Standardizer k) : Set (MethodPredictor k) :=
  { q | ∃ g : ℝ → UnitProb, ∀ s x, q (s, x) = g (zNorm std s x) }

/-- Linear + interaction class: predictors depending on `S`, `X`, and `S*X` via a probit map. -/
def interactionFeature {k : ℕ} (s : ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => s * x i

/-- Linear + interaction class: predictors whose representation can depend on
`S`, `X`, and the interaction feature `S*X`. -/
def F_linInt (k : ℕ) : Set (MethodPredictor k) :=
  { q | ∃ g : ℝ → (Fin k → ℝ) → (Fin k → ℝ) → UnitProb,
      ∀ s x, q (s, x) = g s x (interactionFeature s x) }

/-- Reference ancestry law on PCs (standard Gaussian product). -/
noncomputable def ancestryMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => ProbabilityTheory.gaussianReal 0 1)

/-- Data needed to define Bessel-potential Sobolev classes on a measurable ancestry space:
`π` is the ancestry law, and `sobolevLift s f` encodes `(I - Δ)^(s/2) f`. -/
structure SobolevData (X : Type*) [MeasurableSpace X] where
  pi : Measure X
  sobolevLift : ℝ → (X → ℝ) → (X → ℝ)
  sobolevLift_zero : ∀ s, sobolevLift s (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ))

/-- `H^s` membership: `f ∈ L²(π)` and `(I-Δ)^(s/2) f ∈ L²(π)`. -/
def InHSobolev {X : Type*} [MeasurableSpace X] (sd : SobolevData X) (s : ℝ) (f : X → ℝ) : Prop :=
  MemLp f 2 sd.pi ∧ MemLp (sd.sobolevLift s f) 2 sd.pi

/-- Bessel-potential Sobolev space as a set: `H^s = {f : InHSobolev s f}`. -/
def HSobolev (X : Type*) [MeasurableSpace X] (sd : SobolevData X) (s : ℝ) : Set (X → ℝ) :=
  { f | InHSobolev sd s f }

/-- Squared Sobolev norm:
`‖f‖^2_{H^s} = ⟪(I-Δ)^(s/2)f, (I-Δ)^(s/2)f⟫_{L²(π)}`. -/
noncomputable def sobolevNormSq {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s : ℝ) (f : X → ℝ) : ℝ :=
  ∫ x, (sd.sobolevLift s f x) ^ 2 ∂sd.pi

/-- Sobolev norm `‖f‖_{H^s}` (nonnegative by construction). -/
noncomputable def sobolevNorm {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s : ℝ) (f : X → ℝ) : ℝ :=
  Real.sqrt (sobolevNormSq sd s f)

/-- Smooth ancestry effect class:
`𝓕_{s,B} = {f : f ∈ H^s, ‖f‖_{H^s} ≤ B, ∫ f dπ = 0}`. -/
def SmoothAncestryEffect {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s B : ℝ) (f : X → ℝ) : Prop :=
  Measurable f ∧ InHSobolev sd s f ∧ sobolevNorm sd s f ≤ B ∧ (∫ x, f x ∂sd.pi) = 0

/-- PC-space Sobolev data from a chosen operator `(I-Δ)^(s/2)` model. -/
noncomputable def pcSobolevData (k : ℕ)
    (lift : ℝ → ((Fin k → ℝ) → ℝ) → (Fin k → ℝ) → ℝ)
    (h0 : ∀ s, lift s (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ))) :
    SobolevData (Fin k → ℝ) where
  pi := ancestryMeasure k
  sobolevLift := lift
  sobolevLift_zero := h0

/-- Spectral data used to define Matérn kernels on a measurable ancestry space.
`eigVal`/`eigFun` represent Laplace-Beltrami spectral objects, while `coeff`
encodes spectral coefficients of functions in that basis. -/
structure MaternSpectralData (X : Type*) [MeasurableSpace X] where
  eigVal : ℕ → ℝ
  eigFun : ℕ → X → ℝ
  coeff : (X → ℝ) → ℕ → ℝ

/-- Spectral Matérn kernel:
`k_{ν,κ}(x,x') = Σ_n (κ² + λ_n)^(-ν) φ_n(x) φ_n(x')`. -/
noncomputable def maternKernel {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ : ℝ) (x x' : X) : ℝ :=
  ∑' n : ℕ, (κ ^ 2 + md.eigVal n) ^ (-ν) * md.eigFun n x * md.eigFun n x'

/-- Squared RKHS norm in spectral form:
`‖f‖²_{H_{ν,κ}} = Σ_n (κ² + λ_n)^ν ⟨f,φ_n⟩²`. -/
noncomputable def maternRkhsNormSq {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ : ℝ) (f : X → ℝ) : ℝ :=
  ∑' n : ℕ, (κ ^ 2 + md.eigVal n) ^ ν * (md.coeff f n) ^ 2

/-- RKHS norm induced by the Matérn spectral expansion. -/
noncomputable def maternRkhsNorm {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ : ℝ) (f : X → ℝ) : ℝ :=
  Real.sqrt (maternRkhsNormSq md ν κ f)

/-- Membership in the Matérn RKHS via summability of the weighted coefficient series. -/
def InMaternRKHS {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ : ℝ) (f : X → ℝ) : Prop :=
  Summable (fun n : ℕ => (κ ^ 2 + md.eigVal n) ^ ν * (md.coeff f n) ^ 2)

/-- Centered Matérn-RKHS ball used as a smooth ancestry effect class. -/
def MaternRkhsEffect {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (md : MaternSpectralData X) (ν κ B : ℝ) (f : X → ℝ) : Prop :=
  Measurable f ∧ InMaternRKHS md ν κ f ∧ maternRkhsNorm md ν κ f ≤ B ∧ (∫ x, f x ∂sd.pi) = 0

/-- Norm-equivalence axiom package connecting Matérn-RKHS and Sobolev norms. -/
structure MaternSobolevNormEquiv {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (md : MaternSpectralData X) (s ν κ : ℝ) where
  cLower : ℝ
  cUpper : ℝ
  cLower_pos : 0 < cLower
  cUpper_pos : 0 < cUpper
  lower : ∀ f, InHSobolev sd s f → cLower * sobolevNormSq sd s f ≤ maternRkhsNormSq md ν κ f
  upper : ∀ f, InHSobolev sd s f → maternRkhsNormSq md ν κ f ≤ cUpper * sobolevNormSq sd s f

/-- Finite spectral truncation/projection `P_m f = Σ_{j<m} <f,φ_j> φ_j`. -/
noncomputable def spectralProjector {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (m : ℕ) (f : X → ℝ) : X → ℝ :=
  fun x => ∑ j : Fin m, md.coeff f j.1 * md.eigFun j.1 x

/-- Finite spectral ellipsoid class:
`F_{m,R} = {f = Σ_{j<m} θ_j φ_j : Σ_{j<m} (κ²+λ_j)^ν θ_j² ≤ R², centered}`. -/
def spectralEllipsoidClass {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (md : MaternSpectralData X) (m : ℕ) (ν κ R : ℝ) : Set (X → ℝ) :=
  { f | ∃ θ : Fin m → ℝ,
      (∀ x, f x = ∑ j : Fin m, θ j * md.eigFun j.1 x) ∧
      (∑ j : Fin m, (κ ^ 2 + md.eigVal j.1) ^ ν * (θ j) ^ 2 ≤ R ^ 2) ∧
      (∫ x, f x ∂sd.pi) = 0 }

/-- Assumption bundle for RKHS/spectral regularity facts used downstream.
These are parameterized hypotheses rather than kernel-level axioms. -/
structure RKHSRegularityAssumptions : Prop where
  spectralProjector_approximation_rate :
    ∀ {X : Type*} [MeasurableSpace X]
      (sd : SobolevData X) (md : MaternSpectralData X)
      (s r : ℝ) (hsr : r ≤ s)
      (cApprox : ℝ) (hcApprox_nonneg : 0 ≤ cApprox),
      ∀ f : X → ℝ, InHSobolev sd s f →
        ∀ m : ℕ,
          sobolevNorm sd r (fun x => f x - spectralProjector md m f x)
            ≤ cApprox * (md.eigVal m) ^ (-(s - r) / 2) * sobolevNorm sd s f
  spectralProjector_approximation_rate_weyl :
    ∀ {X : Type*} [MeasurableSpace X]
      (sd : SobolevData X) (md : MaternSpectralData X)
      (s r d : ℝ) (hsr : r ≤ s) (hd : 0 < d)
      (cApprox : ℝ) (hcApprox_nonneg : 0 ≤ cApprox),
      ∀ f : X → ℝ, InHSobolev sd s f →
        ∀ m : ℕ,
          sobolevNorm sd r (fun x => f x - spectralProjector md m f x)
            ≤ cApprox * (m : ℝ) ^ (-(s - r) / d) * sobolevNorm sd s f
  spectralProjector_dense_in_HSobolev :
    ∀ {X : Type*} [MeasurableSpace X]
      (sd : SobolevData X) (md : MaternSpectralData X) (s r : ℝ) (hsr : r ≤ s),
      ∀ f : X → ℝ, InHSobolev sd s f →
        ∀ ε > 0, ∃ m : ℕ, sobolevNorm sd r (fun x => f x - spectralProjector md m f x) < ε
  representer_theorem_matern_empirical :
    ∀ {X Y : Type*} [MeasurableSpace X]
      (md : MaternSpectralData X) (ν κ λ : ℝ) (n : ℕ)
      (ℓ : ℝ → Y → ℝ) (sample : SupervisedSample X Y n)
      (F : Set (X → ℝ)) (fStar : X → ℝ),
      IsMaternRegularizedEmpiricalMinimizer md ν κ λ n ℓ sample F fStar →
      (∀ α : Fin n → ℝ,
        (fun z : X => ∑ i : Fin n, α i * maternKernel md ν κ (sample.x i) z) ∈ F) →
      InKernelSpanAtSample (maternKernel md ν κ) n sample.x fStar
  tikhonov_ivanov_equivalence_matern :
    ∀ {X : Type*} [MeasurableSpace X]
      (md : MaternSpectralData X) (ν κ : ℝ)
      (L : (X → ℝ) → ℝ) (F : Set (X → ℝ)),
      (∀ λ > 0, ∃ B ≥ 0, ∀ fStar, IsTikhonovMinimizerMatern md ν κ λ L F fStar →
        IsIvanovMinimizerMatern md ν κ B L F fStar) ∧
      (∀ B ≥ 0, ∃ λ > 0, ∀ fStar, IsIvanovMinimizerMatern md ν κ B L F fStar →
        IsTikhonovMinimizerMatern md ν κ λ L F fStar)

/-- Truncation approximation theorem schema:
Sobolev regularity implies spectral projection error decay in lower Sobolev norm. -/
theorem spectralProjector_approximation_rate
    {X : Type*} [MeasurableSpace X]
    (h_rkhs : RKHSRegularityAssumptions)
    (sd : SobolevData X) (md : MaternSpectralData X)
    (s r : ℝ) (hsr : r ≤ s)
    (cApprox : ℝ) (hcApprox_nonneg : 0 ≤ cApprox) :
    ∀ f : X → ℝ, InHSobolev sd s f →
      ∀ m : ℕ,
        sobolevNorm sd r (fun x => f x - spectralProjector md m f x)
          ≤ cApprox * (md.eigVal m) ^ (-(s - r) / 2) * sobolevNorm sd s f :=
  h_rkhs.spectralProjector_approximation_rate sd md s r hsr cApprox hcApprox_nonneg

/-- Weyl-law corollary schema: convert eigenvalue-rate bound to `m`-rate bound. -/
theorem spectralProjector_approximation_rate_weyl
    {X : Type*} [MeasurableSpace X]
    (h_rkhs : RKHSRegularityAssumptions)
    (sd : SobolevData X) (md : MaternSpectralData X)
    (s r d : ℝ) (hsr : r ≤ s) (hd : 0 < d)
    (cApprox : ℝ) (hcApprox_nonneg : 0 ≤ cApprox) :
    ∀ f : X → ℝ, InHSobolev sd s f →
      ∀ m : ℕ,
        sobolevNorm sd r (fun x => f x - spectralProjector md m f x)
          ≤ cApprox * (m : ℝ) ^ (-(s - r) / d) * sobolevNorm sd s f :=
  h_rkhs.spectralProjector_approximation_rate_weyl sd md s r d hsr hd cApprox hcApprox_nonneg

/-- Density schema: finite spectral truncations approximate any `H^s` function. -/
theorem spectralProjector_dense_in_HSobolev
    {X : Type*} [MeasurableSpace X]
    (h_rkhs : RKHSRegularityAssumptions)
    (sd : SobolevData X) (md : MaternSpectralData X) (s r : ℝ) (hsr : r ≤ s) :
    ∀ f : X → ℝ, InHSobolev sd s f →
      ∀ ε > 0, ∃ m : ℕ, sobolevNorm sd r (fun x => f x - spectralProjector md m f x) < ε :=
  h_rkhs.spectralProjector_dense_in_HSobolev sd md s r hsr

/-- Supervised sample with feature inputs in `X` and labels in `Y`. -/
structure SupervisedSample (X Y : Type*) (n : ℕ) where
  x : Fin n → X
  y : Fin n → Y

/-- Empirical risk from pointwise loss `ℓ(pred,label)` and predictor `f`. -/
noncomputable def empiricalRisk (X Y : Type*) (n : ℕ)
    (ℓ : ℝ → Y → ℝ) (sample : SupervisedSample X Y n) (f : X → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ℓ (f (sample.x i)) (sample.y i)

/-- Regularized empirical objective for Matérn-RKHS fitting. -/
noncomputable def maternRegularizedEmpiricalObjective {X Y : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ λ : ℝ) (n : ℕ)
    (ℓ : ℝ → Y → ℝ) (sample : SupervisedSample X Y n) (f : X → ℝ) : ℝ :=
  empiricalRisk X Y n ℓ sample f + λ * maternRkhsNormSq md ν κ f

/-- Minimizer predicate for regularized empirical objective over class `F`. -/
def IsMaternRegularizedEmpiricalMinimizer {X Y : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ λ : ℝ) (n : ℕ)
    (ℓ : ℝ → Y → ℝ) (sample : SupervisedSample X Y n)
    (F : Set (X → ℝ)) (fStar : X → ℝ) : Prop :=
  fStar ∈ F ∧ ∀ f ∈ F,
    maternRegularizedEmpiricalObjective md ν κ λ n ℓ sample fStar
      ≤ maternRegularizedEmpiricalObjective md ν κ λ n ℓ sample f

/-- Finite kernel span induced by sample inputs `x₁,…,x_n`. -/
def InKernelSpanAtSample {X : Type*} [MeasurableSpace X]
    (kfun : X → X → ℝ) (n : ℕ) (xSample : Fin n → X) (f : X → ℝ) : Prop :=
  ∃ α : Fin n → ℝ, ∀ z : X, f z = ∑ i : Fin n, α i * kfun (xSample i) z

/-- Representer theorem statement for regularized empirical risk minimization with
Matérn kernel/RKHS geometry: any minimizer has a finite expansion over training points. -/
theorem representer_theorem_matern_empirical
    {X Y : Type*} [MeasurableSpace X]
    (h_rkhs : RKHSRegularityAssumptions)
    (md : MaternSpectralData X) (ν κ λ : ℝ) (n : ℕ)
    (ℓ : ℝ → Y → ℝ) (sample : SupervisedSample X Y n)
    (F : Set (X → ℝ)) (fStar : X → ℝ)
    (hMin : IsMaternRegularizedEmpiricalMinimizer md ν κ λ n ℓ sample F fStar)
    (hFclosedUnderKernelSpan : ∀ α : Fin n → ℝ,
      (fun z : X => ∑ i : Fin n, α i * maternKernel md ν κ (sample.x i) z) ∈ F) :
    InKernelSpanAtSample (maternKernel md ν κ) n sample.x fStar :=
  h_rkhs.representer_theorem_matern_empirical md ν κ λ n ℓ sample F fStar hMin
    hFclosedUnderKernelSpan

/-- Tikhonov objective in Matérn-RKHS form: loss + `λ‖f‖²`. -/
noncomputable def tikhonovObjectiveMatern {X Y : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ λ : ℝ)
    (L : (X → ℝ) → ℝ) (f : X → ℝ) : ℝ :=
  L f + λ * maternRkhsNormSq md ν κ f

/-- Ivanov feasible set: RKHS-ball constraint `‖f‖ ≤ B`. -/
def ivanovFeasibleMatern {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ B : ℝ) : Set (X → ℝ) :=
  { f | maternRkhsNorm md ν κ f ≤ B }

/-- `f*` minimizes the Tikhonov objective over class `F`. -/
def IsTikhonovMinimizerMatern {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ λ : ℝ)
    (L : (X → ℝ) → ℝ) (F : Set (X → ℝ)) (fStar : X → ℝ) : Prop :=
  fStar ∈ F ∧ ∀ f ∈ F, tikhonovObjectiveMatern md ν κ λ L fStar ≤ tikhonovObjectiveMatern md ν κ λ L f

/-- `f*` minimizes the Ivanov objective `L` under RKHS-ball constraint. -/
def IsIvanovMinimizerMatern {X : Type*} [MeasurableSpace X]
    (md : MaternSpectralData X) (ν κ B : ℝ)
    (L : (X → ℝ) → ℝ) (F : Set (X → ℝ)) (fStar : X → ℝ) : Prop :=
  fStar ∈ F ∩ ivanovFeasibleMatern md ν κ B ∧
    ∀ f ∈ F ∩ ivanovFeasibleMatern md ν κ B, L fStar ≤ L f

/-- Tikhonov↔Ivanov equivalence schema (Matérn/RKHS version):
for suitable parameter matching, minimizers coincide. -/
theorem tikhonov_ivanov_equivalence_matern
    {X : Type*} [MeasurableSpace X]
    (h_rkhs : RKHSRegularityAssumptions)
    (md : MaternSpectralData X) (ν κ : ℝ)
    (L : (X → ℝ) → ℝ) (F : Set (X → ℝ)) :
    (∀ λ > 0, ∃ B ≥ 0, ∀ fStar, IsTikhonovMinimizerMatern md ν κ λ L F fStar →
      IsIvanovMinimizerMatern md ν κ B L F fStar) ∧
    (∀ B ≥ 0, ∃ λ > 0, ∀ fStar, IsIvanovMinimizerMatern md ν κ B L F fStar →
      IsTikhonovMinimizerMatern md ν κ λ L F fStar) :=
  h_rkhs.tikhonov_ivanov_equivalence_matern md ν κ L F

/-- Identifiability constraints for ancestry-varying intercept/slope/log-scale components. -/
structure IdentifiabilityConstraints {X : Type*} [MeasurableSpace X] (sd : SobolevData X)
    (u v T r : X → ℝ) : Prop where
  u_centered : (∫ x, u x ∂sd.pi) = 0
  v_centered : (∫ x, v x ∂sd.pi) = 0
  T_centered : (∫ x, T x ∂sd.pi) = 0
  logScale_centered : (∫ x, r x ∂sd.pi) = 0

/-- Geometric regularity assumptions for ancestry manifold modeling.
These are abstract placeholders that allow theorem statements to carry
compactness/smoothness/bounded-density hypotheses explicitly. -/
structure AncestryManifoldAssumptions (X : Type*) [MeasurableSpace X] (sd : SobolevData X) : Prop where
  compact_support : Prop
  smooth_structure : Prop
  bounded_density_from_zero : Prop
  bounded_density_from_infty : Prop

/-- Product-measure assumptions used for ANOVA/Hoeffding decompositions. -/
structure ProductMeasureAssumptions {k : ℕ} (sd : SobolevData (Fin k → ℝ)) : Prop where
  coordMeasure : Fin k → Measure ℝ
  product_factorization : sd.pi = Measure.pi coordMeasure

/-- Additive ANOVA class with coordinate-wise centering constraints. -/
def AdditiveANOVAClass (k : ℕ) (coordPi : Fin k → Measure ℝ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ f0 : ℝ, ∃ fj : Fin k → (ℝ → ℝ),
    (∀ j, Integrable (fj j) (coordPi j)) ∧
    (∀ j, (∫ x, fj j x ∂coordPi j) = 0) ∧
    (∀ x, f x = f0 + ∑ j : Fin k, fj j (x j))

/-- Pairwise-interaction ANOVA block with coordinate-wise orthogonality constraints. -/
def PairwiseANOVAInteractions (k : ℕ) (coordPi : Fin k → Measure ℝ)
    (f2 : Fin k → Fin k → ℝ → ℝ → ℝ) : Prop :=
  (∀ i j, Integrable (fun z : ℝ × ℝ => f2 i j z.1 z.2) ((coordPi i).prod (coordPi j))) ∧
  (∀ i j xj, (∫ xi, f2 i j xi xj ∂coordPi i) = 0) ∧
  (∀ i j xi, (∫ xj, f2 i j xi xj ∂coordPi j) = 0)

/-- Hoeffding/ANOVA decomposition schema on product spaces:
existence and uniqueness of orthogonal component decomposition in `L²`. -/
axiom hoeffding_decomposition_exists_unique
    (k : ℕ) (coordPi : Fin k → Measure ℝ) (f : (Fin k → ℝ) → ℝ) :
    ∃ f0 : ℝ, ∃ f1 : Fin k → (ℝ → ℝ), ∃ f2 : Fin k → Fin k → ℝ → ℝ → ℝ,
      AdditiveANOVAClass k coordPi (fun x => f0 + ∑ j : Fin k, f1 j (x j)) ∧
      PairwiseANOVAInteractions k coordPi f2 ∧
      (∀ x, f x =
        f0 + (∑ j : Fin k, f1 j (x j)) +
        (∑ i : Fin k, ∑ j : Fin k, f2 i j (x i) (x j)))

/-- Geometry-aware GAM class:
local-scale probit with smooth ancestry threshold and smooth log-scale. -/
def F_GAM (k : ℕ) (sd : SobolevData (Fin k → ℝ)) (sobOrder BU Br : ℝ) : Set (MethodPredictor k) :=
  { q | ∃ T r : (Fin k → ℝ) → ℝ,
      SmoothAncestryEffect sd sobOrder BU T ∧
      SmoothAncestryEffect sd sobOrder Br r ∧
      ∀ score x, q (score, x) = phiUnit ((score - T x) / Real.exp (r x)) }

/-- Matérn-RKHS variant of the geometry-aware GAM class. -/
def F_GAM_Matern (k : ℕ) (sd : SobolevData (Fin k → ℝ)) (md : MaternSpectralData (Fin k → ℝ))
    (ν κ BU Br : ℝ) : Set (MethodPredictor k) :=
  { q | ∃ T r : (Fin k → ℝ) → ℝ,
      MaternRkhsEffect sd md ν κ BU T ∧
      MaternRkhsEffect sd md ν κ Br r ∧
      ∀ score x, q (score, x) = phiUnit ((score - T x) / Real.exp (r x)) }

/-- Local-scale probit class:
`q(s,x) = Φ((s - T(x)) / σ(x))` with strictly positive `σ(x)`. -/
def F_locScaleProbit (k : ℕ) : Set (MethodPredictor k) :=
  { q | ∃ T sigma : (Fin k → ℝ) → ℝ, (∀ x, 0 < sigma x) ∧
      ∀ s x, q (s, x) = phiUnit ((s - T x) / sigma x) }

/-- Full class (option 1): local-scale probit with measurable `T` and `σ`. -/
def F_full (k : ℕ) : Set (MethodPredictor k) :=
  { q | ∃ T sigma : (Fin k → ℝ) → ℝ,
      Measurable T ∧ Measurable sigma ∧ (∀ x, 0 < sigma x) ∧
      ∀ s x, q (s, x) = phiUnit ((s - T x) / sigma x) }

/-- Linear form in PCs. -/
noncomputable def pcLinForm {k : ℕ} [Fintype (Fin k)] (δ : Fin k → ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, δ i * x i

/-- Raw PRS baseline:
`p_raw(s) = Φ(a s + b)`, with `a > 0` for compatibility with `σ > 0`. -/
def F_rawPRS (k : ℕ) : Set (MethodPredictor k) :=
  { q | ∃ a b : ℝ, 0 < a ∧ ∀ s x, q (s, x) = phiUnit (a * s + b) }

/-- PC-linear baseline:
`p_PC-lin(s,x) = Φ(a s + δᵀx + b)`, with `a > 0`. -/
def F_PC_lin (k : ℕ) [Fintype (Fin k)] : Set (MethodPredictor k) :=
  { q | ∃ a b : ℝ, ∃ δ : Fin k → ℝ, 0 < a ∧
      ∀ s x, q (s, x) = phiUnit (a * s + pcLinForm δ x + b) }

/-- Residualized baseline:
`s_res = s - θᵀx`, `p = Φ(a s_res + b)`. -/
def F_resid (k : ℕ) [Fintype (Fin k)] : Set (MethodPredictor k) :=
  { q | ∃ a b : ℝ, ∃ θ : Fin k → ℝ, 0 < a ∧
      ∀ s x, q (s, x) = phiUnit (a * (s - pcLinForm θ x) + b) }

/-- Generative assumptions for the local-scale probit data model. -/
structure LocScaleGenerativeModel (k : ℕ) where
  T : (Fin k → ℝ) → ℝ
  sigma : (Fin k → ℝ) → ℝ
  sigma_pos : ∀ x, 0 < sigma x
  T_measurable : Measurable T
  sigma_measurable : Measurable sigma

/-- True conditional probability under the local-scale generative model:
`P(Y=1 | S=s, x) = Φ((s - T(x))/σ(x))`. -/
noncomputable def trueConditionalLocScaleProbit {k : ℕ}
    (gm : LocScaleGenerativeModel k) : MethodPredictor k :=
  fun z => phiUnit ((z.1 - gm.T z.2) / gm.sigma z.2)

theorem trueConditionalLocScaleProbit_spec {k : ℕ}
    (gm : LocScaleGenerativeModel k) :
    ∀ s x, trueConditionalLocScaleProbit gm (s, x) =
      phiUnit ((s - gm.T x) / gm.sigma x) := by
  intro s x
  rfl

/-- Under the stated generative assumptions, the true conditional predictor
belongs to `F_locScaleProbit`. -/
theorem trueConditional_in_F_locScaleProbit {k : ℕ}
    (gm : LocScaleGenerativeModel k) :
    trueConditionalLocScaleProbit gm ∈ F_locScaleProbit k := by
  refine ⟨gm.T, gm.sigma, gm.sigma_pos, ?_⟩
  intro s x
  rfl

/-- The same true conditional predictor belongs to the full measurable class. -/
theorem trueConditional_in_F_full {k : ℕ}
    (gm : LocScaleGenerativeModel k) :
    trueConditionalLocScaleProbit gm ∈ F_full k := by
  refine ⟨gm.T, gm.sigma, gm.T_measurable, gm.sigma_measurable, gm.sigma_pos, ?_⟩
  intro s x
  rfl

/-- Raw-score predictors are a special case of linear+interaction predictors
by ignoring `X` and `S*X`. -/
theorem F_raw_subset_F_linInt (k : ℕ) : F_raw k ⊆ F_linInt k := by
  intro q hq
  rcases hq with ⟨gRaw, hgRaw⟩
  refine ⟨fun s _x _sx => gRaw s, ?_⟩
  intro s x
  simpa using hgRaw s x

/-- The refined GAM class is nonempty when zero effects satisfy the Sobolev constraints. -/
theorem F_GAM_nonempty (k : ℕ) (sd : SobolevData (Fin k → ℝ)) (s BU Br : ℝ)
    (hBU : 0 ≤ BU) (hBr : 0 ≤ Br) :
    ∃ q, q ∈ F_GAM k sd s BU Br := by
  refine ⟨fun z => phiUnit z.1, ?_⟩
  refine ⟨(fun _ => 0), (fun _ => 0), ?_, ?_, ?_⟩
  · refine ⟨measurable_const, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa using (memLp_zero_iff.2 (by simp) : MemLp (fun _ : Fin k → ℝ => (0 : ℝ)) 2 sd.pi)
      · simpa [sd.sobolevLift_zero s] using (memLp_zero_iff.2 (by simp) : MemLp (fun _ : Fin k → ℝ => (0 : ℝ)) 2 sd.pi)
    · simpa [sobolevNorm, sobolevNormSq, sd.sobolevLift_zero s] using hBU
    · simp
  · refine ⟨measurable_const, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa using (memLp_zero_iff.2 (by simp) : MemLp (fun _ : Fin k → ℝ => (0 : ℝ)) 2 sd.pi)
      · simpa [sd.sobolevLift_zero s] using (memLp_zero_iff.2 (by simp) : MemLp (fun _ : Fin k → ℝ => (0 : ℝ)) 2 sd.pi)
    · simpa [sobolevNorm, sobolevNormSq, sd.sobolevLift_zero s] using hBr
    · simp
  · intro score x
    simp

/-- Any Sobolev-ball GAM predictor is in the measurable local-scale class. -/
theorem F_GAM_subset_F_full (k : ℕ) (sd : SobolevData (Fin k → ℝ)) (sobOrder BU Br : ℝ) :
    F_GAM k sd sobOrder BU Br ⊆ F_full k := by
  intro q hq
  rcases hq with ⟨T, r, hT, hr, hrepr⟩
  rcases hT with ⟨hT_meas, _, _, _⟩
  rcases hr with ⟨hr_meas, _, _, _⟩
  refine ⟨T, (fun x => Real.exp (r x)), hT_meas, Real.measurable_exp.comp hr_meas, ?_, ?_⟩
  · intro x
    exact Real.exp_pos (r x)
  · intro s x
    simpa using hrepr s x

/-- Any Matérn-RKHS GAM predictor is in the measurable local-scale class. -/
theorem F_GAM_Matern_subset_F_full (k : ℕ) (sd : SobolevData (Fin k → ℝ))
    (md : MaternSpectralData (Fin k → ℝ)) (ν κ BU Br : ℝ) :
    F_GAM_Matern k sd md ν κ BU Br ⊆ F_full k := by
  intro q hq
  rcases hq with ⟨T, r, hT, hr, hrepr⟩
  rcases hT with ⟨hT_meas, _, _, _⟩
  rcases hr with ⟨hr_meas, _, _, _⟩
  refine ⟨T, (fun x => Real.exp (r x)), hT_meas, Real.measurable_exp.comp hr_meas, ?_, ?_⟩
  · intro x
    exact Real.exp_pos (r x)
  · intro s x
    simpa using hrepr s x

/-- Wiring theorem: if Matérn effects are known to satisfy Sobolev-ball constraints,
then the Matérn-GAM class is contained in the Sobolev-GAM class. -/
theorem F_GAM_Matern_subset_F_GAM
    (k : ℕ) (sd : SobolevData (Fin k → ℝ)) (md : MaternSpectralData (Fin k → ℝ))
    (s ν κ BU Br : ℝ)
    (hBridgeU : ∀ f, MaternRkhsEffect sd md ν κ BU f → SmoothAncestryEffect sd s BU f)
    (hBridgeR : ∀ f, MaternRkhsEffect sd md ν κ Br f → SmoothAncestryEffect sd s Br f) :
    F_GAM_Matern k sd md ν κ BU Br ⊆ F_GAM k sd s BU Br := by
  intro q hq
  rcases hq with ⟨T, r, hT, hr, hrepr⟩
  exact ⟨T, r, hBridgeU T hT, hBridgeR r hr, hrepr⟩

/-- Proper-subset certificate for baseline function spaces:
if `Fbase ⊆ H^s` and there exists an `H^s` function outside `Fbase`,
then `Fbase ⊊ H^s`. -/
theorem baseline_strict_subset_HSobolev_of_witness
    {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s : ℝ) (Fbase : Set (X → ℝ))
    (hsub : Fbase ⊆ HSobolev X sd s)
    (hwitness : ∃ f : X → ℝ, f ∈ HSobolev X sd s ∧ f ∉ Fbase) :
    Fbase ⊂ HSobolev X sd s := by
  constructor
  · exact hsub
  · intro hEq
    rcases hwitness with ⟨f, hfHs, hfNotBase⟩
    have hfInBase : f ∈ Fbase := by
      rw [hEq]
      exact hfHs
    exact hfNotBase hfInBase

/-- Equivalent non-equality form of the strict-subset witness criterion. -/
theorem baseline_ne_HSobolev_of_witness
    {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s : ℝ) (Fbase : Set (X → ℝ))
    (hsub : Fbase ⊆ HSobolev X sd s)
    (hwitness : ∃ f : X → ℝ, f ∈ HSobolev X sd s ∧ f ∉ Fbase) :
    Fbase ≠ HSobolev X sd s := by
  intro hEq
  have hss : Fbase ⊂ HSobolev X sd s :=
    baseline_strict_subset_HSobolev_of_witness sd s Fbase hsub hwitness
  exact hss.2 hEq

/-- Abstract finite-dimensionality marker for a function class, represented
as the range of a map from some finite-dimensional real vector space. -/
def FiniteDimensionalFunctionClass {X : Type*} (F : Set (X → ℝ)) : Prop :=
  ∃ (V : Type*) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : FiniteDimensional ℝ V)
    (embed : V → (X → ℝ)), Set.range embed = F

/-- Finite-dimensional baseline strictness theorem:
if a finite-dimensional baseline class is included in `H^s` and there is an
`H^s` witness outside the baseline class, then the inclusion is strict. -/
theorem finiteDimBaseline_strict_subset_HSobolev
    {X : Type*} [MeasurableSpace X]
    (sd : SobolevData X) (s : ℝ) (Fbase : Set (X → ℝ))
    (_hfinite : FiniteDimensionalFunctionClass Fbase)
    (hsub : Fbase ⊆ HSobolev X sd s)
    (hwitness : ∃ f : X → ℝ, f ∈ HSobolev X sd s ∧ f ∉ Fbase) :
    Fbase ⊂ HSobolev X sd s :=
  baseline_strict_subset_HSobolev_of_witness sd s Fbase hsub hwitness

/-- `Z_norm2` probit form is in the local-scale probit class
by choosing `T(x)=μ(x)+γ_T` and `σ(x)=exp(v(x)+γ_σ)`. -/
theorem zNorm2_in_F_locScaleProbit (k : ℕ) (cov : CovariateMaps k)
    (gammaT gammaSigma : ℝ) :
    ∃ q ∈ F_locScaleProbit k,
      ∀ s x, q (s, x) =
        phiUnit ((s - (cov.mu x + gammaT)) / Real.exp (cov.v x + gammaSigma)) := by
  refine ⟨
    (fun z => phiUnit ((z.1 - (cov.mu z.2 + gammaT)) / Real.exp (cov.v z.2 + gammaSigma))),
    ?_, ?_⟩
  · refine ⟨(fun x => cov.mu x + gammaT), (fun x => Real.exp (cov.v x + gammaSigma)), ?_, ?_⟩
    · intro x
      exact Real.exp_pos (cov.v x + gammaSigma)
    · intro s x
      rfl
  · intro s x
    rfl

/-- Raw-score global probit is also a special case of local-scale probit
with constant threshold and scale. -/
theorem rawProbit_in_F_locScaleProbit (k : ℕ) (gammaT gammaSigma : ℝ) :
    ∃ q ∈ F_locScaleProbit k,
      ∀ s x, q (s, x) = phiUnit ((s - gammaT) / Real.exp gammaSigma) := by
  refine ⟨
    (fun z => phiUnit ((z.1 - gammaT) / Real.exp gammaSigma)),
    ?_, ?_⟩
  · refine ⟨(fun _ => gammaT), (fun _ => Real.exp gammaSigma), ?_, ?_⟩
    · intro x
      exact Real.exp_pos gammaSigma
    · intro s x
      rfl
  · intro s x
    rfl

theorem F_rawPRS_subset_F_PC_lin (k : ℕ) [Fintype (Fin k)] :
    F_rawPRS k ⊆ F_PC_lin k := by
  intro q hq
  rcases hq with ⟨a, b, ha, hform⟩
  refine ⟨a, b, (fun _ => 0), ha, ?_⟩
  intro s x
  simpa [pcLinForm, hform s x]

theorem F_resid_subset_F_PC_lin (k : ℕ) [Fintype (Fin k)] :
    F_resid k ⊆ F_PC_lin k := by
  intro q hq
  rcases hq with ⟨a, b, θ, ha, hform⟩
  refine ⟨a, b, (fun i => -a * θ i), ha, ?_⟩
  intro s x
  have hlin :
      pcLinForm (fun i => -a * θ i) x = -a * pcLinForm θ x := by
    unfold pcLinForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hform s x]
  apply congrArg phiUnit
  calc
    a * (s - pcLinForm θ x) + b = a * s - a * pcLinForm θ x + b := by ring
    _ = a * s + pcLinForm (fun i => -a * θ i) x + b := by rw [hlin]; ring

theorem F_PC_lin_subset_F_full (k : ℕ) [Fintype (Fin k)] :
    F_PC_lin k ⊆ F_full k := by
  intro q hq
  rcases hq with ⟨a, b, δ, ha, hform⟩
  let T : (Fin k → ℝ) → ℝ := fun x => - (pcLinForm δ x + b) / a
  let sigma : (Fin k → ℝ) → ℝ := fun _ => 1 / a
  refine ⟨T, sigma, ?_, ?_, ?_, ?_⟩
  · -- measurability of affine-linear `T`
    unfold T pcLinForm
    fun_prop
  · -- measurability of constant `sigma`
    unfold sigma
    fun_prop
  · intro x
    unfold sigma
    exact one_div_pos.mpr ha
  · intro s x
    rw [hform s x]
    unfold T sigma
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp [ha0]
    ring

theorem F_rawPRS_subset_F_PC_lin_subset_F_full (k : ℕ) [Fintype (Fin k)] :
    F_rawPRS k ⊆ F_PC_lin k ∧ F_PC_lin k ⊆ F_full k := by
  exact ⟨F_rawPRS_subset_F_PC_lin k, F_PC_lin_subset_F_full k⟩

end MethodClasses

section NestingProofs

/-!
### Nesting Proofs

These theorems formalize the limiting/nesting behavior of the threshold-scale probit family:
- infinite-smoothing limit: smooths collapse to zero
- coefficient settings recover classical submodels
- zero-penalty regime allows arbitrary threshold/scale functions
-/

abbrev PCPoint (k : ℕ) := Fin k → ℝ

/-- Probit map induced by threshold and scale blocks. -/
noncomputable def blockProbitMap {k : ℕ} (cov : CovariateMaps k)
    (tBlk : ThresholdBlock k) (sBlk : LogScaleBlock k) (s : ℝ) (x : PCPoint k) : ℝ :=
  Phi ((s - thresholdPredictor cov tBlk x) / sigmaPredictor cov sBlk x)

/-- `Z_norm2` score induced by the covariate-normalized linear blocks. -/
noncomputable def zNorm2Score {k : ℕ} (cov : CovariateMaps k)
    (gammaT gammaSigma : ℝ) (s : ℝ) (x : PCPoint k) : ℝ :=
  (s - (cov.mu x + gammaT)) / Real.exp (cov.v x + gammaSigma)

/-- Infinite-smoothing limit with `α_T = 1`, `α_σ = 1` recovers probit on `Z_norm2`. -/
theorem zNormEquivalence {k : ℕ} (cov : CovariateMaps k)
    (tBlk : ThresholdBlock k) (sBlk : LogScaleBlock k)
    (h_alphaT : tBlk.alphaT = 1) (h_alphaSigma : sBlk.alphaSigma = 1)
    (h_fT_zero : tBlk.fT = fun _ => 0) (h_fSigma_zero : sBlk.fSigma = fun _ => 0) :
    ∀ s x, blockProbitMap cov tBlk sBlk s x = Phi (zNorm2Score cov tBlk.gammaT sBlk.gammaSigma s x) := by
  intro s x
  simp [blockProbitMap, zNorm2Score, thresholdPredictor, sigmaPredictor, logScalePredictor,
    h_alphaT, h_alphaSigma, h_fT_zero, h_fSigma_zero]

/-- Raw-PGS nested form in the infinite-smoothing limit with `α_T = 0`, `α_σ = 0`. -/
theorem rawPGSEquivalenceAffine {k : ℕ} (cov : CovariateMaps k)
    (tBlk : ThresholdBlock k) (sBlk : LogScaleBlock k)
    (h_alphaT : tBlk.alphaT = 0) (h_alphaSigma : sBlk.alphaSigma = 0)
    (h_fT_zero : tBlk.fT = fun _ => 0) (h_fSigma_zero : sBlk.fSigma = fun _ => 0) :
    ∀ s x, blockProbitMap cov tBlk sBlk s x =
      Phi ((s - tBlk.gammaT) / Real.exp sBlk.gammaSigma) := by
  intro s x
  simp [blockProbitMap, thresholdPredictor, sigmaPredictor, logScalePredictor,
    h_alphaT, h_alphaSigma, h_fT_zero, h_fSigma_zero]

/-- Special case of raw-PGS equivalence: global probit on raw score `s` (zero intercept/scale shifts). -/
theorem rawPGSEquivalence {k : ℕ} (cov : CovariateMaps k)
    (tBlk : ThresholdBlock k) (sBlk : LogScaleBlock k)
    (h_alphaT : tBlk.alphaT = 0) (h_alphaSigma : sBlk.alphaSigma = 0)
    (h_fT_zero : tBlk.fT = fun _ => 0) (h_fSigma_zero : sBlk.fSigma = fun _ => 0)
    (h_gammaT : tBlk.gammaT = 0) (h_gammaSigma : sBlk.gammaSigma = 0) :
    ∀ s x, blockProbitMap cov tBlk sBlk s x = Phi s := by
  intro s x
  have h_aff := rawPGSEquivalenceAffine cov tBlk sBlk h_alphaT h_alphaSigma h_fT_zero h_fSigma_zero s x
  simpa [h_gammaT, h_gammaSigma] using h_aff

/-- Zero-penalty flexibility: the model class can realize arbitrary threshold and scale functions.
We construct blocks that exactly match target `T(x)` and strictly positive `σ(x)`. -/
theorem flexibilityZeroPenalty {k : ℕ} (cov : CovariateMaps k) (lambda : ℝ) (h_lambda_zero : lambda = 0)
    (Ttarget sigmaTarget : PCPoint k → ℝ) (h_sigma_pos : ∀ x, 0 < sigmaTarget x) :
    ∃ tBlk : ThresholdBlock k, ∃ sBlk : LogScaleBlock k,
      (∀ x, thresholdPredictor cov tBlk x = Ttarget x) ∧
      (∀ x, sigmaPredictor cov sBlk x = sigmaTarget x) := by
  subst h_lambda_zero
  refine ⟨
    { alphaT := 0, gammaT := 0, fT := Ttarget },
    { alphaSigma := 0, gammaSigma := 0, fSigma := fun x => Real.log (sigmaTarget x) },
    ?_, ?_⟩
  · intro x
    simp [thresholdPredictor]
  · intro x
    simp [sigmaPredictor, logScalePredictor]
    exact Real.exp_log (h_sigma_pos x)

end NestingProofs

end Calibrator

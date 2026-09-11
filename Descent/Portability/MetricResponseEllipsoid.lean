/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricOrderingClassification

assert_below Descent.Decision Descent.Program

/-!
# The exact constrained metric-response ellipsoid

On a finite report space with a strictly positive law `P`, `wInner` is the
law-weighted inner product and `gramMatrix` is the Gram matrix of the residual
influence functions. An information-preserving perturbation direction is a
finite list of linear constraints: orthogonality to the constant function and to
each retained feature. `constrained_response_ellipsoid` is TQ Theorem 5.2 in the
pseudoinverse-free form `{Γ a : aᵀ Γ a ≤ 1}`, which is exactly the manuscript's
`{z ∈ range Γ : zᵀ Γ⁺ z ≤ 1}` because `Γ Γ⁺ Γ = Γ`; stating it this way needs no
Moore-Penrose inverse. The hard inclusion rests on
`exists_projection_coefficients`, an explicit finite Gram-Schmidt construction of
the orthogonal projection onto the span of the residual influences, proved here
rather than assumed. `wInner_eq_weightedExp` identifies `wInner` with the corpus
expectation `weightedExp` of `Descent.Portability.PortabilityMasterTheorem`, so
the geometry here is the geometry of that expectation functional.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MetricResponseEllipsoid

open Foundations

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- The law-weighted inner product `⟨f, g⟩_P = ∑ P ω f ω g ω` on a finite space. -/
def wInner (P f g : Ω → ℝ) : ℝ := ∑ ω, P ω * f ω * g ω

/-- **The corpus tie.** The weighted inner product is the corpus expectation
`weightedExp` of the pointwise product, so every expectation identity proved for
`ExpFunctional` applies to the geometry below. -/
theorem wInner_eq_weightedExp (P : Ω → ℝ) (hp : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1)
    (f g : Ω → ℝ) : wInner P f g = weightedExp P hp hsum (fun ω ↦ f ω * g ω) := by
  simp only [wInner, weightedExp_apply]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- The weighted inner product is symmetric. -/
theorem wInner_comm (P f g : Ω → ℝ) : wInner P f g = wInner P g f := by
  simp only [wInner]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Additivity in the left slot. -/
theorem wInner_add_left (P f g h : Ω → ℝ) :
    wInner P (fun ω ↦ f ω + g ω) h = wInner P f h + wInner P g h := by
  simp only [wInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Subtractivity in the left slot. -/
theorem wInner_sub_left (P f g h : Ω → ℝ) :
    wInner P (fun ω ↦ f ω - g ω) h = wInner P f h - wInner P g h := by
  simp only [wInner, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Subtractivity in the right slot. -/
theorem wInner_sub_right (P f g h : Ω → ℝ) :
    wInner P f (fun ω ↦ g ω - h ω) = wInner P f g - wInner P f h := by
  simp only [wInner, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Homogeneity in the right slot. -/
theorem wInner_smul_right (P f g : Ω → ℝ) (c : ℝ) :
    wInner P f (fun ω ↦ c * g ω) = c * wInner P f g := by
  simp only [wInner, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- A weighted finite combination in the left slot expands linearly. -/
theorem wInner_weighted_sum_left {ι : Type*} (P h : Ω → ℝ) (s : Finset ι) (a : ι → ℝ)
    (g : ι → Ω → ℝ) :
    wInner P (fun ω ↦ ∑ i ∈ s, a i * g i ω) h = ∑ i ∈ s, a i * wInner P (g i) h := by
  calc wInner P (fun ω ↦ ∑ i ∈ s, a i * g i ω) h
      = ∑ ω, ∑ i ∈ s, a i * (P ω * g i ω * h ω) := by
        simp only [wInner]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ i ∈ s, ∑ ω, a i * (P ω * g i ω * h ω) := Finset.sum_comm
    _ = ∑ i ∈ s, a i * wInner P (g i) h := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [wInner, Finset.mul_sum]

/-- The weighted inner product of a function with itself is nonnegative. -/
theorem wInner_self_nonneg {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (f : Ω → ℝ) :
    0 ≤ wInner P f f :=
  Finset.sum_nonneg fun ω _ ↦ by
    have hrw : P ω * f ω * f ω = P ω * (f ω * f ω) := by ring
    rw [hrw]
    exact mul_nonneg (hP ω) (mul_self_nonneg _)

/-- Pythagoras: the squared norm splits along a base point and its residual. -/
theorem wInner_self_split (P f g : Ω → ℝ) :
    wInner P f f = wInner P g g + 2 * wInner P g (fun ω ↦ f ω - g ω) +
      wInner P (fun ω ↦ f ω - g ω) (fun ω ↦ f ω - g ω) := by
  simp only [wInner]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- With a strictly positive law, a vector of zero norm annihilates every other
vector: it is the zero function pointwise. -/
theorem wInner_left_zero_of_self_zero {P : Ω → ℝ} (hP : ∀ ω, 0 < P ω) {w : Ω → ℝ}
    (hw : wInner P w w = 0) (u : Ω → ℝ) : wInner P w u = 0 := by
  have hnn : ∀ ν ∈ (Finset.univ : Finset Ω), 0 ≤ P ν * w ν * w ν := by
    intro ν _
    have hrw : P ν * w ν * w ν = P ν * (w ν * w ν) := by ring
    rw [hrw]
    exact mul_nonneg (hP ν).le (mul_self_nonneg _)
  simp only [wInner] at hw
  have hzero : ∀ ω, w ω = 0 := by
    intro ω
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hw ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp hterm with hpw | hwω
    · rcases mul_eq_zero.mp hpw with hp | hwω
      · exact absurd hp (hP ω).ne'
      · exact hwω
    · exact hwω
  simp only [wInner]
  exact Finset.sum_eq_zero fun ω _ ↦ by rw [hzero ω]; ring

/-- **Finite Gram-Schmidt.** For every finite index set and every function there
are coefficients whose combination of the family leaves a residual orthogonal to
each member of the family. This is the orthogonal projection onto the span,
constructed rather than assumed, and it is what makes the ellipsoid inclusion
unconditional. The law is strictly positive, exactly the manuscript's
nondegeneracy condition. -/
theorem exists_projection_coefficients {ι : Type*} [DecidableEq ι] {P : Ω → ℝ}
    (hP : ∀ ω, 0 < P ω) (r : ι → Ω → ℝ) (s : Finset ι) :
    ∀ f : Ω → ℝ, ∃ a : ι → ℝ,
      ∀ j ∈ s, wInner P (r j) (fun ω ↦ f ω - ∑ i ∈ s, a i * r i ω) = 0 := by
  refine Finset.induction_on s ?_ ?_
  · intro f
    exact ⟨fun _ ↦ 0, by simp⟩
  · intro k s' hk ih f
    obtain ⟨a', ha'⟩ := ih f
    obtain ⟨b', hb'⟩ := ih (r k)
    set c : ℝ := wInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) /
      wInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) with hcdef
    have hcomb : ∀ u : Ω → ℝ,
        wInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω) u = ∑ i ∈ s', b' i * wInner P (r i) u :=
      fun u ↦ wInner_weighted_sum_left P u s' b' r
    have hhb : wInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
        (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0 := by
      rw [hcomb]
      exact Finset.sum_eq_zero fun i hi ↦ by rw [hb' i hi, mul_zero]
    have hha : wInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
        (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) = 0 := by
      rw [hcomb]
      exact Finset.sum_eq_zero fun i hi ↦ by rw [ha' i hi, mul_zero]
    have hkey : c * wInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) =
        wInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := by
      by_cases hb : wInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0
      · rw [hb, mul_zero]
        have hww : wInner P (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω)
            (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0 := by
          rw [wInner_sub_left, hb, hhb, sub_zero]
        have hwa := wInner_left_zero_of_self_zero hP hww
          (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω)
        have hid : (fun ω ↦ (r k ω - ∑ i ∈ s', b' i * r i ω) +
            ∑ i ∈ s', b' i * r i ω) = r k := by
          funext ω
          ring
        calc wInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω)
            = wInner P (fun ω ↦ (r k ω - ∑ i ∈ s', b' i * r i ω) +
                ∑ i ∈ s', b' i * r i ω) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := by
              rw [hid]
          _ = wInner P (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω)
                (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) +
              wInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
                (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := wInner_add_left _ _ _ _
          _ = 0 := by rw [hwa, hha, add_zero]
      · rw [hcdef]
        field_simp
    refine ⟨fun i ↦ if i = k then c else a' i - c * b' i, ?_⟩
    intro j hj
    have hres : (fun ω ↦ f ω - ∑ i ∈ insert k s',
        (if i = k then c else a' i - c * b' i) * r i ω) =
        (fun ω ↦ (f ω - ∑ i ∈ s', a' i * r i ω) -
          c * (r k ω - ∑ i ∈ s', b' i * r i ω)) := by
      funext ω
      rw [Finset.sum_insert hk, if_pos rfl]
      have hs : ∑ i ∈ s', (if i = k then c else a' i - c * b' i) * r i ω =
          (∑ i ∈ s', a' i * r i ω) - c * ∑ i ∈ s', b' i * r i ω := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hik : i ≠ k := fun hc ↦ hk (hc ▸ hi)
        rw [if_neg hik]
        ring
      rw [hs]
      ring
    rw [hres, wInner_sub_right, wInner_smul_right]
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · rw [hkey, sub_self]
    · rw [ha' j hjs, hb' j hjs, mul_zero, sub_zero]

/-- The Gram matrix of a finite family under the law-weighted inner product. -/
def gramMatrix {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ wInner P (r i) (r j)

/-- The Gram matrix is symmetric. -/
theorem gramMatrix_symm {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (i j : Fin m) :
    gramMatrix P r i j = gramMatrix P r j i :=
  wInner_comm P (r i) (r j)

/-- The inner product of the residual family's combination with one member is the
corresponding entry of the Gram matrix times the coefficients. -/
theorem wInner_comb_eq_gram {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (a : Fin m → ℝ)
    (j : Fin m) :
    wInner P (r j) (fun ω ↦ ∑ i, a i * r i ω) = ∑ i, gramMatrix P r j i * a i := by
  rw [wInner_comm, wInner_weighted_sum_left]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [gramMatrix, gramMatrix, wInner_comm P (r j) (r i)]
    ring

/-- The squared norm of the minimum-norm direction is the Gram quadratic form.
This is the second half of the manuscript's formula (5.10). -/
theorem wInner_comb_self {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (a : Fin m → ℝ) :
    wInner P (fun ω ↦ ∑ i, a i * r i ω) (fun ω ↦ ∑ i, a i * r i ω) =
      ∑ j, a j * ∑ i, gramMatrix P r j i * a i := by
  rw [wInner_weighted_sum_left]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [wInner_comb_eq_gram]

/-- **TQ Theorem 5.2 (exact constrained metric-response ellipsoid).** On a finite
report space with a strictly positive law, the set of first-derivative vectors
attained by information-preserving directions of norm at most one is exactly the
set of `Γ a` with `aᵀ Γ a ≤ 1`, where `Γ` is the Gram matrix of the residual
influence functions. Equivalently it is `{z ∈ range Γ : zᵀ Γ⁺ z ≤ 1}`, because
every `z = Γ a` has `zᵀ Γ⁺ z = aᵀ Γ Γ⁺ Γ a = aᵀ Γ a`; the form used here needs no
pseudoinverse. The hypotheses are the manuscript's: the law is positive
everywhere, and each residual influence is orthogonal to the constant function
and to every retained feature, which is exactly what makes it a permissible
direction. -/
theorem constrained_response_ellipsoid {k m : ℕ} {P : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (feat : Fin k → Ω → ℝ) (r : Fin m → Ω → ℝ)
    (hrconst : ∀ j, wInner P (fun _ ↦ (1 : ℝ)) (r j) = 0)
    (hrfeat : ∀ j i, wInner P (feat i) (r j) = 0) (z : Fin m → ℝ) :
    (∃ f : Ω → ℝ, wInner P (fun _ ↦ (1 : ℝ)) f = 0 ∧ (∀ i, wInner P (feat i) f = 0) ∧
        wInner P f f ≤ 1 ∧ ∀ j, wInner P (r j) f = z j) ↔
      ∃ a : Fin m → ℝ, (∀ j, z j = ∑ i, gramMatrix P r j i * a i) ∧
        ∑ j, a j * ∑ i, gramMatrix P r j i * a i ≤ 1 := by
  constructor
  · rintro ⟨f, _, _, hnorm, hz⟩
    obtain ⟨a, ha⟩ := exists_projection_coefficients hP r Finset.univ f
    have horth : ∀ j : Fin m,
        wInner P (r j) (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 :=
      fun j ↦ ha j (Finset.mem_univ j)
    have heq : ∀ j : Fin m, wInner P (r j) f = ∑ i, gramMatrix P r j i * a i := by
      intro j
      have hsub := wInner_sub_right P (r j) f (fun ω ↦ ∑ i, a i * r i ω)
      rw [horth j] at hsub
      have := hsub.symm
      rw [wInner_comb_eq_gram] at this
      linarith [this]
    refine ⟨a, fun j ↦ by rw [← hz j, heq j], ?_⟩
    have hcross : wInner P (fun ω ↦ ∑ i, a i * r i ω)
        (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 := by
      rw [wInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [horth i, mul_zero]
    have hsplit := wInner_self_split P f (fun ω ↦ ∑ i, a i * r i ω)
    rw [hcross, mul_zero, add_zero] at hsplit
    have hrest : 0 ≤ wInner P (fun ω ↦ f ω - ∑ i, a i * r i ω)
        (fun ω ↦ f ω - ∑ i, a i * r i ω) :=
      wInner_self_nonneg (fun ω ↦ (hP ω).le) _
    rw [← wInner_comb_self]
    linarith
  · rintro ⟨a, hz, hq⟩
    refine ⟨fun ω ↦ ∑ i, a i * r i ω, ?_, ?_, ?_, ?_⟩
    · rw [wInner_comm, wInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun i _ ↦ by
        rw [wInner_comm P (r i) (fun _ ↦ (1 : ℝ)), hrconst i, mul_zero]
    · intro i
      rw [wInner_comm, wInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun j _ ↦ by
        rw [wInner_comm P (r j) (feat i), hrfeat j i, mul_zero]
    · rw [wInner_comb_self]
      exact hq
    · intro j
      rw [wInner_comb_eq_gram]
      exact (hz j).symm

/-- **TQ formula (5.10).** Among all directions producing a given derivative
vector, the combination of residual influences has the smallest norm, and that
norm is the Gram quadratic form of its coefficients. No constraint beyond
matching the derivative vector is imposed on the competitor. -/
theorem minimum_norm_direction {m : ℕ} {P : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (r : Fin m → Ω → ℝ) (a : Fin m → ℝ) (f : Ω → ℝ)
    (hmatch : ∀ j, wInner P (r j) f = ∑ i, gramMatrix P r j i * a i) :
    wInner P (fun ω ↦ ∑ i, a i * r i ω) (fun ω ↦ ∑ i, a i * r i ω) ≤ wInner P f f := by
  have hcross : wInner P (fun ω ↦ ∑ i, a i * r i ω)
      (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 := by
    rw [wInner_weighted_sum_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hsub := wInner_sub_right P (r i) f (fun ω ↦ ∑ j, a j * r j ω)
    rw [hmatch i, wInner_comb_eq_gram] at hsub
    rw [hsub, sub_self, mul_zero]
  have hsplit := wInner_self_split P f (fun ω ↦ ∑ i, a i * r i ω)
  rw [hcross, mul_zero, add_zero] at hsplit
  have hrest : 0 ≤ wInner P (fun ω ↦ f ω - ∑ i, a i * r i ω)
      (fun ω ↦ f ω - ∑ i, a i * r i ω) :=
    wInner_self_nonneg (fun ω ↦ (hP ω).le) _
  linarith

end

end Descent.Portability.MetricResponseEllipsoid

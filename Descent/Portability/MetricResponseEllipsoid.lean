/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem

assert_below Descent.Decision Descent.Program

/-!
# The exact constrained metric-response ellipsoid

On a finite report space with a strictly positive law `P`, `weightedInner` is the
law-weighted inner product and `gramMatrix` is the Gram matrix of the residual
influence functions. An information-preserving perturbation direction is a
finite list of linear constraints: orthogonality to the constant function and to
each retained feature. `constrained_response_ellipsoid` is TQ Theorem 5.2 in the
pseudoinverse-free form `{Γ a : aᵀ Γ a ≤ 1}`, which is exactly the manuscript's
`{z ∈ range Γ : zᵀ Γ⁺ z ≤ 1}` because `Γ Γ⁺ Γ = Γ`; stating it this way needs no
Moore-Penrose inverse. The hard inclusion rests on
`exists_projection_coefficients`, an explicit finite Gram-Schmidt construction of
the orthogonal projection onto the span of the residual influences, proved here
rather than assumed. `weightedInner_eq_weightedExp` identifies `weightedInner` with the corpus
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
def weightedInner (P f g : Ω → ℝ) : ℝ := ∑ ω, P ω * f ω * g ω

/-- **The corpus tie.** The weighted inner product is the corpus expectation
`weightedExp` of the pointwise product, so every expectation identity proved for
`ExpFunctional` applies to the geometry below. -/
theorem weightedInner_eq_weightedExp (P : Ω → ℝ) (hp : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1)
    (f g : Ω → ℝ) : weightedInner P f g = weightedExp P hp hsum (fun ω ↦ f ω * g ω) := by
  simp only [weightedInner, weightedExp_apply]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- The weighted inner product is symmetric. -/
theorem weightedInner_comm (P f g : Ω → ℝ) : weightedInner P f g = weightedInner P g f := by
  simp only [weightedInner]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Additivity in the left slot. -/
theorem weightedInner_add_left (P f g h : Ω → ℝ) :
    weightedInner P (fun ω ↦ f ω + g ω) h = weightedInner P f h + weightedInner P g h := by
  simp only [weightedInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Subtractivity in the left slot. -/
theorem weightedInner_sub_left (P f g h : Ω → ℝ) :
    weightedInner P (fun ω ↦ f ω - g ω) h = weightedInner P f h - weightedInner P g h := by
  simp only [weightedInner, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- Subtractivity in the right slot. -/
theorem weightedInner_sub_right (P f g h : Ω → ℝ) :
    weightedInner P f (fun ω ↦ g ω - h ω) = weightedInner P f g - weightedInner P f h := by
  rw [weightedInner_comm, weightedInner_sub_left, weightedInner_comm P g f,
    weightedInner_comm P h f]

/-- Homogeneity in the right slot. -/
theorem weightedInner_smul_right (P f g : Ω → ℝ) (c : ℝ) :
    weightedInner P f (fun ω ↦ c * g ω) = c * weightedInner P f g := by
  simp only [weightedInner, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- A weighted finite combination in the left slot expands linearly. -/
theorem weightedInner_weighted_sum_left {ι : Type*} (P h : Ω → ℝ) (s : Finset ι) (a : ι → ℝ)
    (g : ι → Ω → ℝ) :
    weightedInner P (fun ω ↦ ∑ i ∈ s, a i * g i ω) h = ∑ i ∈ s, a i * weightedInner P (g i) h := by
  calc weightedInner P (fun ω ↦ ∑ i ∈ s, a i * g i ω) h
      = ∑ ω, ∑ i ∈ s, a i * (P ω * g i ω * h ω) := by
        simp only [weightedInner]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ i ∈ s, ∑ ω, a i * (P ω * g i ω * h ω) := Finset.sum_comm
    _ = ∑ i ∈ s, a i * weightedInner P (g i) h := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [weightedInner, Finset.mul_sum]

/-- The weighted inner product of a function with itself is nonnegative. -/
theorem weightedInner_self_nonneg {P : Ω → ℝ} (hP : ∀ ω, 0 ≤ P ω) (f : Ω → ℝ) :
    0 ≤ weightedInner P f f :=
  Finset.sum_nonneg fun ω _ ↦ by
    have hrw : P ω * f ω * f ω = P ω * (f ω * f ω) := by ring
    rw [hrw]
    exact mul_nonneg (hP ω) (mul_self_nonneg _)

/-- Pythagoras: the squared norm splits along a base point and its residual. -/
theorem weightedInner_self_split (P f g : Ω → ℝ) :
    weightedInner P f f = weightedInner P g g + 2 * weightedInner P g (fun ω ↦ f ω - g ω) +
      weightedInner P (fun ω ↦ f ω - g ω) (fun ω ↦ f ω - g ω) := by
  simp only [weightedInner]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

/-- With a strictly positive law, a vector of zero norm annihilates every other
vector: it is the zero function pointwise. -/
theorem weightedInner_left_zero_of_self_zero {P : Ω → ℝ} (hP : ∀ ω, 0 < P ω) {w : Ω → ℝ}
    (hw : weightedInner P w w = 0) (u : Ω → ℝ) : weightedInner P w u = 0 := by
  have hnn : ∀ ν ∈ (Finset.univ : Finset Ω), 0 ≤ P ν * w ν * w ν := by
    intro ν _
    have hrw : P ν * w ν * w ν = P ν * (w ν * w ν) := by ring
    rw [hrw]
    exact mul_nonneg (hP ν).le (mul_self_nonneg _)
  simp only [weightedInner] at hw
  have hzero : ∀ ω, w ω = 0 := by
    intro ω
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hw ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp hterm with hpw | hwω
    · rcases mul_eq_zero.mp hpw with hp | hwω
      · exact absurd hp (hP ω).ne'
      · exact hwω
    · exact hwω
  simp only [weightedInner]
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
      ∀ j ∈ s, weightedInner P (r j) (fun ω ↦ f ω - ∑ i ∈ s, a i * r i ω) = 0 := by
  refine Finset.induction_on s ?_ ?_
  · intro f
    exact ⟨fun _ ↦ 0, by simp⟩
  · intro k s' hk ih f
    obtain ⟨a', ha'⟩ := ih f
    obtain ⟨b', hb'⟩ := ih (r k)
    set c : ℝ := weightedInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) /
      weightedInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) with hcdef
    have hcomb : ∀ u : Ω → ℝ,
        weightedInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω) u =
          ∑ i ∈ s', b' i * weightedInner P (r i) u :=
      fun u ↦ weightedInner_weighted_sum_left P u s' b' r
    have hhb : weightedInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
        (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0 := by
      rw [hcomb]
      exact Finset.sum_eq_zero fun i hi ↦ by rw [hb' i hi, mul_zero]
    have hha : weightedInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
        (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) = 0 := by
      rw [hcomb]
      exact Finset.sum_eq_zero fun i hi ↦ by rw [ha' i hi, mul_zero]
    have hkey : c * weightedInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) =
        weightedInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := by
      by_cases hb : weightedInner P (r k) (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0
      · rw [hb, mul_zero]
        symm
        have hww : weightedInner P (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω)
            (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω) = 0 := by
          rw [weightedInner_sub_left, hb, hhb, sub_zero]
        have hwa := weightedInner_left_zero_of_self_zero hP hww
          (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω)
        have hid : (fun ω ↦ (r k ω - ∑ i ∈ s', b' i * r i ω) +
            ∑ i ∈ s', b' i * r i ω) = r k := by
          funext ω
          ring
        calc weightedInner P (r k) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω)
            = weightedInner P (fun ω ↦ (r k ω - ∑ i ∈ s', b' i * r i ω) +
                ∑ i ∈ s', b' i * r i ω) (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := by
              rw [hid]
          _ = weightedInner P (fun ω ↦ r k ω - ∑ i ∈ s', b' i * r i ω)
                (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) +
              weightedInner P (fun ω ↦ ∑ i ∈ s', b' i * r i ω)
                (fun ω ↦ f ω - ∑ i ∈ s', a' i * r i ω) := weightedInner_add_left _ _ _ _
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
    rw [hres, weightedInner_sub_right, weightedInner_smul_right]
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · rw [hkey, sub_self]
    · rw [ha' j hjs, hb' j hjs, mul_zero, sub_zero]

/-- The Gram matrix of a finite family under the law-weighted inner product. -/
def gramMatrix {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ weightedInner P (r i) (r j)

/-- The Gram matrix is symmetric. -/
theorem gramMatrix_symm {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (i j : Fin m) :
    gramMatrix P r i j = gramMatrix P r j i :=
  weightedInner_comm P (r i) (r j)

/-- The inner product of the residual family's combination with one member is the
corresponding entry of the Gram matrix times the coefficients. -/
theorem weightedInner_comb_eq_gram {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (a : Fin m → ℝ)
    (j : Fin m) :
    weightedInner P (r j) (fun ω ↦ ∑ i, a i * r i ω) = ∑ i, gramMatrix P r j i * a i := by
  rw [weightedInner_comm, weightedInner_weighted_sum_left]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [gramMatrix]
  rw [weightedInner_comm P (r j) (r i)]
  ring

/-- The squared norm of the minimum-norm direction is the Gram quadratic form.
This is the second half of the manuscript's formula (5.10). -/
theorem weightedInner_comb_self {m : ℕ} (P : Ω → ℝ) (r : Fin m → Ω → ℝ) (a : Fin m → ℝ) :
    weightedInner P (fun ω ↦ ∑ i, a i * r i ω) (fun ω ↦ ∑ i, a i * r i ω) =
      ∑ j, a j * ∑ i, gramMatrix P r j i * a i := by
  rw [weightedInner_weighted_sum_left]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [weightedInner_comb_eq_gram]

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
    (hrconst : ∀ j, weightedInner P (fun _ ↦ (1 : ℝ)) (r j) = 0)
    (hrfeat : ∀ j i, weightedInner P (feat i) (r j) = 0) (z : Fin m → ℝ) :
    (∃ f : Ω → ℝ, weightedInner P (fun _ ↦ (1 : ℝ)) f = 0 ∧ (∀ i, weightedInner P (feat i) f = 0) ∧
        weightedInner P f f ≤ 1 ∧ ∀ j, weightedInner P (r j) f = z j) ↔
      ∃ a : Fin m → ℝ, (∀ j, z j = ∑ i, gramMatrix P r j i * a i) ∧
        ∑ j, a j * ∑ i, gramMatrix P r j i * a i ≤ 1 := by
  constructor
  · rintro ⟨f, _, _, hnorm, hz⟩
    obtain ⟨a, ha⟩ := exists_projection_coefficients hP r Finset.univ f
    have horth : ∀ j : Fin m,
        weightedInner P (r j) (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 :=
      fun j ↦ ha j (Finset.mem_univ j)
    have heq : ∀ j : Fin m, weightedInner P (r j) f = ∑ i, gramMatrix P r j i * a i := by
      intro j
      have hsub := weightedInner_sub_right P (r j) f (fun ω ↦ ∑ i, a i * r i ω)
      rw [horth j] at hsub
      have := hsub.symm
      rw [weightedInner_comb_eq_gram] at this
      linarith [this]
    refine ⟨a, fun j ↦ by rw [← hz j, heq j], ?_⟩
    have hcross : weightedInner P (fun ω ↦ ∑ i, a i * r i ω)
        (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 := by
      rw [weightedInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun i _ ↦ by rw [horth i, mul_zero]
    have hsplit := weightedInner_self_split P f (fun ω ↦ ∑ i, a i * r i ω)
    rw [hcross, mul_zero, add_zero] at hsplit
    have hrest : 0 ≤ weightedInner P (fun ω ↦ f ω - ∑ i, a i * r i ω)
        (fun ω ↦ f ω - ∑ i, a i * r i ω) :=
      weightedInner_self_nonneg (fun ω ↦ (hP ω).le) _
    rw [← weightedInner_comb_self]
    linarith
  · rintro ⟨a, hz, hq⟩
    refine ⟨fun ω ↦ ∑ i, a i * r i ω, ?_, ?_, ?_, ?_⟩
    · rw [weightedInner_comm, weightedInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun i _ ↦ by
        rw [weightedInner_comm P (r i) (fun _ ↦ (1 : ℝ)), hrconst i, mul_zero]
    · intro i
      rw [weightedInner_comm, weightedInner_weighted_sum_left]
      exact Finset.sum_eq_zero fun j _ ↦ by
        rw [weightedInner_comm P (r j) (feat i), hrfeat j i, mul_zero]
    · rw [weightedInner_comb_self]
      exact hq
    · intro j
      rw [weightedInner_comb_eq_gram]
      exact (hz j).symm

/-- **TQ formula (5.10).** Among all directions producing a given derivative
vector, the combination of residual influences has the smallest norm, and that
norm is the Gram quadratic form of its coefficients. No constraint beyond
matching the derivative vector is imposed on the competitor. -/
theorem minimum_norm_direction {m : ℕ} {P : Ω → ℝ} (hP : ∀ ω, 0 < P ω)
    (r : Fin m → Ω → ℝ) (a : Fin m → ℝ) (f : Ω → ℝ)
    (hmatch : ∀ j, weightedInner P (r j) f = ∑ i, gramMatrix P r j i * a i) :
    weightedInner P (fun ω ↦ ∑ i, a i * r i ω) (fun ω ↦ ∑ i, a i * r i ω) ≤
      weightedInner P f f := by
  have hcross : weightedInner P (fun ω ↦ ∑ i, a i * r i ω)
      (fun ω ↦ f ω - ∑ i, a i * r i ω) = 0 := by
    rw [weightedInner_weighted_sum_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hsub := weightedInner_sub_right P (r i) f (fun ω ↦ ∑ j, a j * r j ω)
    rw [hmatch i, weightedInner_comb_eq_gram] at hsub
    rw [hsub, sub_self, mul_zero]
  have hsplit := weightedInner_self_split P f (fun ω ↦ ∑ i, a i * r i ω)
  rw [hcross, mul_zero, add_zero] at hsplit
  have hrest : 0 ≤ weightedInner P (fun ω ↦ f ω - ∑ i, a i * r i ω)
      (fun ω ↦ f ω - ∑ i, a i * r i ω) :=
    weightedInner_self_nonneg (fun ω ↦ (hP ω).le) _
  linarith

/-- Homogeneity in the left slot. -/
theorem weightedInner_smul_left (P f g : Ω → ℝ) (c : ℝ) :
    weightedInner P (fun ω ↦ c * f ω) g = c * weightedInner P f g := by
  rw [weightedInner_comm, weightedInner_smul_right, weightedInner_comm P g f]

/-- Additivity in the right slot. -/
theorem weightedInner_add_right (P f g h : Ω → ℝ) :
    weightedInner P f (fun ω ↦ g ω + h ω) = weightedInner P f g + weightedInner P f h := by
  rw [weightedInner_comm, weightedInner_add_left, weightedInner_comm P g f,
    weightedInner_comm P h f]

/-- Scaling a direction scales its squared norm quadratically. -/
theorem weightedInner_smul_self (P u : Ω → ℝ) (c : ℝ) :
    weightedInner P (fun ω ↦ c * u ω) (fun ω ↦ c * u ω) = c ^ 2 * weightedInner P u u := by
  rw [weightedInner_smul_left, weightedInner_smul_right]
  ring

/-- Cauchy-Schwarz for the law-weighted inner product, obtained from the corpus
inequality `Foundations.cauchy_schwarz` for the expectation `weightedExp`. -/
theorem weightedInner_cauchy_schwarz (P : Ω → ℝ) (hp : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1)
    (f g : Ω → ℝ) : weightedInner P f g ^ 2 ≤ weightedInner P f f * weightedInner P g g := by
  have hcs := ExpFunctional.cauchy_schwarz (weightedExp P hp hsum) f g
  rw [weightedInner_eq_weightedExp P hp hsum f g, weightedInner_eq_weightedExp P hp hsum f f,
    weightedInner_eq_weightedExp P hp hsum g g]
  have hf : (fun ω ↦ f ω * f ω) = fun ω ↦ f ω ^ 2 := by
    funext ω
    ring
  have hg : (fun ω ↦ g ω * g ω) = fun ω ↦ g ω ^ 2 := by
    funext ω
    ring
  rw [hf, hg]
  exact hcs

/-- **TQ Corollary 5.3 (sharp summary-invisible sensitivity).** The largest
first-order move of a single metric along an information-preserving direction of
norm at most one is exactly the norm of its residual influence function, and both
signs are attained by an explicit direction: the normalised residual influence
and its negative. The bound is Cauchy-Schwarz; the attainment is a construction,
so the supremum is a maximum. -/
theorem sharp_summary_invisible_sensitivity {k : ℕ} {P : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ P ω) (hsum : ∑ ω, P ω = 1) (feat : Fin k → Ω → ℝ) (rr : Ω → ℝ)
    (hrconst : weightedInner P (fun _ ↦ (1 : ℝ)) rr = 0)
    (hrfeat : ∀ i, weightedInner P (feat i) rr = 0) (hpos : 0 < weightedInner P rr rr) :
    (∀ f : Ω → ℝ, weightedInner P (fun _ ↦ (1 : ℝ)) f = 0 → (∀ i, weightedInner P (feat i) f = 0) →
        weightedInner P f f ≤ 1 → |weightedInner P rr f| ≤ Real.sqrt (weightedInner P rr rr)) ∧
      ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ f : Ω → ℝ, weightedInner P (fun _ ↦ (1 : ℝ)) f = 0 ∧
          (∀ i, weightedInner P (feat i) f = 0) ∧ weightedInner P f f ≤ 1 ∧
          weightedInner P rr f = sign * Real.sqrt (weightedInner P rr rr) := by
  have hroot : 0 < Real.sqrt (weightedInner P rr rr) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (weightedInner P rr rr) ^ 2 = weightedInner P rr rr := Real.sq_sqrt hpos.le
  set nrm : ℝ := Real.sqrt (weightedInner P rr rr) with hnrm
  have hne : nrm ≠ 0 := ne_of_gt hroot
  constructor
  · intro f _ _ hnorm
    have hcs := weightedInner_cauchy_schwarz P hp hsum rr f
    have hb : weightedInner P rr f ^ 2 ≤ weightedInner P rr rr := by nlinarith [hpos.le]
    calc |weightedInner P rr f|
        = Real.sqrt (weightedInner P rr f ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ nrm := Real.sqrt_le_sqrt hb
  · intro sign hsign
    have hkey : nrm⁻¹ * weightedInner P rr rr = nrm := by
      rw [← hsq, sq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have hnormsq : (sign * nrm⁻¹) ^ 2 * weightedInner P rr rr = sign ^ 2 := by
      rw [mul_pow, inv_pow, ← hsq, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hne), mul_one]
    refine ⟨fun ω ↦ sign * nrm⁻¹ * rr ω, ?_, ?_, ?_, ?_⟩
    · rw [weightedInner_smul_right, hrconst, mul_zero]
    · intro i
      rw [weightedInner_smul_right, hrfeat i, mul_zero]
    · rw [weightedInner_smul_self, hnormsq]
      rcases hsign with h | h <;> rw [h] <;> norm_num
    · rw [weightedInner_smul_right, mul_assoc, hkey]

/-- The product of the two first-order metric responses along a direction, when
the residual influences are proportional. Its sign is the sign of the
proportionality constant, in every permissible direction at once. -/
theorem proportional_residual_derivative_product (P : Ω → ℝ) (r1 r2 : Ω → ℝ) (c : ℝ)
    (hprop : ∀ ω, r2 ω = c * r1 ω) (f : Ω → ℝ) :
    weightedInner P r1 f * weightedInner P r2 f = c * weightedInner P r1 f ^ 2 := by
  have hfun : r2 = fun ω ↦ c * r1 ω := funext hprop
  rw [hfun, weightedInner_smul_left]
  ring

/-- **TQ Corollary 5.4, aligned case.** A positive proportionality constant makes
the two metric derivatives agree in sign in every permissible direction, and the
agreement is strict whenever the first derivative is nonzero. -/
theorem proportional_residual_sign_agreement (P : Ω → ℝ) (r1 r2 : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (hprop : ∀ ω, r2 ω = c * r1 ω) (f : Ω → ℝ) :
    0 ≤ weightedInner P r1 f * weightedInner P r2 f ∧
      (weightedInner P r1 f ≠ 0 → 0 < weightedInner P r1 f * weightedInner P r2 f) := by
  rw [proportional_residual_derivative_product P r1 r2 c hprop f]
  exact ⟨mul_nonneg hc.le (sq_nonneg _), fun h ↦
    mul_pos hc (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h)))⟩

/-- **TQ Corollary 5.4, reversed case.** A negative proportionality constant makes
the two metric derivatives disagree in sign in every permissible direction, and
the disagreement is strict whenever the first derivative is nonzero. -/
theorem proportional_residual_sign_reversal (P : Ω → ℝ) (r1 r2 : Ω → ℝ) {c : ℝ}
    (hc : c < 0) (hprop : ∀ ω, r2 ω = c * r1 ω) (f : Ω → ℝ) :
    weightedInner P r1 f * weightedInner P r2 f ≤ 0 ∧
      (weightedInner P r1 f ≠ 0 → weightedInner P r1 f * weightedInner P r2 f < 0) := by
  rw [proportional_residual_derivative_product P r1 r2 c hprop f]
  refine ⟨mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg _), fun h ↦ ?_⟩
  exact mul_neg_of_neg_of_pos hc
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h)))

/-- **TQ Corollary 5.4, independent case.** When the two residual influences have
a positive Gram determinant, every prescribed pair of first-order responses is
attained up to one positive scale factor by a single permissible direction. In
particular every pair of signs is attained, so nothing about the two metrics'
first-order behaviour is forced. The direction is written down explicitly from
the inverse of the two-by-two Gram matrix, then rescaled into the unit ball. -/
theorem independent_residuals_attain_response {k : ℕ} {P : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ P ω) (feat : Fin k → Ω → ℝ) (r1 r2 : Ω → ℝ)
    (h1c : weightedInner P (fun _ ↦ (1 : ℝ)) r1 = 0) (h1f : ∀ i, weightedInner P (feat i) r1 = 0)
    (h2c : weightedInner P (fun _ ↦ (1 : ℝ)) r2 = 0) (h2f : ∀ i, weightedInner P (feat i) r2 = 0)
    (hdet : 0 < weightedInner P r1 r1 * weightedInner P r2 r2 -
      weightedInner P r1 r2 ^ 2) (z1 z2 : ℝ) :
    ∃ (t : ℝ) (f : Ω → ℝ), 0 < t ∧ weightedInner P (fun _ ↦ (1 : ℝ)) f = 0 ∧
      (∀ i, weightedInner P (feat i) f = 0) ∧ weightedInner P f f ≤ 1 ∧
      weightedInner P r1 f = t * z1 ∧ weightedInner P r2 f = t * z2 := by
  have hsym : weightedInner P r2 r1 = weightedInner P r1 r2 := weightedInner_comm P r2 r1
  obtain ⟨a1, ha1⟩ : ∃ a : ℝ,
      a = weightedInner P r2 r2 * z1 - weightedInner P r1 r2 * z2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : ℝ,
      a = weightedInner P r1 r1 * z2 - weightedInner P r1 r2 * z1 := ⟨_, rfl⟩
  have hr1 : weightedInner P r1 (fun ω ↦ a1 * r1 ω + a2 * r2 ω) =
      (weightedInner P r1 r1 * weightedInner P r2 r2 - weightedInner P r1 r2 ^ 2) * z1 := by
    rw [weightedInner_add_right, weightedInner_smul_right, weightedInner_smul_right, ha1, ha2]
    ring
  have hr2 : weightedInner P r2 (fun ω ↦ a1 * r1 ω + a2 * r2 ω) =
      (weightedInner P r1 r1 * weightedInner P r2 r2 - weightedInner P r1 r2 ^ 2) * z2 := by
    rw [weightedInner_add_right, weightedInner_smul_right, weightedInner_smul_right, hsym, ha1, ha2]
    ring
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = weightedInner P (fun ω ↦ a1 * r1 ω + a2 * r2 ω)
      (fun ω ↦ a1 * r1 ω + a2 * r2 ω) := ⟨_, rfl⟩
  have hqnn : 0 ≤ q := by
    rw [hq]
    exact weightedInner_self_nonneg hp _
  have hden : (0 : ℝ) < q + 1 := by linarith
  refine ⟨(q + 1)⁻¹ * (weightedInner P r1 r1 * weightedInner P r2 r2 - weightedInner P r1 r2 ^ 2),
    fun ω ↦ (q + 1)⁻¹ * (a1 * r1 ω + a2 * r2 ω), mul_pos (inv_pos.mpr hden) hdet,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [weightedInner_smul_right, weightedInner_add_right, weightedInner_smul_right,
      weightedInner_smul_right,
      h1c, h2c]
    ring
  · intro i
    rw [weightedInner_smul_right, weightedInner_add_right, weightedInner_smul_right,
      weightedInner_smul_right,
      h1f i, h2f i]
    ring
  · rw [weightedInner_smul_self, ← hq, inv_pow, inv_mul_eq_div, div_le_one (pow_pos hden 2)]
    nlinarith
  · rw [weightedInner_smul_right, hr1, ← mul_assoc]
  · rw [weightedInner_smul_right, hr2, ← mul_assoc]

end

end Descent.Portability.MetricResponseEllipsoid

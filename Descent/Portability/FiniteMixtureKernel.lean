/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas

assert_below Descent.Decision Descent.Program

/-!
# Finite mixture kernels and the feature vectors of finitely supported laws

This module supplies the microscopic vocabulary used by the constructive realizability
argument of NOTE1 §2.1-§2.3. A `FiniteMixtureKernel B X` is a genuine probability kernel on
a bare type `X` whose branching is indexed by a finite type `B`: at each state it chooses a
branch with a nonnegative weight summing to one and then moves deterministically. This is
exactly the class of steps built in NOTE1 §2.3 (migration mixtures, recombination pulses,
allele-flip pulses, single-draw resampling), and it is deliberately the weakest notion that
still makes the pushforward of a finitely supported law finitely supported, so that no
measure theory is needed anywhere in the realization argument.

The action `apply` on observables is proved to be linear, constant-preserving, positive, a
sup-norm contraction on bounded observables, and a sup-norm contraction on differences. The
`deterministic` kernel and the `uniformMixture` of a finite family of kernels are the two
constructors used downstream; `apply_uniformMixture` is the averaging identity that lets a
microscopic step choose one physical stage uniformly at random instead of composing stages,
which is the formalization alternative offered at the end of NOTE1 §2.3.

`featureVector` is the feature vector `∑ ω, p ω • φ (point ω)` of a finitely supported law
presented as data (a finite index type, weights, and atoms). `featureVector_mem_convexHull`
places it in the realization body `conv (range φ)` of NOTE1 (2), and
`featureVector_pushforward` shows that pushing a law through a kernel replaces each atom's
feature by the kernel action on each coordinate. Together these are the one-step half of the
telescoping estimate NOTE1 (5).

`MicroscopicApproximation φ A` bundles the hypothesis (3) of NOTE1 Theorem 1: a family of
kernels indexed by the step size, a remainder bound vanishing as the step size decreases to
zero, and the uniform first-order expansion. It is stated with a coordinatewise absolute
value rather than a norm so that no normed-space instance on the feature space is required.
`trivialApproximation` is the in-corpus witness demanded of every hypothesis-bundling
structure; the substantive two-locus instance is supplied elsewhere.

What is NOT proved here: nothing about the limit semigroup, the closedness or compactness of
the realization body, or Carathéodory bounds on the number of atoms. Those are the content of
the companion modules. The kernels here are also not assumed to be Markov in any topological
sense; `X` carries no structure at all.

## Empirical status

None. The bodies here are algebra: every statement is an identity or inequality between
finite sums of real weights, provable from the two defining axioms of a probability vector,
so no measurement on any population could confirm or refute one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.dupNamespace false

namespace Descent.Portability.FiniteMixtureKernel

open scoped BigOperators

/-- A probability kernel on `X` with finitely many branches: at each state the branch weights
are nonnegative and sum to one, and each branch acts by a deterministic move. -/
structure FiniteMixtureKernel (B : Type*) [Fintype B] (X : Type*) where
  /-- The weight given to each branch at each state. -/
  weight : X → B → ℝ
  /-- The deterministic move performed on each branch. -/
  move : B → X → X
  /-- Branch weights are nonnegative. -/
  weight_nonneg : ∀ x b, 0 ≤ weight x b
  /-- Branch weights at each state sum to one. -/
  weight_sum : ∀ x, ∑ b, weight x b = 1

/-- The feature vector `∑ ω, p ω • φ (point ω)` of the finitely supported law with weights
`p` and atoms `point`, read through the feature map `φ`. -/
def featureVector {Ω X ι : Type*} [Fintype Ω] (p : Ω → ℝ) (point : Ω → X)
    (φ : X → ι → ℝ) : ι → ℝ :=
  ∑ ω, p ω • φ (point ω)

/-- The feature vector of a finitely supported probability law lies in the realization body
`conv (range φ)` of NOTE1 (2). This is the easy inclusion; no topology is used. -/
theorem featureVector_mem_convexHull {Ω X ι : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (point : Ω → X) (φ : X → ι → ℝ) :
    featureVector p point φ ∈ convexHull ℝ (Set.range φ) := by
  simp only [featureVector]
  exact (convex_convexHull ℝ (Set.range φ)).sum_mem (fun ω _ ↦ hp ω) hsum
    (fun ω _ ↦ subset_convexHull ℝ (Set.range φ) (Set.mem_range_self (point ω)))

namespace FiniteMixtureKernel

variable {B X : Type*} [Fintype B]

/-- The kernel acts on an observable by averaging its value after each branch move. -/
def apply (K : FiniteMixtureKernel B X) (f : X → ℝ) (x : X) : ℝ :=
  ∑ b, K.weight x b * f (K.move b x)

/-- The kernel action fixes constants, because the branch weights sum to one. -/
theorem apply_const (K : FiniteMixtureKernel B X) (c : ℝ) (x : X) :
    K.apply (fun _ ↦ c) x = c := by
  simp only [apply, ← Finset.sum_mul, K.weight_sum, one_mul]

/-- The kernel action is additive in the observable. -/
theorem apply_add (K : FiniteMixtureKernel B X) (f g : X → ℝ) (x : X) :
    K.apply (fun y ↦ f y + g y) x = K.apply f x + K.apply g x := by
  simp only [apply, mul_add, Finset.sum_add_distrib]

/-- The kernel action commutes with scaling the observable. -/
theorem apply_smul (K : FiniteMixtureKernel B X) (c : ℝ) (f : X → ℝ) (x : X) :
    K.apply (fun y ↦ c * f y) x = c * K.apply f x := by
  simp only [apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- The kernel action is additive on differences of observables. -/
theorem apply_sub (K : FiniteMixtureKernel B X) (f g : X → ℝ) (x : X) :
    K.apply (fun y ↦ f y - g y) x = K.apply f x - K.apply g x := by
  simp only [apply, mul_sub, Finset.sum_sub_distrib]

/-- The kernel action is positive: a nonnegative observable has nonnegative average. -/
theorem apply_nonneg (K : FiniteMixtureKernel B X) (f : X → ℝ) (hf : ∀ y, 0 ≤ f y) (x : X) :
    0 ≤ K.apply f x :=
  Finset.sum_nonneg fun b _ ↦ mul_nonneg (K.weight_nonneg x b) (hf _)

/-- A uniformly bounded observable stays bounded by the same constant under the kernel
action; this is the sup-norm contraction used in the telescoping estimate NOTE1 (5). -/
theorem apply_le_of_le (K : FiniteMixtureKernel B X) (f : X → ℝ) (M : ℝ)
    (hf : ∀ y, |f y| ≤ M) (x : X) : |K.apply f x| ≤ M := by
  have hstep : ∀ b ∈ (Finset.univ : Finset B),
      |K.weight x b * f (K.move b x)| ≤ K.weight x b * M := by
    intro b _
    rw [abs_mul, abs_of_nonneg (K.weight_nonneg x b)]
    exact mul_le_mul_of_nonneg_left (hf _) (K.weight_nonneg x b)
  calc |K.apply f x| ≤ ∑ b, |K.weight x b * f (K.move b x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, K.weight x b * M := Finset.sum_le_sum hstep
    _ = M := by rw [← Finset.sum_mul, K.weight_sum, one_mul]

/-- The kernel action contracts uniform distances between observables. -/
theorem apply_sub_le (K : FiniteMixtureKernel B X) (f g : X → ℝ) (M : ℝ)
    (hfg : ∀ y, |f y - g y| ≤ M) (x : X) : |K.apply f x - K.apply g x| ≤ M := by
  rw [← K.apply_sub f g x]
  exact K.apply_le_of_le (fun y ↦ f y - g y) M hfg x

/-- The kernel with a single branch that moves by `g`. -/
def deterministic {X : Type*} (g : X → X) : FiniteMixtureKernel Unit X where
  weight := fun _ _ ↦ 1
  move := fun _ x ↦ g x
  weight_nonneg := fun _ _ ↦ zero_le_one
  weight_sum := fun _ ↦ by simp

/-- The one-branch kernel evaluates an observable at the moved state. -/
theorem apply_deterministic {X : Type*} (g : X → X) (f : X → ℝ) (x : X) :
    (deterministic g).apply f x = f (g x) := by
  simp [apply, deterministic]

/-- The kernel that first picks one of `Fintype.card S` sub-kernels uniformly at random and
then runs it. This is the stage-choosing construction of NOTE1 §2.3: a step whose generator
is the average of the sub-generators, with no composition lemma required. -/
noncomputable def uniformMixture {S : Type*} [Fintype S] (K : S → FiniteMixtureKernel B X)
    (hS : 0 < Fintype.card S) : FiniteMixtureKernel (S × B) X where
  weight := fun x sb ↦ (Fintype.card S : ℝ)⁻¹ * (K sb.1).weight x sb.2
  move := fun sb x ↦ (K sb.1).move sb.2 x
  weight_nonneg := fun x sb ↦
    mul_nonneg (by positivity) ((K sb.1).weight_nonneg x sb.2)
  weight_sum := fun x ↦ by
    have hrow : ∀ s : S, ∑ b : B, (Fintype.card S : ℝ)⁻¹ * (K s).weight x b
        = (Fintype.card S : ℝ)⁻¹ := fun s ↦ by
      rw [← Finset.mul_sum, (K s).weight_sum, mul_one]
    have hcard : (Fintype.card S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp only [Fintype.sum_prod_type, hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard

/-- The uniform mixture averages the actions of its sub-kernels. -/
theorem apply_uniformMixture {S : Type*} [Fintype S] (K : S → FiniteMixtureKernel B X)
    (hS : 0 < Fintype.card S) (f : X → ℝ) (x : X) :
    (uniformMixture K hS).apply f x
      = (Fintype.card S : ℝ)⁻¹ * ∑ s, (K s).apply f x := by
  simp only [apply, uniformMixture, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The weights of the law obtained by pushing a finitely supported law through the kernel:
the atom `(ω, b)` carries the mass of `ω` times the weight of branch `b` at its atom. -/
def pushforwardMass {Ω : Type*} (K : FiniteMixtureKernel B X) (p : Ω → ℝ)
    (point : Ω → X) : Ω × B → ℝ :=
  fun ωb ↦ p ωb.1 * K.weight (point ωb.1) ωb.2

/-- The atoms of the pushforward law: each original atom moved along each branch. -/
def pushforwardPoint {Ω : Type*} (K : FiniteMixtureKernel B X) (point : Ω → X) :
    Ω × B → X :=
  fun ωb ↦ K.move ωb.2 (point ωb.1)

/-- The pushforward weights are nonnegative. -/
theorem pushforwardMass_nonneg {Ω : Type*} (K : FiniteMixtureKernel B X) (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (point : Ω → X) (ωb : Ω × B) :
    0 ≤ K.pushforwardMass p point ωb :=
  mul_nonneg (hp _) (K.weight_nonneg _ _)

/-- The pushforward weights again sum to one, so a pushforward of a probability law is a
probability law: this is why every microscopic step of NOTE1 §2.3 stays inside the body. -/
theorem pushforwardMass_sum {Ω : Type*} [Fintype Ω] (K : FiniteMixtureKernel B X)
    (p : Ω → ℝ) (hsum : ∑ ω, p ω = 1) (point : Ω → X) :
    ∑ ωb, K.pushforwardMass p point ωb = 1 := by
  simp only [pushforwardMass, Fintype.sum_prod_type, ← Finset.mul_sum, K.weight_sum, mul_one]
  exact hsum

/-- The feature vector of the pushforward law is the original law averaged against the
kernel action on each feature coordinate. -/
theorem featureVector_pushforward {Ω ι : Type*} [Fintype Ω] (K : FiniteMixtureKernel B X)
    (p : Ω → ℝ) (point : Ω → X) (φ : X → ι → ℝ) :
    featureVector (K.pushforwardMass p point) (K.pushforwardPoint point) φ
      = ∑ ω, p ω • (fun i ↦ K.apply (fun y ↦ φ y i) (point ω)) := by
  funext i
  simp only [featureVector, pushforwardMass, pushforwardPoint, apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteMixtureKernel

/-- Hypothesis (3) of NOTE1 Theorem 1, bundled as data. `kernel h` is a genuine probability
kernel for every step size, `error` is a remainder bound vanishing as the step size decreases
to zero through positive values, and `expansion` is the uniform first-order expansion
`K_h φ = φ + h A φ + O(h · error h)`, stated coordinatewise so that the feature space needs
no norm. Assumes: nothing beyond the listed fields; `trivialApproximation` is a witness. -/
structure MicroscopicApproximation {ι B X : Type*} [Fintype ι] [Fintype B]
    (φ : X → ι → ℝ) (A : Matrix ι ι ℝ) where
  /-- The probability kernel used at step size `h`. -/
  kernel : ℝ → FiniteMixtureKernel B X
  /-- The uniform remainder bound at step size `h`. -/
  error : ℝ → ℝ
  /-- The remainder bound is nonnegative. -/
  error_nonneg : ∀ h, 0 ≤ error h
  /-- The remainder bound vanishes as the step size decreases to zero from above. -/
  error_tendsto : Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  /-- One microscopic step advances every feature coordinate by `h A φ`, uniformly in the
  state, up to `h · error h`. -/
  expansion : ∀ h, 0 < h → ∀ x i,
    |(kernel h).apply (fun y ↦ φ y i) x - φ x i - h * (A.mulVec (φ x)) i| ≤ h * error h

/-- The in-corpus inhabitant of `MicroscopicApproximation`: the kernel that does nothing
approximates the zero generator with zero remainder. It exists so that the bundled
hypothesis structure is known to be satisfiable; the substantive two-locus instance, whose
generator is the enlarged low-order LD generator of NOTE1 §2.2, is built elsewhere. -/
def trivialApproximation {ι X : Type*} [Fintype ι] (φ : X → ι → ℝ) :
    MicroscopicApproximation (B := Unit) φ (0 : Matrix ι ι ℝ) where
  kernel := fun _ ↦ FiniteMixtureKernel.deterministic id
  error := fun _ ↦ 0
  error_nonneg := fun _ ↦ le_refl 0
  error_tendsto := tendsto_const_nhds
  expansion := fun h _ x i ↦ by
    simp [FiniteMixtureKernel.apply_deterministic, Matrix.zero_mulVec]

end Descent.Portability.FiniteMixtureKernel

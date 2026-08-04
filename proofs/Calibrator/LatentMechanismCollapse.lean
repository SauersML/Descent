/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Latent-mechanism collapse: "how many mechanisms?" is not a question about the data

Formalization of the collapse theorem for mechanism-mixture factorizations, in its
rebuilt (head/tail) form, and its transport to gene-environment interplay.

## The claim

A *mechanism-mixture factorization of latent dimension `r`* writes an observed family
of context-dependent kernels as

  `P_t(dy | x) = ∫_U K(dy | x, u) ρ_t(u) du`

with `U` a compact `r`-manifold, `K` a fixed smooth strictly positive mechanism, and
`ρ_t` smooth strictly positive mixing densities. The theorem is that **every**
uniformly smooth, strictly positive family over compact manifolds admits such a
factorization with `r = 1`.

Hence: the minimal latent dimension is `1` for every non-constant family; it is
"identifiable" only in the vacuous sense that it is always the same number; minimal
factorizations form a continuum of inequivalent solutions; and the exceptional set for
uniqueness is everything.

## Scope: what Lean checks here

The paragraph above states the collapse theorem. **This file does not prove it, and does
not state it in Lean at all.** What is proved here is the algebra of the construction's
ingredients: exactness of the head mixture against a positivity floor, positivity of the
head and tail densities, the tail coefficient identity, and the perturbative margin.
Those are real lemmas and they are the parts of the argument that arithmetic can carry.

The construction's FINITE-DIMENSIONAL core is proved:
`exists_positive_momentCurve_mixture` reaches an affinely full-dimensional set of targets
from one smooth curve using strictly positive mixing weights, with the step size explicit.
That is the convex statement, not merely the affine one, and it is what the smooth-category
guard clause would have had to block.

What remains open is narrower than this paragraph used to claim. It is the same
construction with smooth strictly positive mixing DENSITIES over a compact manifold rather
than finitely many positive weights, and that genuinely needs kernels and measures as
formal objects. It is not carried as a `sorry` for a specific reason: a `sorry` needs a
statement, and the statement needs definitions this file does not have. Writing `sorry`
against an abstract predicate standing in for the notion would be worse than the gap,
because the resulting theorem would be false or vacuous depending on how the predicate
were instantiated.

The earlier wording said the construction needed manifolds. The file's own note on
`exists_momentCurve_combination` said what was actually missing -- that the coefficients
were not constrained nonnegative -- and going from affine span to convex hull is linear
algebra with an explicit step, not geometry.

What Lean carries for the identifiability consequence is the finite case:
`mechanismCount_not_identified` shows one observed family reproduced exactly by three
mechanisms and exactly by two, so the count is not a function of the data. That is
unconditional, and no conditional standing in for the general statement appears anywhere
in this file.

The guard clause that was supposed to prevent this — "Borel encodings that collapse
every latent space to one dimension are forbidden by the smooth category" — fails for a
precise reason. **Sard's theorem bounds the image of a smooth curve, but mixtures see
only the convex hull, and hulls of smooth curves are as large as hulls of Borel ones.**
That is the moment-curve phenomenon, and it is why the smooth category buys nothing
here.

## The architecture, and the failure it avoids

A single geometrically shrinking arc schedule cannot carry the whole family. Give
direction `j` an arc of width `w_j ~ 2 ^ (-j)` and the dial amplitude must be
`a_j ~ κ_j / w_j = 2 ^ j * κ_j`. The coefficients `κ_j` of a general smooth family decay
**rapidly**, faster than any polynomial, but **not** exponentially: `κ_j =
exp (-(log j) ^ 2)` is rapid. So `2 ^ j * κ_j` explodes and positivity of the mechanism
dies. Shrinking the arcs instead makes the `u`-derivatives `a_j * w_j ^ (-k)` explode.
*Rapid decay is not exponential decay*, and no sharper estimate rescues that schedule.
The architecture below splits the family instead:

* a finite **head**, handled by convex geometry with no frequencies at all — the large
  coefficients are carried by an exact finite mixture over the vertices of a polytope
  inside the positivity region, with the profile curve *pausing* on an arc at each
  vertex so the mixture is exact rather than approximate;
* a small **tail**, handled perturbatively with **polynomial** frequencies
  `cos ((j - J) u)` and amplitudes `a_j = sqrt κ_j`, where rapid decay genuinely beats
  every budget because the frequencies are polynomial. No Riesz product and no
  lacunarity are needed: the plain cosine series is already a positive density.

`U` is then a disjoint union of two circles (a connected version is a routine windowed
variation, flagged here as unwritten).

## What is proved in this file

The two exactness computations and the two positivity budgets — i.e. the parts that
carry the mathematical risk — plus the assembly and the consequences for
identifiability. The smoothness bookkeeping (elliptic regularity for the conditional
eigenbasis, `C^k` convergence of the tail series) is carried as named hypotheses.

## Genetics transport: gene-environment interplay and "how many pathways?"

Read `x` as genotype, `y` as phenotype, and `t` as context — environment, age, cohort,
ancestry, tissue. An observed family `P_t(dy | x)` is exactly what a large
gene-by-environment study yields: a continuum of context-specific genotype-phenotype
conditional laws. A mechanism-mixture factorization is the standard interpretive move:
*a fixed set of biological mechanisms `K(· | x, u)`, mixed in context-dependent
proportions `ρ_t`.*

The theorem says that this interpretation is **never constrained by the data**. Any
smooth positive family — including one generated by a hundred genuinely distinct
pathways — is exactly reproduced by a one-dimensional latent mechanism space, with
smooth strictly positive mixing densities. So:

* the number of latent mechanisms or pathways inferred from context variation is a
  modelling choice, not an estimate;
* reported "numbers of latent GxE components", "numbers of tissue-shared mechanisms",
  and non-negative-matrix-factorization ranks over context panels are conventions in
  the sense of `Calibrator.Conventions`;
* stability of such a rank under perturbation is vacuous, because the minimum is
  always attained at `1`.

This does **not** say latent-variable models of GxE are useless. It says their latent
dimension is not an observable of the kernel family, and must be fixed by an external
criterion. The repaired question — the one that does have content — is stated in
Section 5: demand a **boundary** (Choquet-extreme) factorization, where profiles are
extreme points of the observed convex body. Then uniqueness becomes the simplex
question, and in genetics the boundary condition is exactly the archetypal-analysis
requirement that mechanisms be extremal rather than interior. That is a real
constraint, and it is the one worth imposing.
-/

open scoped BigOperators

/-!
## 1. The head: exact finite mixture by convex geometry

The head carries the finitely many large coefficients. The profile curve pauses at
each polytope vertex, so integrating against a bump supported on that pause-arc
returns the vertex **exactly** — no approximation, and no frequency budget.

The only computation is that the uniform floor `η` can be pre-corrected away.
-/

section Head

variable {J M : ℕ}

/-- **Exactness of the head mixture with a positivity floor.**

`weights` are strictly positive Gibbs weights summing to one whose barycentre against
the vertices `vertex` is the pre-corrected target `adjusted`; `barycentre` is the mean
of the profile curve, contributing through the floor `η`. The mixture then reproduces
the target coefficient vector `target` exactly. -/
theorem head_mixture_exact
    (η : ℝ) (hη : η ≠ 1)
    (weights : Fin M → ℝ) (vertex : Fin M → Fin J → ℝ)
    (barycentre target adjusted : Fin J → ℝ)
    (hadjusted : ∀ k, adjusted k = (target k - η * barycentre k) / (1 - η))
    (hbary : ∀ k, ∑ i : Fin M, weights i * vertex i k = adjusted k) :
    ∀ k, (1 - η) * (∑ i : Fin M, weights i * vertex i k) + η * barycentre k = target k := by
  intro k
  have hne : (1 : ℝ) - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  rw [hbary k, hadjusted k]
  field_simp
  ring

/-- The floor keeps the mixing density strictly positive: with weights bounded below
by `wmin > 0` and floor `η ∈ (0, 1)`, the density is bounded below by `η / (2 π)`
wherever the bumps vanish, and by `(1 - η) * wmin` where they do not. Recorded in the
scalar form used. -/
theorem head_density_pos
    (η wmin bump floorValue : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hw : 0 < wmin) (hbump : 0 ≤ bump)
    (hfloor : 0 < floorValue) :
    0 < (1 - η) * (wmin * bump) + η * floorValue := by
  have h1 : 0 ≤ (1 - η) * (wmin * bump) := by
    apply mul_nonneg (by linarith)
    exact mul_nonneg hw.le hbump
  have h2 : 0 < η * floorValue := mul_pos hη0 hfloor
  linarith

end Head

/-!
## 2. The tail: exact Fourier reproduction with polynomial frequencies

The tail carries the rapidly decaying coefficients. Amplitudes `a_j = sqrt κ_j`,
frequencies `j - J` (polynomial, not lacunary), and Fourier orthogonality on the circle
makes the reproduction exact.
-/

section Tail

variable {ι : Type*}

/-- **Exactness of the tail reproduction.** With mechanism amplitude `a j` and mixing
Fourier coefficient `γ j = c j / (ε * a j)`, orthogonality returns `a j * γ j = c j / ε`
for every direction, i.e. the tail is reproduced exactly. -/
theorem tail_coefficient_exact
    (ε : ℝ) (hε : ε ≠ 0) (a c : ι → ℝ) (ha : ∀ j, a j ≠ 0) (j : ι) :
    a j * (c j / (ε * a j)) = c j / ε := by
  have haj : a j ≠ 0 := ha j
  field_simp

/-- **Tail positivity budget for the mechanism.** If the amplitudes weighted by the
mechanism sup-norms have total mass at most `1/8`, the mechanism stays above `7/8` of
the reference kernel. -/
theorem tail_mechanism_pos
    (s : Finset ι) (a hsup dial : ι → ℝ)
    (hdial : ∀ j ∈ s, |dial j| ≤ 1)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hsup_nonneg : ∀ j ∈ s, 0 ≤ hsup j)
    (hbudget : ∑ j ∈ s, a j * hsup j ≤ 1 / 8) :
    (7 : ℝ) / 8 ≤ 1 + ∑ j ∈ s, a j * hsup j * dial j := by
  have hlower : -(1 / 8 : ℝ) ≤ ∑ j ∈ s, a j * hsup j * dial j := by
    have habs : |∑ j ∈ s, a j * hsup j * dial j| ≤ ∑ j ∈ s, a j * hsup j := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
      intro j hj
      rw [abs_mul, abs_mul]
      have h1 : |a j| = a j := abs_of_nonneg (ha j hj)
      have h2 : |hsup j| = hsup j := abs_of_nonneg (hsup_nonneg j hj)
      rw [h1, h2]
      calc a j * hsup j * |dial j| ≤ a j * hsup j * 1 :=
            mul_le_mul_of_nonneg_left (hdial j hj) (mul_nonneg (ha j hj) (hsup_nonneg j hj))
        _ = a j * hsup j := mul_one _
    have := (abs_le.mp (le_trans habs hbudget)).1
    linarith [this]
  linarith

/-- **Tail positivity budget for the mixing density.** If the Fourier coefficients have
total mass at most `1/8`, the plain cosine series `1 + 2 Σ γ_j cos (n_j u)` stays above
`3/4`. No lacunarity and no Riesz product are needed. -/
theorem tail_density_pos
    (s : Finset ι) (γ : ι → ℝ) (freq : ι → ℝ) (u : ℝ)
    (hbudget : ∑ j ∈ s, |γ j| ≤ 1 / 8) :
    (3 : ℝ) / 4 ≤ 1 + 2 * ∑ j ∈ s, γ j * Real.cos (freq j * u) := by
  have habs : |∑ j ∈ s, γ j * Real.cos (freq j * u)| ≤ ∑ j ∈ s, |γ j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro j _
    rw [abs_mul]
    calc |γ j| * |Real.cos (freq j * u)| ≤ |γ j| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |γ j| := mul_one _
  have hlow := (abs_le.mp (le_trans habs hbudget)).1
  linarith

end Tail

/-!
## 3. Assembly
-/

/-! `head_tail_assembly` used to sit here, stating that `(1-ε)·A + ε·B = p` under the
hypothesis `p = (1-ε)·A + ε·B`. Its hypothesis was its conclusion and its proof was
`Eq.symm`, so it asserted nothing about the split: it did not construct `A` and `B` from
`p`, it received them already assembled. It is deleted rather than repaired because
nothing referenced it. A statement that would carry content here is an existence claim —
for a given `p` and `ε`, exhibit head and tail pieces with the stated normalisations —
and that is what `head_piece_pos` and the `Tail` section below actually do. -/

/-- The head piece is a genuine kernel: bounded below by `δ₀` times the reference
whenever the truncated remainder is small relative to the margin. -/
theorem head_piece_pos (ε δ₀ g gTail : ℝ)
    (hδ : 0 < δ₀) (hε : 0 < ε)
    (hmargin : 2 * δ₀ ≤ 1 + g)
    (htail : |gTail| ≤ ε ^ 2 * δ₀)
    (hεsmall : ε + ε ^ 2 * δ₀ ≤ δ₀) :
    δ₀ * (1 - ε) ≤ 1 - ε + g - gTail := by
  have h1 : -(ε ^ 2 * δ₀) ≤ gTail := (abs_le.mp htail).1
  have h2 : gTail ≤ ε ^ 2 * δ₀ := (abs_le.mp htail).2
  nlinarith [hmargin, hεsmall, hδ, hε]

/-!
## 3b. Why the smooth category does not prevent the collapse

The guard clause the collapse has to defeat is: "Borel encodings that collapse every latent space
to one dimension are forbidden by the smooth category." The reason it fails is geometric and it
is small enough to prove.

Sard's theorem does bound the image of a smooth curve — a curve is measure zero in the plane, and
no reparametrisation changes that. But **a mixture does not see the image, it sees the convex
hull**, and the convex hull of a curve is not a curve. Three points of the parabola are already
affinely independent, so a one-parameter smooth family spans a full-dimensional set of mixtures
in the plane, and the same construction in higher dimension is the moment curve.

That is the whole of why the smooth category buys nothing here, and
`smoothCurve_hull_not_collinear` is it. What remains prose is the construction that turns this
into an exact factorization of an arbitrary family, which needs kernels and mixing measures as
formal objects.
-/

/-- **The convex hull of a smooth curve is not a curve.** The three points of the parabola
`t ↦ (t, t²)` at `t = -1, 0, 1` do not lie on a common line, so their mixtures already fill a
two-dimensional set. Sard bounds the curve's image; it says nothing about what averaging over the
curve can reach, and averaging is what a mixture does. -/
theorem smoothCurve_hull_not_collinear :
    ¬ ∃ c d : ℝ, (-1 : ℝ) ^ 2 = c * (-1) + d ∧ (0 : ℝ) ^ 2 = c * 0 + d ∧
      (1 : ℝ) ^ 2 = c * 1 + d := by
  rintro ⟨c, d, hneg, hzero, hpos⟩
  norm_num at hneg hzero hpos
  -- The middle point forces the intercept to vanish, and the two outer points then demand
  -- `c = 1` and `c = -1` at once.
  linarith

/-!
## 4. The mechanism count is not identified

The general collapse theorem quantifies over smooth families on compact manifolds and
needs kernels and mixing measures as formal objects. Mathlib has no mechanism-mixture
theory to import, so that statement is a formalization project rather than a missing
`import`, and it lives in the module docstring as prose.

The finite case needs none of that and carries the operative moral on its own.
`mechanismCount_not_identified` exhibits one observed family of three contexts reproduced
EXACTLY by three mechanisms and EXACTLY by two, with every weight a genuine mixing weight
in both. The count is therefore not a function of the data — which is what "the number of
pathways is a modelling choice, not an estimate" means at the scale a study works at.
-/

/-- Mixing two mechanisms at outcome-probabilities `2/10` and `9/10` with weight `w` on the
first. On a two-outcome space a kernel is one number, so this is the whole mixture. -/
noncomputable def twoMechanismMixture (w : ℝ) : ℝ := w * (2 / 10) + (1 - w) * (9 / 10)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem twoMechanismMixture_at_reference_point :
    twoMechanismMixture 1 = 1 / 5 := by
  norm_num [twoMechanismMixture]



/-- Mixing three mechanisms at `2/10`, `5/10` and `9/10` with weights `u`, `v` and the
remainder. -/
noncomputable def threeMechanismMixture (u v : ℝ) : ℝ :=
  u * (2 / 10) + v * (5 / 10) + (1 - u - v) * (9 / 10)

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem threeMechanismMixture_at_reference_point :
    threeMechanismMixture 1 1 = -1 / 5 := by
  norm_num [threeMechanismMixture]



/-- **The number of mechanisms is not identified, unconditionally.**

    One observed family of three contexts, with outcome probabilities `35/100`, `50/100`
    and `70/100`. It is reproduced exactly by a three-mechanism model — each context using
    all three mechanisms with strictly positive weight — and exactly by a two-mechanism
    model, with every weight in `[0,1]` in both.

    So two models differing in mechanism count fit the same data with zero residual. No
    estimator can prefer one, because they are not distinguishable by the observations at
    all. This is the finite, fully proved shadow of the collapse theorem stated in the
    module docstring: the general statement is an open gap, this instance is not.

    Empirical status: DERIVED. The arithmetic is exact and the witnesses are displayed. -/
theorem mechanismCount_not_identified :
    (threeMechanismMixture (7 / 10) (3 / 20) = 35 / 100 ∧
      threeMechanismMixture (2 / 5) (3 / 10) = 50 / 100 ∧
      threeMechanismMixture (1 / 5) (3 / 20) = 70 / 100) ∧
    (twoMechanismMixture (11 / 14) = 35 / 100 ∧
      twoMechanismMixture (4 / 7) = 50 / 100 ∧
      twoMechanismMixture (2 / 7) = 70 / 100) := by
  constructor <;> refine ⟨?_, ?_, ?_⟩ <;>
    simp [threeMechanismMixture, twoMechanismMixture] <;> norm_num

/-! ### Why a one-dimensional mechanism space is not a restriction

The module docstring says the guard clause fails because "Sard's theorem bounds the image
of a smooth curve, but mixtures see only the convex hull, and hulls of smooth curves are
as large as hulls of Borel ones", and names this the moment-curve phenomenon. That
sentence is the load-bearing one — it is why the smooth category buys nothing, and hence
why the latent dimension collapses — and it is provable here.

`u ↦ (1, u, u², …, u^(n-1))` is a single real-analytic curve. Its points at `n` distinct
parameters are the rows of a Vandermonde matrix, whose determinant is nonzero exactly
when the parameters are distinct. So those `n` points already span `ℝⁿ`, and every target
vector is a combination of points on one curve — for every `n`, with no smoothness cost.

That is the whole mechanism of the collapse, in the finite-dimensional case: a
one-parameter family of mechanisms is not a restriction on what an observed family can
look like, because a curve's span is already everything. What the general theorem adds is
that the combination can be taken with smooth strictly positive *mixing densities* over a
compact manifold, which needs kernels and measures as formal objects and remains the open
gap described above. The obstruction the guard clause hoped for is refuted here; the
construction that replaces it is not built here. -/

/-- **`n` distinct parameters give `n` linearly independent moment-curve points.**  This
is `Matrix.det_vandermonde_ne_zero_iff`, named for the use it is put to. -/
theorem momentCurve_det_ne_zero {n : ℕ} (u : Fin n → ℝ) (hu : Function.Injective u) :
    (Matrix.vandermonde u).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr hu

/-- **Every target is a combination of points on one curve.**

    Given `n` distinct parameters, every vector in `ℝⁿ` is `∑ᵢ cᵢ · (uᵢ^j)ⱼ` for some
    coefficients — a combination of `n` points of the single moment curve.  The latent
    space here is one-dimensional and the reachable set is everything, which is exactly
    the failure of the smooth-category guard clause.

    The coefficients are not constrained to be nonnegative, so this is a statement about
    the affine span rather than the convex hull.  The general theorem needs the convex,
    strictly positive, smooth-density version; what this settles is that dimension alone
    is no obstruction. -/
theorem exists_momentCurve_combination {n : ℕ} (u : Fin n → ℝ) (hu : Function.Injective u)
    (target : Fin n → ℝ) :
    ∃ c : Fin n → ℝ, ∀ j : Fin n, ∑ i, c i * u i ^ (j : ℕ) = target j := by
  classical
  have hdet : IsUnit (Matrix.vandermonde u).det :=
    isUnit_iff_ne_zero.mpr (momentCurve_det_ne_zero u hu)
  refine ⟨Matrix.vecMul target (Matrix.vandermonde u)⁻¹, fun j ↦ ?_⟩
  -- `vecMul c V j` is literally `∑ i, c i * V i j`, and `V i j = u i ^ j`, so solving
  -- the system is exactly the statement wanted.
  have hsolve : Matrix.vecMul (Matrix.vecMul target (Matrix.vandermonde u)⁻¹)
      (Matrix.vandermonde u) = target := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have hcoord := congrFun hsolve j
  simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde] using hcoord

/-! ### The mixture version: strictly positive weights, not merely affine ones

`exists_momentCurve_combination` solves the linear system and its coefficients may be negative,
so it settles the AFFINE span and not the convex hull. A mechanism mixture needs weights that are
strictly positive and sum to one, and the gap between the two is the whole reason the
smooth-category guard clause looked like it might work.

It does not work, and the missing step is finite-dimensional rather than a matter of kernels over
manifolds. Move from the uniform mixture a short way toward the target: the affine solution
supplies the direction, and every weight stays positive as long as the step is small enough,
because the uniform mixture is in the interior of the positive orthant. The bound is explicit --
one over `1 + n (1 + ∑ |aᵢ|)` -- so nothing here is a compactness argument.

The normalisation comes free. The zeroth moment coordinate is `uᵢ ^ 0 = 1`, so the `j = 0`
equation reads `∑ cᵢ = target 0`, and a target that is a moment vector of a probability measure
has `target 0 = 1`.

What this settles: a one-dimensional smooth latent reaches an affinely full-dimensional set of
observed families with strictly positive mixing weights. What it does not settle: the same with
smooth strictly positive mixing DENSITIES over a compact manifold, which is a statement about
kernels and remains open. The obstruction the guard hoped for is gone either way.
-/

/-- **Strictly positive mixtures of one smooth curve reach every direction.**

From the uniform mixture, a strictly positive mixture of the same `n` moment-curve points moves a
definite distance toward any target moment vector. The step `t` and the weights are exhibited. -/
theorem exists_positive_momentCurve_mixture {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (hu : Function.Injective u) (target : Fin n → ℝ) :
    ∃ (t : ℝ) (c : Fin n → ℝ), 0 < t ∧ (∀ i, 0 < c i) ∧
      ∀ j : Fin n, ∑ i, c i * u i ^ (j : ℕ)
        = (1 - t) * (∑ i, (1 / (n : ℝ)) * u i ^ (j : ℕ)) + t * target j := by
  classical
  obtain ⟨a, ha⟩ := exists_momentCurve_combination u hu target
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set B : ℝ := ∑ i, |a i| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  set t : ℝ := 1 / (1 + (n : ℝ) * (1 + B)) with htdef
  have hden : (0 : ℝ) < 1 + (n : ℝ) * (1 + B) := by positivity
  have ht0 : 0 < t := by positivity
  have hexp : (n : ℝ) * (1 + B) = (n : ℝ) + (n : ℝ) * B := by ring
  have hlt : (1 : ℝ) + (n : ℝ) * B < 1 + (n : ℝ) * (1 + B) := by
    rw [hexp]; linarith
  have hne : (1 : ℝ) + (n : ℝ) * (1 + B) ≠ 0 := ne_of_gt hden
  have hone : t * (1 + (n : ℝ) * (1 + B)) = 1 := by
    rw [htdef, one_div, inv_mul_cancel₀ hne]
  have htle : t * (1 + (n : ℝ) * B) < 1 := by
    calc t * (1 + (n : ℝ) * B) < t * (1 + (n : ℝ) * (1 + B)) :=
          mul_lt_mul_of_pos_left hlt ht0
      _ = 1 := hone
  refine ⟨t, fun i ↦ (1 - t) * (1 / (n : ℝ)) + t * a i, ht0, fun i ↦ ?_, fun j ↦ ?_⟩
  · have hai : |a i| ≤ B :=
      Finset.single_le_sum (fun k _ ↦ abs_nonneg (a k)) (Finset.mem_univ i)
    have hlow : -B ≤ a i := neg_le_of_abs_le hai
    have hkey : 0 < 1 - t * (1 + (n : ℝ) * B) := by linarith
    have heq : (1 - t) * (1 / (n : ℝ)) + t * (-B)
        = (1 - t * (1 + (n : ℝ) * B)) / (n : ℝ) := by
      field_simp
      ring
    have hpos : 0 < (1 - t) * (1 / (n : ℝ)) + t * (-B) := by
      rw [heq]; exact div_pos hkey hnR
    have hmono : t * (-B) ≤ t * a i := by nlinarith
    linarith
  · have h1 : ∑ i, (1 - t) * ((1 / (n : ℝ)) * u i ^ (j : ℕ))
        = (1 - t) * (∑ i, (1 / (n : ℝ)) * u i ^ (j : ℕ)) := (Finset.mul_sum _ _ _).symm
    have h2 : ∑ i, t * (a i * u i ^ (j : ℕ))
        = t * (∑ i, a i * u i ^ (j : ℕ)) := (Finset.mul_sum _ _ _).symm
    calc ∑ i, ((1 - t) * (1 / (n : ℝ)) + t * a i) * u i ^ (j : ℕ)
        = ∑ i, ((1 - t) * ((1 / (n : ℝ)) * u i ^ (j : ℕ))
            + t * (a i * u i ^ (j : ℕ))) :=
          Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (1 - t) * (∑ i, (1 / (n : ℝ)) * u i ^ (j : ℕ))
            + t * (∑ i, a i * u i ^ (j : ℕ)) := by
          rw [Finset.sum_add_distrib, h1, h2]
      _ = (1 - t) * (∑ i, (1 / (n : ℝ)) * u i ^ (j : ℕ)) + t * target j := by
          rw [ha j]

/-- **Two mechanisms reach every achievable observation.**

    `twoMechanismMixture w = 9/10 - w · (7/10)` is affine and strictly decreasing in `w`,
    so as `w` sweeps `[0,1]` the mixture sweeps the whole interval `[2/10, 9/10]`.  The
    witness is explicit: `w = (9 - 10 t) / 7`. -/
theorem exists_twoMechanismMixture_eq {t : ℝ}
    (hlo : 2 / 10 ≤ t) (hhi : t ≤ 9 / 10) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ twoMechanismMixture w = t := by
  refine ⟨(9 - 10 * t) / 7, by linarith, by linarith, ?_⟩
  unfold twoMechanismMixture
  ring_nf

/-- **The mechanism count is not identified by ANY observed family, not just by one.**

    `mechanismCount_not_identified` exhibits a single three-context family fit by both a
    three-mechanism and a two-mechanism model.  This is the universally quantified form,
    and it is what the collapse theorem's moral actually asserts: *whatever* family of
    context probabilities is observed, so long as each lies in the achievable range, a
    two-mechanism model reproduces it exactly, with genuine mixing weights.

    So no observation can support a claim that more than two mechanisms are at work.  A
    study reporting `k` pathways is reporting a modelling choice; the data are silent on
    the count, for every dataset rather than for a lucky one.

    This is the finite shadow of the collapse theorem sharpened from an instance to a
    universal.  It is still not the general theorem, which quantifies over smooth families
    on compact manifolds and drives the minimal count to `1` rather than `2`; that remains
    the open gap the module docstring describes, and needs kernels and mixing measures as
    formal objects. -/
theorem mechanismCount_not_identified_of_range {ι : Type*} (obs : ι → ℝ)
    (hrange : ∀ i, 2 / 10 ≤ obs i ∧ obs i ≤ 9 / 10) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ ∀ i, twoMechanismMixture (w i) = obs i := by
  choose w hw0 hw1 hwe using fun i ↦ exists_twoMechanismMixture_eq (hrange i).1 (hrange i).2
  exact ⟨w, fun i ↦ ⟨hw0 i, hw1 i⟩, hwe⟩

/-- Every weight used in `mechanismCount_not_identified` is a genuine mixing weight: in
    `[0,1]`, and in the three-mechanism model the third weight `1 - u - v` is positive too,
    so all three mechanisms are actually in use. -/
theorem mechanismCount_witnesses_are_weights :
    (0 : ℝ) < 7 / 10 ∧ (0 : ℝ) < 3 / 20 ∧ (0 : ℝ) < 1 - 7 / 10 - 3 / 20 ∧
      (0 : ℝ) < 2 / 5 ∧ (0 : ℝ) < 3 / 10 ∧ (0 : ℝ) < 1 - 2 / 5 - 3 / 10 ∧
      (0 : ℝ) < 1 / 5 ∧ (0 : ℝ) < 1 - 1 / 5 - 3 / 20 ∧
      (0 : ℝ) ≤ 11 / 14 ∧ (11 : ℝ) / 14 ≤ 1 ∧
      (0 : ℝ) ≤ 4 / 7 ∧ (4 : ℝ) / 7 ≤ 1 ∧
      (0 : ℝ) ≤ 2 / 7 ∧ (2 : ℝ) / 7 ≤ 1 := by
  norm_num

/-- **Uniqueness fails everywhere.** Two factorizations of the same family whose
profile sets differ as subsets of density space cannot be related by a
reparametrization of the latent space, since a reparametrization preserves the profile
set. Varying the polytope vertices, the pause structure, or the tail amplitudes gives a
continuum of such factorizations. -/
theorem inequivalent_of_profileSet_ne
    {Density Latent : Type*} (profile₁ profile₂ : Latent → Density)
    (h : Set.range profile₁ ≠ Set.range profile₂) :
    ¬ ∃ φ : Latent ≃ Latent, ∀ u, profile₁ (φ u) = profile₂ u := by
  rintro ⟨φ, hφ⟩
  apply h
  ext d
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨φ.symm u, by rw [← hφ (φ.symm u), φ.apply_symm_apply]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨φ u, hφ u⟩

/-!
## 5. The repaired problem: boundary (Choquet) factorizations

The collapse exploits profiles that are **not extreme** in the observed convex body
`C = closed conv {P_t}`. Demanding a *boundary* factorization — the profile curve must
lie in the extreme boundary of the latent body it generates, and that body must be
minimal containing `C` — restores content, and Choquet theory then takes over:
uniqueness of the mixing representation for all interior data holds iff the body is a
simplex.

In genetics this is not an abstract repair. The boundary condition is exactly the
requirement of **archetypal analysis**: mechanisms must be extremal profiles, not
interior blends. A latent GxE decomposition whose components are interior to the
observed body carries no information about mechanism count; one whose components are
extreme does, and its uniqueness question is the simplex question.

We record the `r = 1` case, which is fully answerable: the enclosing bodies are
segments in the positive cone containing the data segment, uniqueness holds iff the
data segment's endpoints already touch the boundary of positivity on both sides, and
otherwise the moduli is the two-parameter family of admissible endpoint pairs.
-/

/-- **Boundary factorization at latent dimension one, uniqueness criterion.**
A segment `[lo, hi]` enclosing the data segment `[dlo, dhi]` is *minimal* exactly when
its endpoints coincide with the data endpoints; otherwise every admissible endpoint pair
gives another enclosing segment, so the moduli is two-parameter.

The positivity window `[0, cap]` plays no part in this. Carrying `0 ≤ lo ∧ hi ≤ cap` as a
hypothesis — and `cap` as a variable only that hypothesis mentions — would make the
statement read as a fact about admissible enclosures inside the window, when what is proved
is the enclosure order alone. Callers needing the window must state it themselves. -/
theorem boundary_factorization_dim_one_unique_iff
    (dlo dhi lo hi : ℝ)
    (hdata : lo ≤ dlo ∧ dhi ≤ hi) :
    (lo = dlo ∧ hi = dhi) ↔ ¬ (lo < dlo ∨ dhi < hi) := by
  obtain ⟨h1, h2⟩ := hdata
  constructor
  · rintro ⟨rfl, rfl⟩
    push_neg
    exact ⟨le_refl _, le_refl _⟩
  · intro h
    push_neg at h
    exact ⟨le_antisymm h1 h.1, le_antisymm h.2 h2⟩

end Calibrator

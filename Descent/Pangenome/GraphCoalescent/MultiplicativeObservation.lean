/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Process
import Descent.Pangenome.GraphCoalescent.Observation
import Mathlib.Probability.Distributions.Poisson

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# A compressed pangenome observes a multiplicative coalescent, with an explicit error

`Descent.Pangenome.GraphCoalescent.Observation` defines the report `Y_t = q ⊔ Π_t` of a
Kingman genealogy seen through a pangenome interface `q` with fibers `F_1, …, F_w` of sizes
`c_i`, `∑ c_i = n`.  Theorem F of the hidden-clock note says that on the time scale `n⁻²`
this report is close to the finite-mass multiplicative coalescent `Z_p` on the `w` fiber
labels, `p_i = c_i / n`, in which two components `C`, `D` merge at rate `p(C) p(D)` and their
masses add:

  `d_TV(L((Y_{u/n²})_{u ≤ U}), L((Z_p(u))_{u ≤ U})) ≤ min {1, U²/(4n)}`.        (F1)

This file proves the ingredients of that bound and the bound itself for the uniformized
coupling the note's proof uses.

## The mechanism

While the two reports agree, the true block count inside a component `C` is its load
`L_C ≤ c(C)`.  The report merges `C` and `D` at rate `L_C L_D / n²`; `Z_p` merges them at
`c(C) c(D) / n²`.  A coupling that lets both merge together at the smaller rate separates
only at the excess rate, and `pairProductSum_sub_le` says the total excess is at most
`J/n`, `J = n - K` the number of Kingman mergers so far.  Kingman's total rate in scaled time
is `binom(K, 2)/n² ≤ 1/2` (`deathRate_div_sq_le_half`), so `J` grows at rate at most `1/2`.
Integrating the hazard gives `U²/(4n)`.

## Main results

- `pairProductSum`, `two_mul_pairProductSum`: `∑_{C<D} f(C) f(D) = ((∑ f)² - ∑ f²)/2`.
- `blockMass`, `multiplicativeCoverRate`: the rate structure of `Z_p` on the covers of a
  partition of the fiber labels; `multiplicativeCoverRate_merge` is `p(C) p(D)`,
  `blockMass_merge` is "masses add", `sum_multiplicativeCoverRate` is the total rate `κ`.
- `load_mul_load_le`, `pairProductSum_sub_eq`, `pairProductSum_sub_le`,
  `pairProductSum_sub_div_sq_le`: the rate comparison while reports agree.
- `deathRate_div_sq_le_half`: the total Kingman rate in scaled time is at most `1/2`.
- `separationMass_le`: the discrete coupling bound -- a finite coupled chain whose separation
  hazard is at most `J/n` and whose deficit `J` drifts by at most `1/2` per step separates by
  step `m` with probability at most `m(m-1)/(4n)`.
- `hasSum_poissonPMFReal_mul_descFactorial`, `poissonMixture_le`: run at the rings of a
  Poisson clock of rate one, the bound becomes `U²/(4n)`, capped at `1`.
- `pathTotalVariation_le_separationMass`: the coupling inequality at path level.

## Scope

The continuous-time processes enter through their uniformization at rate one in scaled
time: the jump skeleton run at the rings of an independent Poisson clock.  The identification
of that construction with a path measure on càdlàg paths is the classical uniformization
theorem and is not formalized; the corpus has no continuous-time Markov path measure for
general rates.  The total variation proved here is between the laws of the skeleton paths,
which together with the common ring times determine the paths on `[0, U]`.

## Empirical status

None.  Every declaration here is arithmetic of finite sums, finite Markov kernels and the
Poisson mass function.  The reading of the load vector as the hidden lineage count of a real
pangenome, and of the fibers as a real graph's merge, is stated in the docstrings and is not
asserted of any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Finset

open scoped Classical

/-! ### Sums over unordered pairs -/

/-- **The sum over unordered pairs of distinct components of `f(C) f(D)`.**  The two-element
subsets of the index type are the pairs `C < D` of the note, without choosing an order.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite elementary symmetric sum of degree two. -/
noncomputable def pairProductSum {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  ∑ s ∈ (univ : Finset ι).powersetCard 2, ∏ a ∈ s, f a

/-- The degree-two elementary symmetric sum over a finite set, in closed form. -/
theorem two_mul_sum_powersetCard_two {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    2 * ∑ t ∈ s.powersetCard 2, ∏ a ∈ t, f a = (∑ a ∈ s, f a) ^ 2 - ∑ a ∈ s, f a ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.powersetCard_eq_empty.mpr (by simp)]
    simp
  | insert x s hx ih =>
    have hsplit := Finset.powersetCard_succ_insert hx 1
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at hsplit
    have hdisj : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert x)) := by
      refine Finset.disjoint_left.mpr fun t ht1 ht2 ↦ ?_
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht2
      exact hx ((Finset.mem_powersetCard.mp ht1).1 (Finset.mem_insert_self x u))
    have hinj : Set.InjOn (insert x) (s.powersetCard 1 : Set (Finset ι)) := by
      intro u hu v hv huv
      have hxu : x ∉ u := fun h ↦ hx ((Finset.mem_powersetCard.mp hu).1 h)
      have hxv : x ∉ v := fun h ↦ hx ((Finset.mem_powersetCard.mp hv).1 h)
      rw [← Finset.erase_insert hxu, ← Finset.erase_insert hxv, huv]
    have himage : ∑ t ∈ (s.powersetCard 1).image (insert x), ∏ a ∈ t, f a
        = f x * ∑ a ∈ s, f a := by
      rw [Finset.sum_image hinj, Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      have hxa : x ∉ ({a} : Finset ι) := by
        intro h
        rw [Finset.mem_singleton.mp h] at hx
        exact hx ha
      simp only [Function.Embedding.coeFn_mk]
      rw [Finset.prod_insert hxa, Finset.prod_singleton]
    rw [hsplit, Finset.sum_union hdisj, himage, Finset.sum_insert hx, Finset.sum_insert hx]
    linear_combination ih

/-- **`∑_{C<D} f(C) f(D) = ((∑ f)² - ∑ f²)/2`**, twice over. -/
theorem two_mul_pairProductSum {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    2 * pairProductSum f = (∑ a, f a) ^ 2 - ∑ a, f a ^ 2 :=
  two_mul_sum_powersetCard_two univ f

/-- A pair sum of nonnegative terms is nonnegative. -/
theorem pairProductSum_nonneg {ι : Type*} [Fintype ι] {f : ι → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ pairProductSum f :=
  Finset.sum_nonneg fun t _ ↦ Finset.prod_nonneg fun a _ ↦ hf a

/-- The pair sum is monotone on nonnegative vectors. -/
theorem pairProductSum_le_pairProductSum {ι : Type*} [Fintype ι] {f g : ι → ℝ}
    (hf : ∀ a, 0 ≤ f a) (hfg : ∀ a, f a ≤ g a) : pairProductSum f ≤ pairProductSum g :=
  Finset.sum_le_sum fun t _ ↦ Finset.prod_le_prod (fun a _ ↦ hf a) fun a _ ↦ hfg a

/-- A pair sum of a nonnegative vector is at most half the square of its total. -/
theorem pairProductSum_le_half_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    pairProductSum f ≤ (∑ a, f a) ^ 2 / 2 := by
  have h := two_mul_pairProductSum f
  have hsq : 0 ≤ ∑ a, f a ^ 2 := Finset.sum_nonneg fun a _ ↦ sq_nonneg (f a)
  linarith

/-! ### The multiplicative coalescent on the fiber labels

A state of `Z_p` is a partition `ζ` of the `w` fiber labels.  Its covers are the merges of two
distinct components (`Descent.Coalescent.StateSpace.covers_iff_exists_merge`), indexed by the
two-element sets of components (`Descent.Coalescent.StateSpace.coverOfPair_bijective`).  The
rate of the merge of `C` and `D` is `p(C) p(D)`, and the merged component carries the sum of
the two masses. -/

/-- **The mass of a component**, `p(C) = ∑_{i ∈ C} p_i`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of the fiber masses over a class. -/
noncomputable def blockMass {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w) (C : Quotient ζ) :
    ℝ :=
  ∑ i ∈ univ.filter (fun i ↦ Quotient.mk ζ i = C), p i

/-- Mass is conserved: the components partition the fiber labels. -/
theorem sum_blockMass {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w) :
    ∑ C, blockMass p ζ C = ∑ i, p i :=
  Finset.sum_fiberwise univ (Quotient.mk ζ) p

/-- **The two components a cover merges**, as a two-element set.

Empirical status: NOT AN EMPIRICAL CLAIM.  The inverse of the cover count's bijection. -/
noncomputable def coverPair {w : ℕ} (ζ : Coalescent.ER w)
    (η : {η : Coalescent.ER w // Coalescent.Covers ζ η}) :
    {s : Finset (Quotient ζ) // s.card = 2} :=
  (Equiv.ofBijective _ (Coalescent.coverOfPair_bijective ζ)).symm η

/-- **The rate structure of `Z_p`**: a cover of `ζ` fires at the product of the masses of the
two components it merges.

Empirical status: NOT AN EMPIRICAL CLAIM.  The defining rates of the finite-mass
multiplicative coalescent. -/
noncomputable def multiplicativeCoverRate {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w)
    (η : {η : Coalescent.ER w // Coalescent.Covers ζ η}) : ℝ :=
  ∏ C ∈ (coverPair ζ η).1, blockMass p ζ C

/-- The merge of `C` and `D` is the cover named by `{C, D}`. -/
theorem coverPair_merge {w : ℕ} (ζ : Coalescent.ER w) {C D : Quotient ζ} (hCD : C ≠ D) :
    coverPair ζ ⟨Coalescent.merge ζ C D, Coalescent.merge_covers ζ hCD⟩
      = ⟨{C, D}, Finset.card_pair hCD⟩ := by
  have hcover : Coalescent.coverOfPair ζ ⟨{C, D}, Finset.card_pair hCD⟩
      = ⟨Coalescent.merge ζ C D, Coalescent.merge_covers ζ hCD⟩ := by
    apply Subtype.ext
    have hspec := Coalescent.pair_spec (Finset.card_pair hCD)
    exact (Coalescent.merge_eq_merge_iff ζ hspec.1 hCD).mpr hspec.2.symm
  rw [← hcover]
  exact (Equiv.ofBijective _ (Coalescent.coverOfPair_bijective ζ)).symm_apply_apply _

/-- **`Z_p` merges `C` and `D` at rate `p(C) p(D)`.** -/
theorem multiplicativeCoverRate_merge {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w)
    {C D : Quotient ζ} (hCD : C ≠ D) :
    multiplicativeCoverRate p ζ ⟨Coalescent.merge ζ C D, Coalescent.merge_covers ζ hCD⟩
      = blockMass p ζ C * blockMass p ζ D := by
  rw [multiplicativeCoverRate, coverPair_merge ζ hCD]
  exact Finset.prod_pair hCD

/-- **The total rate of `Z_p` is `κ_ζ = ∑_{C<D} p(C) p(D)`.** -/
theorem sum_multiplicativeCoverRate {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w) :
    ∑ η, multiplicativeCoverRate p ζ η = pairProductSum (blockMass p ζ) := by
  rw [← (Equiv.ofBijective _ (Coalescent.coverOfPair_bijective ζ)).sum_comp
    (multiplicativeCoverRate p ζ)]
  simp only [multiplicativeCoverRate, coverPair, Equiv.symm_apply_apply]
  unfold pairProductSum
  exact (Finset.sum_subtype ((univ : Finset (Quotient ζ)).powersetCard 2)
    (fun s ↦ Finset.mem_powersetCard_univ) fun t ↦ ∏ C ∈ t, blockMass p ζ C).symm

/-- **Masses add.**  After `C` and `D` merge, the component containing them has mass
`p(C) + p(D)`. -/
theorem blockMass_merge {w : ℕ} (p : Fin w → ℝ) (ζ : Coalescent.ER w) {C D : Quotient ζ}
    (hCD : C ≠ D) {i : Fin w} (hi : Quotient.mk ζ i = C) :
    blockMass p (Coalescent.merge ζ C D) (Quotient.mk _ i)
      = blockMass p ζ C + blockMass p ζ D := by
  have hdisj : Disjoint (univ.filter fun j : Fin w ↦ Quotient.mk ζ j = C)
      (univ.filter fun j : Fin w ↦ Quotient.mk ζ j = D) :=
    Finset.disjoint_filter.mpr fun j _ hj1 hj2 ↦ hCD (hj1.symm.trans hj2)
  unfold blockMass
  rw [← Finset.sum_union hdisj]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hj
    have hr : Coalescent.mergeMap ζ C D (Quotient.mk ζ j)
        = Coalescent.mergeMap ζ C D (Quotient.mk ζ i) := Quotient.exact hj
    rw [hi, Coalescent.mergeMap_apply_of_ne ζ C D C hCD] at hr
    by_cases hjD : Quotient.mk ζ j = D
    · exact Or.inr hjD
    · rw [Coalescent.mergeMap_apply_of_ne ζ C D _ hjD] at hr
      exact Or.inl hr
  · intro hj
    apply Quotient.sound
    show Coalescent.mergeMap ζ C D (Quotient.mk ζ j)
      = Coalescent.mergeMap ζ C D (Quotient.mk ζ i)
    rw [hi, Coalescent.mergeMap_apply_of_ne ζ C D C hCD]
    rcases hj with hj | hj
    · rw [hj, Coalescent.mergeMap_apply_of_ne ζ C D C hCD]
    · rw [hj, Coalescent.mergeMap_apply_self]

/-- **`κ_ζ = (1 - ∑_C p(C)²)/2`**, twice over, when the fiber masses sum to one. -/
theorem two_mul_sum_multiplicativeCoverRate {w : ℕ} {p : Fin w → ℝ} (hp : ∑ i, p i = 1)
    (ζ : Coalescent.ER w) :
    2 * ∑ η, multiplicativeCoverRate p ζ η = 1 - ∑ C, blockMass p ζ C ^ 2 := by
  rw [sum_multiplicativeCoverRate, two_mul_pairProductSum, sum_blockMass, hp, one_pow]

/-- The total rate of `Z_p` in scaled time is at most one half. -/
theorem sum_multiplicativeCoverRate_le_half {w : ℕ} {p : Fin w → ℝ} (hp : ∑ i, p i = 1)
    (ζ : Coalescent.ER w) : ∑ η, multiplicativeCoverRate p ζ η ≤ 1 / 2 := by
  have h := two_mul_sum_multiplicativeCoverRate hp ζ
  have hsq : 0 ≤ ∑ C, blockMass p ζ C ^ 2 := Finset.sum_nonneg fun C _ ↦ sq_nonneg _
  linarith

/-! ### The rate comparison while the reports agree

Components are indexed by an arbitrary finite type `ι`; `c C` is the number of sampled
haplotypes in the fibers of `C` and `L C` its load, the number of true ancestral blocks inside
it.  While the Kingman report and `Z_p` agree, every block lies in exactly one component, so
`L C ≤ c C`. -/

/-- **The deficit of a component**: `D_C = c(C) - L_C`, the Kingman mergers already absorbed
inside `C`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A difference of two counts. -/
def loadDeficit {ι : Type*} (c L : ι → ℝ) (C : ι) : ℝ := c C - L C

/-- The total deficit is `J = n - K`. -/
theorem sum_loadDeficit {ι : Type*} [Fintype ι] (c L : ι → ℝ) :
    ∑ C, loadDeficit c L C = ∑ C, c C - ∑ C, L C :=
  Finset.sum_sub_distrib c L

/-- **The actual visible rate is at most the comparison rate**, pair by pair:
`L_C L_D ≤ c(C) c(D)`. -/
theorem load_mul_load_le {ι : Type*} {c L : ι → ℝ} (hL0 : ∀ C, 0 ≤ L C)
    (hL : ∀ C, L C ≤ c C) (C D : ι) : L C * L D ≤ c C * c D :=
  mul_le_mul (hL C) (hL D) (hL0 D) ((hL0 C).trans (hL C))

/-- **The excess identity of the note**:
`∑_{C<D} (c(C) c(D) - L_C L_D) = ∑_C D_C (n - c(C)) - ∑_{C<D} D_C D_D`. -/
theorem pairProductSum_sub_eq {ι : Type*} [Fintype ι] (c L : ι → ℝ) :
    pairProductSum c - pairProductSum L
      = ∑ C, loadDeficit c L C * (∑ D, c D - c C) - pairProductSum (loadDeficit c L) := by
  have hc := two_mul_pairProductSum c
  have hL := two_mul_pairProductSum L
  have hD := two_mul_pairProductSum (loadDeficit c L)
  have hsum := sum_loadDeficit c L
  have hpoint : ∑ C, (L C ^ 2 - c C ^ 2 - loadDeficit c L C ^ 2
      + 2 * (loadDeficit c L C * c C)) = 0 :=
    Finset.sum_eq_zero fun C _ ↦ by
      unfold loadDeficit
      ring
  have hcross : ∑ C, loadDeficit c L C * (∑ D, c D - c C)
      = (∑ D, c D) * ∑ C, loadDeficit c L C - ∑ C, loadDeficit c L C * c C := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun C _ ↦ by ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hpoint
  rw [hcross]
  linear_combination (1 / 2 : ℝ) * hc - (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hD
    + (1 / 2 : ℝ) * hpoint
    + (1 / 2 : ℝ) * (∑ C, loadDeficit c L C - ∑ D, c D - ∑ C, L C) * hsum

/-- **The total excess rate is at most `n J`**: `∑_{C<D} (c(C) c(D) - L_C L_D) ≤ n J`. -/
theorem pairProductSum_sub_le {ι : Type*} [Fintype ι] {c L : ι → ℝ} (hc : ∀ C, 0 ≤ c C)
    (hL : ∀ C, L C ≤ c C) :
    pairProductSum c - pairProductSum L ≤ (∑ C, c C) * ∑ C, loadDeficit c L C := by
  have hD : ∀ C, 0 ≤ loadDeficit c L C := fun C ↦ sub_nonneg.mpr (hL C)
  rw [pairProductSum_sub_eq, Finset.mul_sum]
  have hpair := pairProductSum_nonneg hD
  have hle : ∑ C, loadDeficit c L C * (∑ D, c D - c C)
      ≤ ∑ C, (∑ D, c D) * loadDeficit c L C :=
    Finset.sum_le_sum fun C _ ↦ by nlinarith [hD C, hc C]
  linarith

/-- **The rate comparison in scaled time**: `∑_{C<D} (c(C) c(D) - L_C L_D)/n² ≤ J/n`. -/
theorem pairProductSum_sub_div_sq_le {ι : Type*} [Fintype ι] {c L : ι → ℝ}
    (hc : ∀ C, 0 ≤ c C) (hL : ∀ C, L C ≤ c C) (hn : 0 < ∑ C, c C) :
    (pairProductSum c - pairProductSum L) / (∑ C, c C) ^ 2
      ≤ (∑ C, loadDeficit c L C) / ∑ C, c C := by
  rw [div_le_div_iff₀ (pow_pos hn 2) hn]
  have h := pairProductSum_sub_le hc hL
  nlinarith

/-- **The total Kingman rate in scaled time is at most one half**: with `K ≤ n` blocks,
`binom(K, 2)/n² ≤ 1/2`. -/
theorem deathRate_div_sq_le_half {K n : ℕ} (hK : K ≤ n) :
    Coalescent.deathRate K / (n : ℝ) ^ 2 ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hKR : (K : ℝ) ≤ n := by exact_mod_cast hK
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [div_le_iff₀ (pow_pos hnR 2)]
  unfold Coalescent.deathRate Descent.Core.pairCount
  nlinarith

/-! ### The discrete coupling bound

A coupled chain lives on a finite state space `S` with a stochastic kernel `P`.  `sep` marks
the states at which the two coordinates have separated, and it is absorbing.  `J` is the
deficit.  The two one-step hypotheses are the note's: from an unseparated state the chance
of separating is at most `h J`, and the expected deficit after the step, on the unseparated
event, is at most `J + ρ`.  With `h = 1/n` and `ρ = 1/2` the conclusion is `m(m-1)/(4n)`. -/

section Separation

variable {S : Type*} [Fintype S]

/-- **The law of a finite chain after `k` steps**, as a vector of masses.

Empirical status: NOT AN EMPIRICAL CLAIM.  The `k`-th power of a kernel applied to an initial
vector. -/
noncomputable def skeletonLaw (P : S → S → ℝ) (μ₀ : S → ℝ) : ℕ → S → ℝ
  | 0 => μ₀
  | k + 1 => fun t ↦ ∑ s, skeletonLaw P μ₀ k s * P s t

theorem skeletonLaw_nonneg {P : S → S → ℝ} {μ₀ : S → ℝ} (hP : ∀ s t, 0 ≤ P s t)
    (hμ : ∀ s, 0 ≤ μ₀ s) (k : ℕ) (t : S) : 0 ≤ skeletonLaw P μ₀ k t := by
  induction k generalizing t with
  | zero => exact hμ t
  | succ k ih => exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (ih s) (hP s t)

/-- One step, summed over a set of targets, is the previous law against the kernel's mass on
that set. -/
theorem sum_skeletonLaw_succ (P : S → S → ℝ) (μ₀ : S → ℝ) (k : ℕ) (F : Finset S)
    (g : S → ℝ) :
    ∑ t ∈ F, skeletonLaw P μ₀ (k + 1) t * g t
      = ∑ s, skeletonLaw P μ₀ k s * ∑ t ∈ F, P s t * g t := by
  simp only [skeletonLaw, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ by ring

/-- A stochastic kernel preserves total mass. -/
theorem sum_skeletonLaw {P : S → S → ℝ} {μ₀ : S → ℝ} (hrow : ∀ s, ∑ t, P s t = 1)
    (k : ℕ) : ∑ t, skeletonLaw P μ₀ k t = ∑ s, μ₀ s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := sum_skeletonLaw_succ P μ₀ k univ fun _ ↦ 1
    simp only [mul_one, hrow] at h
    rw [h, ih]

/-- **The mass of the separated states after `k` steps.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of a law over a set of states. -/
noncomputable def separationMass (P : S → S → ℝ) (μ₀ : S → ℝ) (sep : S → Prop) (k : ℕ) :
    ℝ :=
  ∑ t ∈ univ.filter sep, skeletonLaw P μ₀ k t

/-- **The expected deficit on the unseparated event after `k` steps.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of a law against a function. -/
noncomputable def deficitMass (P : S → S → ℝ) (μ₀ : S → ℝ) (sep : S → Prop) (J : S → ℝ)
    (k : ℕ) : ℝ :=
  ∑ t ∈ univ.filter (fun t ↦ ¬ sep t), skeletonLaw P μ₀ k t * J t

/-- The unseparated mass of a law is at most its total mass. -/
theorem sum_filter_not_skeletonLaw_le {P : S → S → ℝ} {μ₀ : S → ℝ} (hP : ∀ s t, 0 ≤ P s t)
    (hrow : ∀ s, ∑ t, P s t = 1) (hμ : ∀ s, 0 ≤ μ₀ s) (hμ1 : ∑ s, μ₀ s = 1)
    (F : Finset S) (k : ℕ) : ∑ s ∈ F, skeletonLaw P μ₀ k s ≤ 1 := by
  rw [← hμ1, ← sum_skeletonLaw hrow k]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    fun s _ _ ↦ skeletonLaw_nonneg hP hμ k s

/-- **The deficit grows by at most `ρ` per step.** -/
theorem deficitMass_le {P : S → S → ℝ} {μ₀ : S → ℝ} {sep : S → Prop} {J : S → ℝ} {ρ : ℝ}
    (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1) (hμ : ∀ s, 0 ≤ μ₀ s)
    (hμ1 : ∑ s, μ₀ s = 1) (hρ : 0 ≤ ρ) (habsorb : ∀ s t, sep s → ¬ sep t → P s t = 0)
    (hdrift : ∀ s, ¬ sep s → ∑ t ∈ univ.filter (fun t ↦ ¬ sep t), P s t * J t ≤ J s + ρ)
    (hstart : deficitMass P μ₀ sep J 0 ≤ 0) (k : ℕ) :
    deficitMass P μ₀ sep J k ≤ ρ * k := by
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
    set G : S → ℝ := fun s ↦ ∑ t ∈ univ.filter (fun t ↦ ¬ sep t), P s t * J t with hG
    have hswap : deficitMass P μ₀ sep J (k + 1) = ∑ s, skeletonLaw P μ₀ k s * G s :=
      sum_skeletonLaw_succ P μ₀ k _ J
    have hsplit := Finset.sum_filter_add_sum_filter_not univ sep
      fun s ↦ skeletonLaw P μ₀ k s * G s
    have hsep0 : ∑ s ∈ univ.filter sep, skeletonLaw P μ₀ k s * G s = 0 := by
      refine Finset.sum_eq_zero fun s hs ↦ ?_
      have hs' := (Finset.mem_filter.mp hs).2
      have hGs : G s = 0 := Finset.sum_eq_zero fun t ht ↦ by
        rw [habsorb s t hs' (Finset.mem_filter.mp ht).2, zero_mul]
      rw [hGs, mul_zero]
    have hle : ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s * G s
        ≤ ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s * (J s + ρ) :=
      Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_left
        (hdrift s (Finset.mem_filter.mp hs).2) (skeletonLaw_nonneg hP hμ k s)
    have hexpand : ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s * (J s + ρ)
        = deficitMass P μ₀ sep J k
          + ρ * ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s := by
      rw [deficitMass, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ ↦ by ring
    have hmass := sum_filter_not_skeletonLaw_le hP hrow hμ hμ1
      (univ.filter fun s ↦ ¬ sep s) k
    have hρmass := mul_le_mul_of_nonneg_left hmass hρ
    push_cast
    linarith

/-- **The discrete coupling bound.**  If separation is absorbing, its one-step chance from an
unseparated state is at most `h J`, and the deficit drifts by at most `ρ`, then the chain has
separated by step `k` with probability at most `h ρ k (k - 1)/2`.

Assumes: the kernel is stochastic, the initial law is a probability vector with no separated
mass and no deficit, and `0 ≤ h`, `0 ≤ ρ`. -/
theorem separationMass_le {P : S → S → ℝ} {μ₀ : S → ℝ} {sep : S → Prop} {J : S → ℝ}
    {h ρ : ℝ} (hP : ∀ s t, 0 ≤ P s t) (hrow : ∀ s, ∑ t, P s t = 1) (hμ : ∀ s, 0 ≤ μ₀ s)
    (hμ1 : ∑ s, μ₀ s = 1) (hh : 0 ≤ h) (hρ : 0 ≤ ρ)
    (habsorb : ∀ s t, sep s → ¬ sep t → P s t = 0)
    (hhazard : ∀ s, ¬ sep s → ∑ t ∈ univ.filter sep, P s t ≤ h * J s)
    (hdrift : ∀ s, ¬ sep s → ∑ t ∈ univ.filter (fun t ↦ ¬ sep t), P s t * J t ≤ J s + ρ)
    (hsep0 : separationMass P μ₀ sep 0 = 0) (hdef0 : deficitMass P μ₀ sep J 0 ≤ 0) (k : ℕ) :
    separationMass P μ₀ sep k ≤ h * ρ * ((k : ℝ) * ((k : ℝ) - 1) / 2) := by
  induction k with
  | zero => simp [hsep0]
  | succ k ih =>
    set G : S → ℝ := fun s ↦ ∑ t ∈ univ.filter sep, P s t with hG
    have hswap : separationMass P μ₀ sep (k + 1) = ∑ s, skeletonLaw P μ₀ k s * G s := by
      have h1 := sum_skeletonLaw_succ P μ₀ k (univ.filter sep) fun _ ↦ 1
      simp only [mul_one] at h1
      exact h1
    have hsplit := Finset.sum_filter_add_sum_filter_not univ sep
      fun s ↦ skeletonLaw P μ₀ k s * G s
    have hA : ∑ s ∈ univ.filter sep, skeletonLaw P μ₀ k s * G s
        ≤ separationMass P μ₀ sep k := by
      refine Finset.sum_le_sum fun s _ ↦ ?_
      have hle1 : G s ≤ 1 := by
        rw [hG, ← hrow s]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun t _ _ ↦ hP s t
      calc skeletonLaw P μ₀ k s * G s ≤ skeletonLaw P μ₀ k s * 1 :=
            mul_le_mul_of_nonneg_left hle1 (skeletonLaw_nonneg hP hμ k s)
        _ = skeletonLaw P μ₀ k s := mul_one _
    have hB : ∑ s ∈ univ.filter (fun s ↦ ¬ sep s), skeletonLaw P μ₀ k s * G s
        ≤ h * deficitMass P μ₀ sep J k := by
      rw [deficitMass, Finset.mul_sum]
      refine Finset.sum_le_sum fun s hs ↦ ?_
      calc skeletonLaw P μ₀ k s * G s ≤ skeletonLaw P μ₀ k s * (h * J s) :=
            mul_le_mul_of_nonneg_left (hhazard s (Finset.mem_filter.mp hs).2)
              (skeletonLaw_nonneg hP hμ k s)
        _ = h * (skeletonLaw P μ₀ k s * J s) := by ring
    have hdef := deficitMass_le hP hrow hμ hμ1 hρ habsorb hdrift hdef0 k
    have hhdef := mul_le_mul_of_nonneg_left hdef hh
    push_cast
    nlinarith

end Separation

/-! ### Running the skeleton at the rings of a Poisson clock

Uniformized at rate one in scaled time, the number of steps taken by time `U` is Poisson with
mean `U`, independent of the skeleton.  Its second factorial moment is `U²`, which turns
`m(m-1)/(4n)` into `U²/(4n)`. -/

open ProbabilityTheory

/-- The Poisson mass function against the falling factorial of degree two, one term. -/
theorem poissonPMFReal_add_two_mul (U : NNReal) (j : ℕ) :
    poissonPMFReal U (j + 2) * (((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1))
      = (U : ℝ) ^ 2 * poissonPMFReal U j := by
  unfold poissonPMFReal
  rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The second factorial moment of a Poisson law is `U²`.** -/
theorem hasSum_poissonPMFReal_mul_descFactorial (U : NNReal) :
    HasSum (fun m : ℕ ↦ poissonPMFReal U m * ((m : ℝ) * ((m : ℝ) - 1))) ((U : ℝ) ^ 2) := by
  have hshift : HasSum
      (fun j : ℕ ↦ poissonPMFReal U (j + 2) * (((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1)))
      ((U : ℝ) ^ 2) := by
    have h := (poissonPMFRealSum U).mul_left ((U : ℝ) ^ 2)
    simp only [mul_one] at h
    have hfun : (fun j : ℕ ↦
        poissonPMFReal U (j + 2) * (((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1)))
        = fun j ↦ (U : ℝ) ^ 2 * poissonPMFReal U j :=
      funext (poissonPMFReal_add_two_mul U)
    rw [hfun]
    exact h
  have h2 := (hasSum_nat_add_iff
    (f := fun m : ℕ ↦ poissonPMFReal U m * ((m : ℝ) * ((m : ℝ) - 1))) 2).mp hshift
  simpa [Finset.sum_range_succ] using h2

/-- **A sequence mixed over the rings of a Poisson clock of mean `U`.**

Empirical status: NOT AN EMPIRICAL CLAIM.  An infinite convex combination with Poisson
weights. -/
noncomputable def poissonMixture (U : NNReal) (a : ℕ → ℝ) : ℝ :=
  ∑' m, poissonPMFReal U m * a m

/-- **(F1), as a bound on the Poisson-mixed separation probability**: if after `m` steps the
separation probability is at most `m(m-1)/(4n)`, then by scaled time `U` it is at most
`U²/(4n)`. -/
theorem poissonMixture_le {U : NNReal} {a : ℕ → ℝ} {n : ℝ} (hn : 0 < n)
    (ha0 : ∀ m, 0 ≤ a m) (ha : ∀ m, a m ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n)) :
    poissonMixture U a ≤ (U : ℝ) ^ 2 / (4 * n) := by
  have hB := (hasSum_poissonPMFReal_mul_descFactorial U).div_const (4 * n)
  have hterm : ∀ m : ℕ, poissonPMFReal U m * a m
      ≤ poissonPMFReal U m * ((m : ℝ) * ((m : ℝ) - 1)) / (4 * n) := by
    intro m
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (ha m) poissonPMFReal_nonneg
  have hA : Summable fun m : ℕ ↦ poissonPMFReal U m * a m :=
    Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (ha0 m)) hterm
      hB.summable
  exact hasSum_le hterm hA.hasSum hB

/-- A Poisson mixture of probabilities is a probability. -/
theorem poissonMixture_le_one {U : NNReal} {a : ℕ → ℝ} (ha0 : ∀ m, 0 ≤ a m)
    (ha1 : ∀ m, a m ≤ 1) : poissonMixture U a ≤ 1 := by
  have hB := poissonPMFRealSum U
  have hterm : ∀ m : ℕ, poissonPMFReal U m * a m ≤ poissonPMFReal U m := fun m ↦ by
    calc poissonPMFReal U m * a m ≤ poissonPMFReal U m * 1 :=
          mul_le_mul_of_nonneg_left (ha1 m) poissonPMFReal_nonneg
      _ = poissonPMFReal U m := mul_one _
  have hA : Summable fun m : ℕ ↦ poissonPMFReal U m * a m :=
    Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (ha0 m)) hterm
      hB.summable
  exact hasSum_le hterm hA.hasSum hB

/-- **(F1), capped**: `min {1, U²/(4n)}`. -/
theorem poissonMixture_le_min {U : NNReal} {a : ℕ → ℝ} {n : ℝ} (hn : 0 < n)
    (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1)
    (ha : ∀ m, a m ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n)) :
    poissonMixture U a ≤ min 1 ((U : ℝ) ^ 2 / (4 * n)) :=
  le_min (poissonMixture_le_one ha0 ha1) (poissonMixture_le hn ha0 ha)

/-! ### The coupling inequality at path level

A coupled chain on `S` carries two observations `F G : S → X`.  The laws of the two observed
paths are images of one law on coupled paths, so the sum of their absolute differences is at
most twice the mass of the coupled paths along which the observations differ somewhere.  When
the observations agree at every unseparated state and separation is absorbing, that mass is at
most the separation mass. -/

section PathCoupling

variable {S : Type*} [Fintype S]

/-- **The weight of an `m`-step path**: the initial mass times the transition masses along it.

Empirical status: NOT AN EMPIRICAL CLAIM.  The finite-dimensional law of a Markov chain. -/
noncomputable def skeletonPathWeight (P : S → S → ℝ) (μ₀ : S → ℝ) (m : ℕ)
    (ω : Fin (m + 1) → S) : ℝ :=
  μ₀ (ω 0) * ∏ k : Fin m, P (ω k.castSucc) (ω k.succ)

theorem skeletonPathWeight_nonneg {P : S → S → ℝ} {μ₀ : S → ℝ} (hP : ∀ s t, 0 ≤ P s t)
    (hμ : ∀ s, 0 ≤ μ₀ s) (m : ℕ) (ω : Fin (m + 1) → S) :
    0 ≤ skeletonPathWeight P μ₀ m ω :=
  mul_nonneg (hμ _) (Finset.prod_nonneg fun _ _ ↦ hP _ _)

/-- Extending a path by one step multiplies its weight by the last transition. -/
theorem skeletonPathWeight_snoc (P : S → S → ℝ) (μ₀ : S → ℝ) (m : ℕ)
    (ω : Fin (m + 1) → S) (x : S) :
    skeletonPathWeight P μ₀ (m + 1) (Fin.snoc ω x)
      = skeletonPathWeight P μ₀ m ω * P (ω (Fin.last m)) x := by
  unfold skeletonPathWeight
  rw [Fin.prod_univ_castSucc, ← Fin.castSucc_zero' (n := m + 1)]
  simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

/-- A sum over paths of one more step splits off the last state. -/
theorem sum_pi_fin_succ {M : Type*} [AddCommMonoid M] (m : ℕ)
    (F : (Fin (m + 1 + 1) → S) → M) :
    ∑ ω, F ω = ∑ ω : Fin (m + 1) → S, ∑ x : S, F (Fin.snoc ω x) := by
  rw [← (Fin.snocEquiv fun _ : Fin (m + 1 + 1) ↦ S).sum_comp F, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- **The last coordinate of the path law is the skeleton law.** -/
theorem sum_skeletonPathWeight_mul (P : S → S → ℝ) (μ₀ : S → ℝ) (m : ℕ) (g : S → ℝ) :
    ∑ ω : Fin (m + 1) → S, skeletonPathWeight P μ₀ m ω * g (ω (Fin.last m))
      = ∑ t, skeletonLaw P μ₀ m t * g t := by
  induction m generalizing g with
  | zero =>
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ fun ω ↦ ?_
    rw [skeletonPathWeight, Fin.prod_univ_zero, mul_one]
    rfl
  | succ m ih =>
    rw [sum_pi_fin_succ, sum_skeletonLaw_succ P μ₀ m univ g,
      ← ih fun t ↦ ∑ t' ∈ univ, P t t' * g t']
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [skeletonPathWeight_snoc, Fin.snoc_last]
    ring

/-- **The coupling inequality for finite laws**: two images of one nonnegative mass differ, in
summed absolute value, by at most twice the mass on which the two maps disagree. -/
theorem sum_abs_sub_fiber_le {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (wt : Ω → ℝ)
    (hwt : ∀ ω, 0 ≤ wt ω) (F G : Ω → X) :
    ∑ x, |∑ ω ∈ univ.filter (fun ω ↦ F ω = x), wt ω
        - ∑ ω ∈ univ.filter (fun ω ↦ G ω = x), wt ω|
      ≤ 2 * ∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω), wt ω := by
  have hdiff : ∀ x, ∑ ω ∈ univ.filter (fun ω ↦ F ω = x), wt ω
      - ∑ ω ∈ univ.filter (fun ω ↦ G ω = x), wt ω
      = ∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω),
          wt ω * ((if F ω = x then 1 else 0) - (if G ω = x then 1 else 0)) := by
    intro x
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    by_cases h : F ω = G ω
    · rw [h, sub_self, if_neg fun hne ↦ hne rfl]
    · rw [if_pos h]
      split_ifs <;> ring
  calc ∑ x, |∑ ω ∈ univ.filter (fun ω ↦ F ω = x), wt ω
        - ∑ ω ∈ univ.filter (fun ω ↦ G ω = x), wt ω|
      = ∑ x, |∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω),
          wt ω * ((if F ω = x then 1 else 0) - (if G ω = x then 1 else 0))| :=
        Finset.sum_congr rfl fun x _ ↦ by rw [hdiff x]
    _ ≤ ∑ x, ∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω),
          wt ω * ((if F ω = x then 1 else 0) + (if G ω = x then 1 else 0)) := by
        refine Finset.sum_le_sum fun x _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun ω _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hwt ω)]
        exact mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) (hwt ω)
    _ = ∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω), wt ω * 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        ring
    _ = 2 * ∑ ω ∈ univ.filter (fun ω ↦ F ω ≠ G ω), wt ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ ↦ mul_comm _ _

/-- **Along a path of positive weight separation is absorbing**: once separated, separated at
the end. -/
theorem sep_last_of_skeletonPathWeight_ne_zero {P : S → S → ℝ} {μ₀ : S → ℝ} {sep : S → Prop}
    (habsorb : ∀ s t, sep s → ¬ sep t → P s t = 0) {m : ℕ} {ω : Fin (m + 1) → S}
    (hω : skeletonPathWeight P μ₀ m ω ≠ 0) {k : Fin (m + 1)} (hk : sep (ω k)) :
    sep (ω (Fin.last m)) := by
  have hstep : ∀ i : ℕ, (hi : i < m) → sep (ω ⟨i, by omega⟩) → sep (ω ⟨i + 1, by omega⟩) := by
    intro i hi hs
    by_contra hns
    apply hω
    unfold skeletonPathWeight
    have hzero : P (ω (Fin.castSucc ⟨i, hi⟩)) (ω (Fin.succ ⟨i, hi⟩)) = 0 :=
      habsorb _ _ hs hns
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨i, hi⟩) hzero)
  have hall : ∀ d : ℕ, (hd : k.val + d ≤ m) → sep (ω ⟨k.val + d, by omega⟩) := by
    intro d
    induction d with
    | zero =>
      intro hd
      simpa using hk
    | succ d ih =>
      intro hd
      exact hstep (k.val + d) (by omega) (ih (by omega))
  have hend := hall (m - k.val) (by omega)
  have hidx : (⟨k.val + (m - k.val), by omega⟩ : Fin (m + 1)) = Fin.last m := by
    ext
    simp only [Fin.val_last]
    omega
  rwa [hidx] at hend

/-- **The paths along which the observations differ carry at most the separation mass.** -/
theorem sum_filter_path_ne_le_separationMass {X : Type*} [DecidableEq X] {P : S → S → ℝ}
    {μ₀ : S → ℝ} {sep : S → Prop} (hP : ∀ s t, 0 ≤ P s t) (hμ : ∀ s, 0 ≤ μ₀ s)
    (habsorb : ∀ s t, sep s → ¬ sep t → P s t = 0) (F G : S → X)
    (hagree : ∀ s, ¬ sep s → F s = G s) (m : ℕ) :
    ∑ ω ∈ univ.filter
        (fun ω : Fin (m + 1) → S ↦ (fun k ↦ F (ω k)) ≠ fun k ↦ G (ω k)),
        skeletonPathWeight P μ₀ m ω
      ≤ separationMass P μ₀ sep m := by
  have hsm : separationMass P μ₀ sep m = ∑ ω : Fin (m + 1) → S,
      skeletonPathWeight P μ₀ m ω * (if sep (ω (Fin.last m)) then 1 else 0) := by
    rw [separationMass, Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun t _ ↦ ?_)
      (sum_skeletonPathWeight_mul P μ₀ m fun t ↦ if sep t then 1 else 0).symm
    show (if sep t then skeletonLaw P μ₀ m t else 0)
      = skeletonLaw P μ₀ m t * (if sep t then 1 else 0)
    split_ifs <;> simp
  rw [hsm, Finset.sum_filter]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  split_ifs with hne hsep hsep
  · rw [mul_one]
  · have hzero : skeletonPathWeight P μ₀ m ω = 0 := by
      by_contra hω
      obtain ⟨k, hk⟩ : ∃ k, F (ω k) ≠ G (ω k) := by
        by_contra hall
        push_neg at hall
        exact hne (funext hall)
      exact hsep (sep_last_of_skeletonPathWeight_ne_zero habsorb hω
        (by_contra fun hs ↦ hk (hagree _ hs)))
    rw [hzero, zero_mul]
  · rw [mul_one]
    exact skeletonPathWeight_nonneg hP hμ m ω
  · rw [mul_zero]

/-- **The coupling inequality at path level.**  The observed path laws of a coupled chain differ,
in summed absolute value, by at most twice its separation mass; with `separationMass_le` this is
the discrete form of (F1).

Assumes: the kernel and the initial law are nonnegative, separation is absorbing, and the two
observations agree at every unseparated state. -/
theorem pathTotalVariation_le_separationMass {X : Type*} [Fintype X] [DecidableEq X]
    {P : S → S → ℝ} {μ₀ : S → ℝ} {sep : S → Prop} (hP : ∀ s t, 0 ≤ P s t) (hμ : ∀ s, 0 ≤ μ₀ s)
    (habsorb : ∀ s t, sep s → ¬ sep t → P s t = 0) (F G : S → X)
    (hagree : ∀ s, ¬ sep s → F s = G s) (m : ℕ) :
    ∑ y : Fin (m + 1) → X,
        |∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → S ↦ (fun k ↦ F (ω k)) = y),
            skeletonPathWeight P μ₀ m ω
          - ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → S ↦ (fun k ↦ G (ω k)) = y),
            skeletonPathWeight P μ₀ m ω|
      ≤ 2 * separationMass P μ₀ sep m :=
  (sum_abs_sub_fiber_le (skeletonPathWeight P μ₀ m) (skeletonPathWeight_nonneg hP hμ m)
    (fun ω k ↦ F (ω k)) fun ω k ↦ G (ω k)).trans
    (mul_le_mul_of_nonneg_left
      (sum_filter_path_ne_le_separationMass hP hμ habsorb F G hagree m) zero_le_two)

end PathCoupling

end Descent.Pangenome.GraphCoalescent

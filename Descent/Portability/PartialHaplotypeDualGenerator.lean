/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeCarrier
import Mathlib.Algebra.MvPolynomial.PDeriv

assert_below Descent.Decision Descent.Program

/-!
# The neutral diffusion generator on partial-haplotype moments

This module formalizes the generator identity (19) of NOTE1 §4.2 for finitely many demes,
finitely many loci and finite alphabets.  The forward neutral diffusion generator is a genuine
second-order differential operator on the polynomial ring in the multi-deme haplotype
frequencies `x_i[h]`: its first-order part carries migration, recombination and mutation, and
its second-order part in deme `i` is the Wright–Fisher operator
`(c_i / 2) Σ_{g,k} x_g (δ_{gk} − x_k) ∂_g ∂_k`.  Partial derivatives are `MvPolynomial.pderiv`,
so the Leibniz rule on products is a theorem, not a definition: the generator of a product is
the product rule plus the carré du champ, and the carré du champ of two partial-haplotype
frequencies in the same deme is `c_i (x[A ∪ B, a ∪ b] − x[A, a] x[B, b])` for compatible
assignments and `−c_i x[A, a] x[B, b]` otherwise.

The configuration moment `H_ξ` of (17) is the product of marginal frequency polynomials over
the carriers of `ξ`.  The Leibniz rule expands the generator of `H_ξ` carrier by carrier and
pair by pair: one term for each carrier with the generator of its marginal frequency, and one
term for each ordered pair of distinct carriers with half the carré du champ.  This expansion
is proved for every configuration by induction on the multiset.

## Empirical status

None.  The bodies here are algebra: they differentiate polynomials in a supplied frequency
vector and multiply marginal masses of supplied probability laws, so no measurement can bear on
them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeDualGenerator

open PartialHaplotypeCarrier MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-- A full haplotype: one allele at every locus. -/
abbrev FullHaplotype (Locus : Type*) (Allele : Locus → Type*) := ∀ ℓ, Allele ℓ

/-- The frequency variable `x_i[h]`: a deme together with a full haplotype. -/
abbrev FrequencyVariable (Deme Locus : Type*) (Allele : Locus → Type*) :=
  Deme × FullHaplotype Locus Allele

/-- Real polynomials in all multi-deme haplotype frequencies. -/
abbrev FrequencyPolynomial (Deme Locus : Type*) (Allele : Locus → Type*) :=
  MvPolynomial (FrequencyVariable Deme Locus Allele) ℝ

/-- Rates of the neutral model of NOTE1 §4.2: pairwise coalescence in each deme, backward
lineage migration between demes, recombination along each crossover selector, and per-site
mutation between alleles.  Mutation is symmetric, as §4.2 requires for the dual to be a
substochastic generator without a diagonal potential. -/
structure NeutralRates (Deme Locus : Type*) (Allele : Locus → Type*) where
  /-- Coalescence rate `c_i` of one unordered pair of lineages in deme `i`. -/
  coalescence : Deme → ℝ
  /-- Backward migration rate of a lineage from the first deme to the second. -/
  migration : Deme → Deme → ℝ
  /-- Rate of the crossover pattern whose selected loci come from one parent. -/
  recombination : (Locus → Bool) → ℝ
  /-- Mutation rate at a locus from the first allele to the second. -/
  mutation : ∀ ℓ, Allele ℓ → Allele ℓ → ℝ
  /-- Coalescence rates are nonnegative. -/
  coalescence_nonneg : ∀ i, 0 ≤ coalescence i
  /-- Migration rates are nonnegative. -/
  migration_nonneg : ∀ i j, 0 ≤ migration i j
  /-- Recombination rates are nonnegative. -/
  recombination_nonneg : ∀ selector, 0 ≤ recombination selector
  /-- Mutation rates are nonnegative. -/
  mutation_nonneg : ∀ ℓ a b, 0 ≤ mutation ℓ a b
  /-- Forward and reverse mutation rates between two alleles agree. -/
  mutation_symm : ∀ ℓ a b, mutation ℓ a b = mutation ℓ b a

/-- The unit-rate neutral model: every coalescence, migration, recombination and mutation rate
equals one.  It inhabits `NeutralRates`, so the theorems below are not vacuous. -/
def NeutralRates.uniform : NeutralRates Deme Locus Allele where
  coalescence _ := 1
  migration _ _ := 1
  recombination _ := 1
  mutation _ _ _ := 1
  coalescence_nonneg _ := zero_le_one
  migration_nonneg _ _ := zero_le_one
  recombination_nonneg _ := zero_le_one
  mutation_nonneg _ _ _ := zero_le_one
  mutation_symm _ _ _ := rfl

/-- A full haplotype satisfies a partial allele assignment when it carries the assigned allele
at every assigned locus. -/
def Satisfies (assignment : ∀ ℓ, Option (Allele ℓ)) (hap : FullHaplotype Locus Allele) :
    Prop :=
  ∀ ℓ, assignment ℓ = none ∨ assignment ℓ = some (hap ℓ)

/-- Satisfaction of a partial assignment is decidable over finitely many loci. -/
instance decidableSatisfies [Fintype Locus] [∀ ℓ, DecidableEq (Allele ℓ)]
    (assignment : ∀ ℓ, Option (Allele ℓ)) (hap : FullHaplotype Locus Allele) :
    Decidable (Satisfies assignment hap) := by
  unfold Satisfies
  infer_instance

/-- Compatibility of two partial types is decidable over finitely many loci. -/
instance decidableCompatible [Fintype Locus] [∀ ℓ, DecidableEq (Allele ℓ)]
    (τ σ : PartialType Deme Locus Allele) : Decidable (Compatible τ σ) := by
  unfold Compatible
  infer_instance

/-- Partial types have decidable equality over finitely many loci. -/
instance decidableEqPartialType [DecidableEq Deme] [Fintype Locus]
    [∀ ℓ, DecidableEq (Allele ℓ)] : DecidableEq (PartialType Deme Locus Allele) :=
  fun τ σ ↦ decidable_of_iff (τ.deme = σ.deme ∧ τ.allele = σ.allele)
    ⟨fun h ↦ PartialType.eq_of_fields h.1 h.2, fun h ↦ by subst h; exact ⟨rfl, rfl⟩⟩

/-- The restriction of a partial assignment to the loci chosen by a selector. -/
def restrictAssignment (assignment : ∀ ℓ, Option (Allele ℓ)) (selector : Locus → Bool) :
    ∀ ℓ, Option (Allele ℓ) :=
  fun ℓ ↦ if selector ℓ = true then assignment ℓ else none

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- The marginal frequency polynomial `x_i[A, a] = Σ_{h ⊨ a} x_i[h]` of a partial assignment
in deme `i`.  The empty assignment gives the total frequency of the deme. -/
def assignmentPolynomial (i : Deme) (assignment : ∀ ℓ, Option (Allele ℓ)) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ hap ∈ Finset.univ.filter (Satisfies assignment), X (i, hap)

/-- The marginal frequency polynomial of a partial haplotype type. -/
def marginalPolynomial (τ : PartialType Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  assignmentPolynomial τ.deme τ.allele

/-- The configuration moment polynomial `H_ξ` of (17): the product of the marginal frequency
polynomials of the carriers. -/
def momentPolynomial (ξ : Multiset (PartialType Deme Locus Allele)) :
    FrequencyPolynomial Deme Locus Allele :=
  (ξ.map marginalPolynomial).prod

/-- The frequency point of a family of per-deme haplotype laws. -/
def lawPoint (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :
    FrequencyVariable Deme Locus Allele → ℝ :=
  fun coordinate ↦ (law coordinate.1).mass coordinate.2

/-- The first-order drift of the frequency `x_i[h]` under the neutral model: migrants from
every deme, recombinants assembled from the two marginal halves of each crossover selector, and
mutational inflow and outflow at every site. -/
def driftPolynomial (rates : NeutralRates Deme Locus Allele)
    (coordinate : FrequencyVariable Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  (∑ j, C (rates.migration coordinate.1 j) * (X (j, coordinate.2) - X coordinate))
    + (∑ selector : Locus → Bool, C (rates.recombination selector) *
        (assignmentPolynomial coordinate.1
            (restrictAssignment (fun ℓ ↦ some (coordinate.2 ℓ)) selector)
          * assignmentPolynomial coordinate.1
            (restrictAssignment (fun ℓ ↦ some (coordinate.2 ℓ)) fun ℓ ↦ !selector ℓ)
          - X coordinate))
    + ∑ ℓ, ∑ b : Allele ℓ,
        (C (rates.mutation ℓ b (coordinate.2 ℓ))
            * X (coordinate.1, Function.update coordinate.2 ℓ b)
          - C (rates.mutation ℓ (coordinate.2 ℓ) b) * X coordinate)

/-- The Wright–Fisher second-order operator of deme `i`,
`Σ_g x_g ∂_g ∂_g f − Σ_{g,k} x_g x_k ∂_g ∂_k f`. -/
def demeSecondOrder (i : Deme) (f : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ g, X (i, g) * pderiv (i, g) (pderiv (i, g) f)
    - ∑ g, ∑ k, X (i, g) * X (i, k) * pderiv (i, g) (pderiv (i, k) f)

/-- The Wright–Fisher bilinear form of deme `i`,
`Σ_g x_g ∂_g f ∂_g h − Σ_{g,k} x_g x_k ∂_g f ∂_k h`. -/
def demeCovarianceForm (i : Deme) (f h : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ g, X (i, g) * (pderiv (i, g) f * pderiv (i, g) h)
    - ∑ g, ∑ k, X (i, g) * X (i, k) * (pderiv (i, g) f * pderiv (i, k) h)

/-- **The forward neutral diffusion generator** on polynomial functions of the multi-deme
haplotype frequencies: the drift derivative plus `c_i / 2` times the Wright–Fisher operator of
every deme. -/
def neutralGenerator (rates : NeutralRates Deme Locus Allele)
    (f : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  ∑ coordinate, driftPolynomial rates coordinate * pderiv coordinate f
    + ∑ i, C (rates.coalescence i / 2) * demeSecondOrder i f

/-- Half of the carré du champ: `c_i / 2` times the Wright–Fisher bilinear form of every
deme. -/
def halfCovariance (rates : NeutralRates Deme Locus Allele)
    (f h : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  ∑ i, C (rates.coalescence i / 2) * demeCovarianceForm i f h

/-- The carré du champ `Γ(f, h) = L(f h) − f L h − h L f` of the neutral generator. -/
def carreDuChamp (rates : NeutralRates Deme Locus Allele)
    (f h : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  halfCovariance rates f h + halfCovariance rates h f

/-! ## The Leibniz rule -/

/-- The Wright–Fisher operator of one deme obeys the second-order product rule. -/
theorem demeSecondOrder_mul (i : Deme) (f h : FrequencyPolynomial Deme Locus Allele) :
    demeSecondOrder i (f * h) = f * demeSecondOrder i h + h * demeSecondOrder i f
      + demeCovarianceForm i f h + demeCovarianceForm i h f := by
  have hdiag : ∀ g : FullHaplotype Locus Allele,
      X (i, g) * pderiv (i, g) (pderiv (i, g) (f * h))
        = f * (X (i, g) * pderiv (i, g) (pderiv (i, g) h))
          + h * (X (i, g) * pderiv (i, g) (pderiv (i, g) f))
          + X (i, g) * (pderiv (i, g) f * pderiv (i, g) h)
          + X (i, g) * (pderiv (i, g) h * pderiv (i, g) f) := by
    intro g
    simp only [pderiv_mul, map_add]
    ring
  have hcross : ∀ g k : FullHaplotype Locus Allele,
      X (i, g) * X (i, k) * pderiv (i, g) (pderiv (i, k) (f * h))
        = f * (X (i, g) * X (i, k) * pderiv (i, g) (pderiv (i, k) h))
          + h * (X (i, g) * X (i, k) * pderiv (i, g) (pderiv (i, k) f))
          + X (i, g) * X (i, k) * (pderiv (i, g) f * pderiv (i, k) h)
          + X (i, g) * X (i, k) * (pderiv (i, g) h * pderiv (i, k) f) := by
    intro g k
    simp only [pderiv_mul, map_add]
    ring
  simp only [demeSecondOrder, demeCovarianceForm, hdiag, hcross, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- **The Leibniz rule of the neutral generator.**  The generator of a product is the product
rule plus both halves of the carré du champ. -/
theorem neutralGenerator_mul (rates : NeutralRates Deme Locus Allele)
    (f h : FrequencyPolynomial Deme Locus Allele) :
    neutralGenerator rates (f * h) = f * neutralGenerator rates h + h * neutralGenerator rates f
      + halfCovariance rates f h + halfCovariance rates h f := by
  have hdrift : ∀ coordinate : FrequencyVariable Deme Locus Allele,
      driftPolynomial rates coordinate * pderiv coordinate (f * h)
        = f * (driftPolynomial rates coordinate * pderiv coordinate h)
          + h * (driftPolynomial rates coordinate * pderiv coordinate f) := by
    intro coordinate
    rw [pderiv_mul]
    ring
  have hdeme : ∀ i : Deme,
      C (rates.coalescence i / 2) * demeSecondOrder i (f * h)
        = f * (C (rates.coalescence i / 2) * demeSecondOrder i h)
          + h * (C (rates.coalescence i / 2) * demeSecondOrder i f)
          + C (rates.coalescence i / 2) * demeCovarianceForm i f h
          + C (rates.coalescence i / 2) * demeCovarianceForm i h f := by
    intro i
    rw [demeSecondOrder_mul]
    ring
  simp only [neutralGenerator, halfCovariance, hdrift, hdeme, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

/-- The Leibniz rule in carré-du-champ form: `L(f h) = f L h + h L f + Γ(f, h)`. -/
theorem neutralGenerator_mul_eq_carreDuChamp (rates : NeutralRates Deme Locus Allele)
    (f h : FrequencyPolynomial Deme Locus Allele) :
    neutralGenerator rates (f * h) = f * neutralGenerator rates h + h * neutralGenerator rates f
      + carreDuChamp rates f h := by
  rw [neutralGenerator_mul, carreDuChamp]
  ring

/-- The generator annihilates constants. -/
theorem neutralGenerator_one (rates : NeutralRates Deme Locus Allele) :
    neutralGenerator rates 1 = 0 := by
  simp [neutralGenerator, demeSecondOrder, pderiv_one]

/-- Half of the carré du champ vanishes when its first argument is constant. -/
theorem halfCovariance_one_left (rates : NeutralRates Deme Locus Allele)
    (h : FrequencyPolynomial Deme Locus Allele) : halfCovariance rates 1 h = 0 := by
  simp [halfCovariance, demeCovarianceForm, pderiv_one]

/-- Half of the carré du champ vanishes when its second argument is constant. -/
theorem halfCovariance_one_right (rates : NeutralRates Deme Locus Allele)
    (f : FrequencyPolynomial Deme Locus Allele) : halfCovariance rates f 1 = 0 := by
  simp [halfCovariance, demeCovarianceForm, pderiv_one]

/-- Half of the carré du champ is a derivation in its second argument. -/
theorem halfCovariance_mul_right (rates : NeutralRates Deme Locus Allele)
    (f g h : FrequencyPolynomial Deme Locus Allele) :
    halfCovariance rates f (g * h)
      = g * halfCovariance rates f h + h * halfCovariance rates f g := by
  have hdiag : ∀ (i : Deme) (k : FullHaplotype Locus Allele),
      X (i, k) * (pderiv (i, k) f * pderiv (i, k) (g * h))
        = g * (X (i, k) * (pderiv (i, k) f * pderiv (i, k) h))
          + h * (X (i, k) * (pderiv (i, k) f * pderiv (i, k) g)) := by
    intro i k
    rw [pderiv_mul]
    ring
  have hcross : ∀ (i : Deme) (k m : FullHaplotype Locus Allele),
      X (i, k) * X (i, m) * (pderiv (i, k) f * pderiv (i, m) (g * h))
        = g * (X (i, k) * X (i, m) * (pderiv (i, k) f * pderiv (i, m) h))
          + h * (X (i, k) * X (i, m) * (pderiv (i, k) f * pderiv (i, m) g)) := by
    intro i k m
    rw [pderiv_mul]
    ring
  have hdeme : ∀ i : Deme, C (rates.coalescence i / 2) * demeCovarianceForm i f (g * h)
      = g * (C (rates.coalescence i / 2) * demeCovarianceForm i f h)
        + h * (C (rates.coalescence i / 2) * demeCovarianceForm i f g) := by
    intro i
    simp only [demeCovarianceForm, hdiag, hcross, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  simp only [halfCovariance, hdeme, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Half of the carré du champ is a derivation in its first argument. -/
theorem halfCovariance_mul_left (rates : NeutralRates Deme Locus Allele)
    (g h f : FrequencyPolynomial Deme Locus Allele) :
    halfCovariance rates (g * h) f
      = g * halfCovariance rates h f + h * halfCovariance rates g f := by
  have hdiag : ∀ (i : Deme) (k : FullHaplotype Locus Allele),
      X (i, k) * (pderiv (i, k) (g * h) * pderiv (i, k) f)
        = g * (X (i, k) * (pderiv (i, k) h * pderiv (i, k) f))
          + h * (X (i, k) * (pderiv (i, k) g * pderiv (i, k) f)) := by
    intro i k
    rw [pderiv_mul]
    ring
  have hcross : ∀ (i : Deme) (k m : FullHaplotype Locus Allele),
      X (i, k) * X (i, m) * (pderiv (i, k) (g * h) * pderiv (i, m) f)
        = g * (X (i, k) * X (i, m) * (pderiv (i, k) h * pderiv (i, m) f))
          + h * (X (i, k) * X (i, m) * (pderiv (i, k) g * pderiv (i, m) f)) := by
    intro i k m
    rw [pderiv_mul]
    ring
  have hdeme : ∀ i : Deme, C (rates.coalescence i / 2) * demeCovarianceForm i (g * h) f
      = g * (C (rates.coalescence i / 2) * demeCovarianceForm i h f)
        + h * (C (rates.coalescence i / 2) * demeCovarianceForm i g f) := by
    intro i
    simp only [demeCovarianceForm, hdiag, hcross, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  simp only [halfCovariance, hdeme, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## Expansion of a configuration moment -/

/-- The moment of a configuration with one more carrier: (17) read as a recursion. -/
theorem momentPolynomial_cons (τ : PartialType Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    momentPolynomial (τ ::ₘ ξ) = marginalPolynomial τ * momentPolynomial ξ := by
  simp only [momentPolynomial, Multiset.map_cons, Multiset.prod_cons]

/-- A first-order Leibniz map distributes over a configuration moment carrier by carrier:
`D H_ξ = Σ_{τ ∈ ξ} D(x[τ]) H_{ξ − τ}`. -/
theorem leibniz_momentPolynomial
    (D : FrequencyPolynomial Deme Locus Allele → FrequencyPolynomial Deme Locus Allele)
    (hmul : ∀ f h, D (f * h) = f * D h + h * D f) (hone : D 1 = 0)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    D (momentPolynomial ξ)
      = (ξ.map fun τ ↦ D (marginalPolynomial τ) * momentPolynomial (ξ.erase τ)).sum := by
  induction ξ using Multiset.induction_on with
  | empty => simp [momentPolynomial, hone]
  | cons τ ζ ih =>
    have hrest : (ζ.map fun σ ↦ D (marginalPolynomial σ) * momentPolynomial ((τ ::ₘ ζ).erase σ))
        = ζ.map fun σ ↦
          marginalPolynomial τ * (D (marginalPolynomial σ) * momentPolynomial (ζ.erase σ)) := by
      refine Multiset.map_congr rfl fun σ hσ ↦ ?_
      rw [Multiset.erase_cons_tail_of_mem hσ, momentPolynomial_cons]
      ring
    rw [momentPolynomial_cons, hmul, ih, Multiset.map_cons, Multiset.sum_cons,
      Multiset.erase_cons_head, hrest, Multiset.sum_map_mul_left]
    ring

/-- **The generator of a configuration moment.**  `L H_ξ` is the sum over carriers `τ` of
`L x[τ] · H_{ξ − τ}` plus the sum over ordered pairs of distinct carriers `(τ, σ)` of half the
carré du champ of `x[τ]` and `x[σ]` times `H_{ξ − τ − σ}`. -/
theorem neutralGenerator_momentPolynomial (rates : NeutralRates Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    neutralGenerator rates (momentPolynomial ξ)
      = (ξ.map fun τ ↦
          neutralGenerator rates (marginalPolynomial τ) * momentPolynomial (ξ.erase τ)).sum
        + (ξ.map fun τ ↦ ((ξ.erase τ).map fun σ ↦
            halfCovariance rates (marginalPolynomial τ) (marginalPolynomial σ)
              * momentPolynomial ((ξ.erase τ).erase σ)).sum).sum := by
  induction ξ using Multiset.induction_on with
  | empty => simp [momentPolynomial, neutralGenerator_one]
  | cons τ ζ ih =>
    have hleft : halfCovariance rates (marginalPolynomial τ) (momentPolynomial ζ)
        = (ζ.map fun σ ↦ halfCovariance rates (marginalPolynomial τ) (marginalPolynomial σ)
            * momentPolynomial (ζ.erase σ)).sum :=
      leibniz_momentPolynomial (halfCovariance rates (marginalPolynomial τ))
        (fun f h ↦ halfCovariance_mul_right rates _ f h) (halfCovariance_one_right rates _) ζ
    have hright : halfCovariance rates (momentPolynomial ζ) (marginalPolynomial τ)
        = (ζ.map fun σ ↦ halfCovariance rates (marginalPolynomial σ) (marginalPolynomial τ)
            * momentPolynomial (ζ.erase σ)).sum :=
      leibniz_momentPolynomial (fun f ↦ halfCovariance rates f (marginalPolynomial τ))
        (fun f h ↦ halfCovariance_mul_left rates f h _) (halfCovariance_one_left rates _) ζ
    have hfirst : (ζ.map fun σ ↦
          neutralGenerator rates (marginalPolynomial σ) * momentPolynomial ((τ ::ₘ ζ).erase σ))
        = ζ.map fun σ ↦ marginalPolynomial τ *
          (neutralGenerator rates (marginalPolynomial σ) * momentPolynomial (ζ.erase σ)) := by
      refine Multiset.map_congr rfl fun σ hσ ↦ ?_
      rw [Multiset.erase_cons_tail_of_mem hσ, momentPolynomial_cons]
      ring
    have hsecond : (ζ.map fun σ ↦ (((τ ::ₘ ζ).erase σ).map fun ρ ↦
          halfCovariance rates (marginalPolynomial σ) (marginalPolynomial ρ)
            * momentPolynomial (((τ ::ₘ ζ).erase σ).erase ρ)).sum)
        = ζ.map fun σ ↦
          halfCovariance rates (marginalPolynomial σ) (marginalPolynomial τ)
              * momentPolynomial (ζ.erase σ)
            + ((ζ.erase σ).map fun ρ ↦ marginalPolynomial τ *
                (halfCovariance rates (marginalPolynomial σ) (marginalPolynomial ρ)
                  * momentPolynomial ((ζ.erase σ).erase ρ))).sum := by
      refine Multiset.map_congr rfl fun σ hσ ↦ ?_
      rw [Multiset.erase_cons_tail_of_mem hσ, Multiset.map_cons, Multiset.sum_cons,
        Multiset.erase_cons_head]
      congr 1
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun ρ hρ ↦ ?_)
      rw [Multiset.erase_cons_tail_of_mem hρ, momentPolynomial_cons]
      ring
    rw [momentPolynomial_cons, neutralGenerator_mul, ih, hleft, hright]
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    rw [hfirst, hsecond]
    simp only [Multiset.sum_map_add, Multiset.sum_map_mul_left]
    ring

/-! ## Linear coordinates -/

/-- The partial derivative of a marginal frequency polynomial is the indicator of the
haplotypes it counts. -/
theorem pderiv_assignmentPolynomial (d : Deme) (g : FullHaplotype Locus Allele) (i : Deme)
    (assignment : ∀ ℓ, Option (Allele ℓ)) :
    pderiv (d, g) (assignmentPolynomial i assignment)
      = if d = i ∧ Satisfies assignment g then 1 else 0 := by
  unfold assignmentPolynomial
  rw [map_sum]
  by_cases hc : d = i ∧ Satisfies assignment g
  · obtain ⟨rfl, hsat⟩ := hc
    rw [if_pos ⟨rfl, hsat⟩, Finset.sum_eq_single g]
    · exact pderiv_X_self _
    · intro hap _ hne
      exact pderiv_X_of_ne fun heq ↦ hne (congrArg Prod.snd heq)
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsat⟩) hnot
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun hap hhap ↦ pderiv_X_of_ne fun heq ↦ hc ?_
    obtain ⟨hdeme, hhap'⟩ := Prod.mk.inj heq
    refine ⟨hdeme.symm, ?_⟩
    rw [← hhap']
    exact (Finset.mem_filter.mp hhap).2

/-- Marginal frequency polynomials are linear, so their second partial derivatives vanish. -/
theorem pderiv_pderiv_assignmentPolynomial (u : FrequencyVariable Deme Locus Allele) (d : Deme)
    (g : FullHaplotype Locus Allele) (i : Deme) (assignment : ∀ ℓ, Option (Allele ℓ)) :
    pderiv u (pderiv (d, g) (assignmentPolynomial i assignment)) = 0 := by
  rw [pderiv_assignmentPolynomial]
  split_ifs
  · exact pderiv_one
  · exact map_zero _

/-- **The generator of a linear coordinate is its drift.**  The generator of a marginal
frequency polynomial is the sum of the drifts of the haplotype frequencies it counts; the
Wright–Fisher part contributes nothing because the polynomial is linear. -/
theorem neutralGenerator_assignmentPolynomial (rates : NeutralRates Deme Locus Allele)
    (i : Deme) (assignment : ∀ ℓ, Option (Allele ℓ)) :
    neutralGenerator rates (assignmentPolynomial i assignment)
      = ∑ hap ∈ Finset.univ.filter (Satisfies assignment), driftPolynomial rates (i, hap) := by
  have hsecond : ∀ d : Deme, demeSecondOrder d (assignmentPolynomial i assignment) = 0 := by
    intro d
    simp only [demeSecondOrder, pderiv_pderiv_assignmentPolynomial, mul_zero,
      Finset.sum_const_zero, sub_self]
  simp only [neutralGenerator, hsecond, mul_zero, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp only [pderiv_assignmentPolynomial, eq_self_iff_true, true_and, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_filter]
  · intro d _ hd
    refine Finset.sum_eq_zero fun hap _ ↦ ?_
    rw [pderiv_assignmentPolynomial, if_neg fun hc ↦ hd hc.1, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot

/-- The Wright–Fisher bilinear form of two marginal frequency polynomials: nonzero only in
their common deme, where it is the joint frequency minus the product of the marginals. -/
theorem demeCovarianceForm_assignmentPolynomial (d i j : Deme)
    (first second : ∀ ℓ, Option (Allele ℓ)) :
    demeCovarianceForm d (assignmentPolynomial i first) (assignmentPolynomial j second)
      = if d = i ∧ d = j then
          (∑ hap ∈ Finset.univ.filter (fun hap ↦ Satisfies first hap ∧ Satisfies second hap),
              (X (d, hap) : FrequencyPolynomial Deme Locus Allele))
            - assignmentPolynomial d first * assignmentPolynomial d second
        else 0 := by
  simp only [demeCovarianceForm, pderiv_assignmentPolynomial]
  by_cases hdi : d = i
  · by_cases hdj : d = j
    · rw [if_pos ⟨hdi, hdj⟩, ← hdi, ← hdj]
      simp only [eq_self_iff_true, true_and, ite_zero_mul_ite_zero, mul_one, mul_boole,
        assignmentPolynomial, Finset.sum_mul_sum, Finset.sum_filter]
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    · simp only [hdj, and_false, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero,
        sub_self]
  · simp only [hdi, false_and, ↓reduceIte, zero_mul, mul_zero, Finset.sum_const_zero, sub_self]

/-- Half of the carré du champ of two marginal frequency polynomials. -/
theorem halfCovariance_assignmentPolynomial (rates : NeutralRates Deme Locus Allele)
    (i j : Deme) (first second : ∀ ℓ, Option (Allele ℓ)) :
    halfCovariance rates (assignmentPolynomial i first) (assignmentPolynomial j second)
      = if i = j then
          C (rates.coalescence i / 2) *
            ((∑ hap ∈ Finset.univ.filter (fun hap ↦ Satisfies first hap ∧ Satisfies second hap),
                (X (i, hap) : FrequencyPolynomial Deme Locus Allele))
              - assignmentPolynomial i first * assignmentPolynomial i second)
        else 0 := by
  unfold halfCovariance
  simp only [demeCovarianceForm_assignmentPolynomial, mul_ite, mul_zero]
  by_cases hij : i = j
  · rw [if_pos hij, Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, hij⟩]
    · intro d _ hd
      rw [if_neg fun hc ↦ hd hc.1]
    · intro hnot
      exact absurd (Finset.mem_univ i) hnot
  · rw [if_neg hij]
    exact Finset.sum_eq_zero fun d _ ↦ if_neg fun hc ↦ hij (hc.1.symm.trans hc.2)

/-- Evaluating a marginal frequency polynomial sums the frequencies of the haplotypes it
counts. -/
theorem eval_assignmentPolynomial (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme)
    (assignment : ∀ ℓ, Option (Allele ℓ)) :
    eval x (assignmentPolynomial i assignment)
      = ∑ hap ∈ Finset.univ.filter (Satisfies assignment), x (i, hap) := by
  simp only [assignmentPolynomial, map_sum, eval_X]

/-- At the frequency point of per-deme haplotype laws, the marginal frequency polynomial of a
partial type evaluates to the corpus marginal frequency `x_i[A, a]`. -/
theorem eval_marginalPolynomial (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (τ : PartialType Deme Locus Allele) :
    eval (lawPoint law) (marginalPolynomial τ) = marginalFrequency law τ := by
  rw [marginalPolynomial, eval_assignmentPolynomial, marginalFrequency]
  exact Finset.sum_congr (Finset.filter_congr fun _ _ ↦ Iff.rfl) fun _ _ ↦ rfl

/-- At the frequency point of per-deme haplotype laws, the moment polynomial evaluates to the
corpus configuration moment `H_ξ` of (17). -/
theorem eval_momentPolynomial (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    eval (lawPoint law) (momentPolynomial ξ) = configurationMoment law ξ := by
  rw [momentPolynomial, configurationMoment, map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun τ _ ↦ eval_marginalPolynomial law τ

/-! ## Coalescence of compatible assignments -/

/-- A haplotype satisfies the merged assignment of two compatible partial types exactly when
it satisfies both. -/
theorem satisfies_coalesce_iff (τ σ : PartialType Deme Locus Allele) (hcompat : Compatible τ σ)
    (hap : FullHaplotype Locus Allele) :
    Satisfies (coalesce τ σ).allele hap ↔ Satisfies τ.allele hap ∧ Satisfies σ.allele hap := by
  constructor
  · intro h
    refine ⟨fun ℓ ↦ ?_, fun ℓ ↦ ?_⟩
    · cases hτ : τ.allele ℓ with
      | none => exact Or.inl rfl
      | some a =>
        have hc : (coalesce τ σ).allele ℓ = some a := by simp [coalesce, hτ]
        have h' := h ℓ
        rwa [hc] at h'
    · cases hσ : σ.allele ℓ with
      | none => exact Or.inl rfl
      | some b =>
        have hsome : (σ.allele ℓ).isSome = true := by simp [hσ]
        have hc : (coalesce τ σ).allele ℓ = some b := by
          rw [coalesce_allele_eq_of_compatible τ σ hcompat ℓ hsome, hσ]
        have h' := h ℓ
        rwa [hc] at h'
  · rintro ⟨hτ, hσ⟩ ℓ
    cases h : τ.allele ℓ with
    | none =>
      have hc : (coalesce τ σ).allele ℓ = σ.allele ℓ := by simp [coalesce, h]
      rw [hc]
      exact hσ ℓ
    | some a =>
      have hc : (coalesce τ σ).allele ℓ = some a := by simp [coalesce, h]
      rw [hc]
      have ht := hτ ℓ
      rwa [h] at ht

/-- No haplotype satisfies two incompatible partial types. -/
theorem not_satisfies_of_not_compatible (τ σ : PartialType Deme Locus Allele)
    (hnot : ¬ Compatible τ σ) (hap : FullHaplotype Locus Allele) :
    ¬ (Satisfies τ.allele hap ∧ Satisfies σ.allele hap) := by
  rintro ⟨hτ, hσ⟩
  apply hnot
  intro ℓ hτs hσs
  rcases hτ ℓ with ht | ht
  · rw [ht] at hτs
    exact absurd hτs (by simp)
  · rcases hσ ℓ with hs | hs
    · rw [hs] at hσs
      exact absurd hσs (by simp)
    · rw [ht, hs]

/-- The joint frequency of two partial types in one deme is the merged marginal frequency when
they are compatible and zero otherwise. -/
theorem jointFrequency_eq_coalesce (x : FrequencyVariable Deme Locus Allele → ℝ)
    (τ σ : PartialType Deme Locus Allele) :
    ∑ hap ∈ Finset.univ.filter (fun hap ↦ Satisfies τ.allele hap ∧ Satisfies σ.allele hap),
        x (τ.deme, hap)
      = if Compatible τ σ then eval x (marginalPolynomial (coalesce τ σ)) else 0 := by
  split_ifs with hcompat
  · rw [marginalPolynomial, eval_assignmentPolynomial]
    exact Finset.sum_congr
      (Finset.filter_congr fun hap _ ↦ (satisfies_coalesce_iff τ σ hcompat hap).symm)
      fun _ _ ↦ rfl
  · exact Finset.sum_eq_zero fun hap hhap ↦
      absurd (Finset.mem_filter.mp hhap).2 (not_satisfies_of_not_compatible τ σ hcompat hap)

/-- Half of the carré du champ of two partial-type marginal frequencies, evaluated at any
frequency point, in terms of their joint frequency. -/
theorem eval_halfCovariance_joint (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ σ : PartialType Deme Locus Allele) :
    eval x (halfCovariance rates (marginalPolynomial τ) (marginalPolynomial σ))
      = if τ.deme = σ.deme then
          rates.coalescence τ.deme / 2 *
            ((∑ hap ∈ Finset.univ.filter
                (fun hap ↦ Satisfies τ.allele hap ∧ Satisfies σ.allele hap), x (τ.deme, hap))
              - eval x (marginalPolynomial τ) * eval x (marginalPolynomial σ))
        else 0 := by
  have hτ : marginalPolynomial τ = assignmentPolynomial τ.deme τ.allele := rfl
  have hσ : marginalPolynomial σ = assignmentPolynomial σ.deme σ.allele := rfl
  rw [hτ, hσ, halfCovariance_assignmentPolynomial]
  split_ifs with hdeme
  · rw [map_mul, map_sub, map_mul, eval_C, map_sum, hdeme]
    simp only [eval_X]
  · exact map_zero _

/-- **The drift covariance of two partial-haplotype frequencies**, compatible case: in their
common deme the carré du champ is `c_i (x[A ∪ B, a ∪ b] − x[A, a] x[B, b])`. -/
theorem eval_carreDuChamp_compatible (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ σ : PartialType Deme Locus Allele)
    (hdeme : τ.deme = σ.deme) (hcompat : Compatible τ σ) :
    eval x (carreDuChamp rates (marginalPolynomial τ) (marginalPolynomial σ))
      = rates.coalescence τ.deme *
          (eval x (marginalPolynomial (coalesce τ σ))
            - eval x (marginalPolynomial τ) * eval x (marginalPolynomial σ)) := by
  have hjoint : ∑ hap ∈ Finset.univ.filter
        (fun hap ↦ Satisfies σ.allele hap ∧ Satisfies τ.allele hap), x (σ.deme, hap)
      = ∑ hap ∈ Finset.univ.filter
        (fun hap ↦ Satisfies τ.allele hap ∧ Satisfies σ.allele hap), x (τ.deme, hap) := by
    rw [hdeme]
    exact Finset.sum_congr (Finset.filter_congr fun _ _ ↦ and_comm) fun _ _ ↦ rfl
  rw [carreDuChamp, map_add, eval_halfCovariance_joint, eval_halfCovariance_joint,
    if_pos hdeme, if_pos hdeme.symm, hjoint, jointFrequency_eq_coalesce, if_pos hcompat, hdeme]
  ring

/-- **The drift covariance of two partial-haplotype frequencies**, incompatible case: in their
common deme the carré du champ is `−c_i x[A, a] x[B, b]`. -/
theorem eval_carreDuChamp_incompatible (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ σ : PartialType Deme Locus Allele)
    (hdeme : τ.deme = σ.deme) (hnot : ¬ Compatible τ σ) :
    eval x (carreDuChamp rates (marginalPolynomial τ) (marginalPolynomial σ))
      = -(rates.coalescence τ.deme *
          (eval x (marginalPolynomial τ) * eval x (marginalPolynomial σ))) := by
  have hjoint : ∑ hap ∈ Finset.univ.filter
        (fun hap ↦ Satisfies σ.allele hap ∧ Satisfies τ.allele hap), x (σ.deme, hap) = 0 := by
    rw [← hdeme]
    exact Finset.sum_eq_zero fun hap hhap ↦
      absurd (Finset.mem_filter.mp hhap).2
        ((not_satisfies_of_not_compatible τ σ hnot hap) ∘ And.symm)
  rw [carreDuChamp, map_add, eval_halfCovariance_joint, eval_halfCovariance_joint,
    if_pos hdeme, if_pos hdeme.symm, hjoint, jointFrequency_eq_coalesce, if_neg hnot, hdeme]
  ring

end

end Descent.Portability.PartialHaplotypeDualGenerator

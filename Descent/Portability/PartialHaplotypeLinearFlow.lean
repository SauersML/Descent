/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualSemigroup

assert_below Descent.Decision Descent.Program

/-!
# The migration–mutation flow satisfies the forward moment equation

`PartialHaplotypeDualSemigroup.expectedMomentVector_eq_matrixExponential` (NOTE1 (20)) takes the
forward moment equation of an expectation family as a hypothesis.  This module constructs a
family that satisfies it, with no hypothesis beyond the form of the rates: neutral rates without
coalescence and without recombination.  For such rates the neutral generator is a linear
first-order operator (`neutralGenerator_of_coalescence_zero`,
`eval_driftPolynomial_of_recombination_zero`), so the population moves deterministically along
the linear flow `x' = A x` of migration and mutation (`linearDriftMatrix`, `flowPoint`).

The flow `x(t) = e^{tA} x(0)` stays in the multi-deme simplex.  The matrix `A` is Metzler
(`linearDriftMatrix_isMetzler`), so its exponential is entrywise nonnegative; and the deme totals
intertwine `A` with the conservative migration generator on demes
(`demeProjection_mul_linearDriftMatrix`), so every deme total stays one
(`demeTotals_flowPoint`).  The flow is therefore a path of per-deme haplotype laws (`flowLaw`),
and the Dirac expectation at the flow (`flowExpectation`) satisfies the forward moment equation
at every configuration by the chain rule for polynomial evaluation (`hasDerivAt_eval_path`,
`flowExpectation_forward`).  NOTE1 (20) then holds without hypotheses:
`e^{tQ} H(x(0)) = H(x(t))` (`flowMoments_eq_matrixExponential`), for instance at unit migration
and mutation rates (`migrationMutationRates`).

Scope.  Coalescence and recombination are zero here.  With coalescence the population law is not
a point mass, and the expectation family is the law of the neutral diffusion, whose construction
is NOTE1 §4.2a; with recombination the flow is nonlinear and is not constructed here.

## Empirical status

None.  The bodies here are algebra and calculus: a matrix exponential of supplied rates and the
derivative of polynomials along it, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeLinearFlow

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open SubstochasticGeneratorSemigroup Descent.Coalescent Descent.Foundations MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- **The chain rule for polynomial evaluation.**  Along a differentiable path of frequency
vectors, the value of a frequency polynomial has derivative `Σ_v ∂_v p · velocity_v`. -/
theorem hasDerivAt_eval_path (p : FrequencyPolynomial Deme Locus Allele)
    (path : ℝ → FrequencyVariable Deme Locus Allele → ℝ)
    (velocity : FrequencyVariable Deme Locus Allele → ℝ) (t : ℝ)
    (hpath : HasDerivAt path velocity t) :
    HasDerivAt (fun s ↦ eval (path s) p) (∑ v, eval (path t) (pderiv v p) * velocity v) t := by
  refine MvPolynomial.induction_on
    (motive := fun q ↦ HasDerivAt (fun s ↦ eval (path s) q)
      (∑ v, eval (path t) (pderiv v q) * velocity v) t) p ?_ ?_ ?_
  · intro a
    simp only [eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const (x := t) (c := a)
  · intro q r hq hr
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hq.add hr
  · intro q n hq
    show HasDerivAt (fun s ↦ eval (path s) (q * X n))
      (∑ v, eval (path t) (pderiv v (q * X n)) * velocity v) t
    have hderiv : ∑ v, eval (path t) (pderiv v (q * X n)) * velocity v
        = (∑ v, eval (path t) (pderiv v q) * velocity v) * path t n
          + eval (path t) q * velocity n := by
      simp only [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [eval_X]
        ring
      · rw [Finset.sum_eq_single n]
        · simp
        · intro v _ hv
          simp [pderiv_X_of_ne (Ne.symm hv)]
        · intro hn
          exact absurd (Finset.mem_univ n) hn
    rw [hderiv]
    simpa only [map_mul, eval_X] using hq.mul (hasDerivAt_pi.mp hpath n)

/-- Without coalescence the neutral generator is the first-order drift derivative. -/
theorem neutralGenerator_of_coalescence_zero (rates : NeutralRates Deme Locus Allele)
    (hcoal : ∀ i, rates.coalescence i = 0) (f : FrequencyPolynomial Deme Locus Allele) :
    neutralGenerator rates f = ∑ v, driftPolynomial rates v * pderiv v f := by
  simp [neutralGenerator, hcoal]

/-- The migration part of the linear drift: haplotype `h` of deme `i` receives migrants from
every deme `j` at the backward rate `m_{ij}`. -/
def migrationDriftMatrix (rates : NeutralRates Deme Locus Allele) :
    Matrix (FrequencyVariable Deme Locus Allele) (FrequencyVariable Deme Locus Allele) ℝ :=
  fun u w ↦ if w.2 = u.2 then
    rates.migration u.1 w.1 - (if w.1 = u.1 then ∑ j, rates.migration u.1 j else 0) else 0

/-- The mutation part of the linear drift: mutational inflow into `h` from every relabelling of
one of its sites, and outflow from `h` at the total mutation rate of its alleles. -/
def mutationDriftMatrix (rates : NeutralRates Deme Locus Allele) :
    Matrix (FrequencyVariable Deme Locus Allele) (FrequencyVariable Deme Locus Allele) ℝ :=
  fun u w ↦ (∑ ℓ, ∑ b : Allele ℓ,
      if w = (u.1, Function.update u.2 ℓ b) then rates.mutation ℓ b (u.2 ℓ) else 0)
    - if w = u then ∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ (u.2 ℓ) b else 0

/-- The linear drift matrix of migration and mutation. -/
def linearDriftMatrix (rates : NeutralRates Deme Locus Allele) :
    Matrix (FrequencyVariable Deme Locus Allele) (FrequencyVariable Deme Locus Allele) ℝ :=
  migrationDriftMatrix rates + mutationDriftMatrix rates

/-- The migration drift matrix acting on a frequency vector. -/
theorem migrationDriftMatrix_mulVec (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (u : FrequencyVariable Deme Locus Allele) :
    (migrationDriftMatrix rates).mulVec x u
      = ∑ j, rates.migration u.1 j * (x (j, u.2) - x u) := by
  have hinner : ∀ d : Deme,
      ∑ g : FullHaplotype Locus Allele, migrationDriftMatrix rates u (d, g) * x (d, g)
        = (rates.migration u.1 d - if d = u.1 then ∑ j, rates.migration u.1 j else 0)
          * x (d, u.2) := by
    intro d
    rw [Finset.sum_eq_single u.2]
    · simp [migrationDriftMatrix]
    · intro g _ hg
      simp [migrationDriftMatrix, hg]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have hdiag : ∑ d : Deme, (if d = u.1 then ∑ j, rates.migration u.1 j else 0) * x (d, u.2)
      = ∑ j, rates.migration u.1 j * x u := by
    rw [Finset.sum_eq_single u.1]
    · simp [Finset.sum_mul]
    · intro d _ hd
      simp [hd]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp only [hinner, sub_mul, Finset.sum_sub_distrib, hdiag, mul_sub]

/-- The mutation drift matrix acting on a frequency vector. -/
theorem mutationDriftMatrix_mulVec (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (u : FrequencyVariable Deme Locus Allele) :
    (mutationDriftMatrix rates).mulVec x u
      = ∑ ℓ, ∑ b : Allele ℓ,
          (rates.mutation ℓ b (u.2 ℓ) * x (u.1, Function.update u.2 ℓ b)
            - rates.mutation ℓ (u.2 ℓ) b * x u) := by
  have hentry : ∀ w : FrequencyVariable Deme Locus Allele,
      mutationDriftMatrix rates u w * x w
        = (∑ ℓ, ∑ b : Allele ℓ,
            if w = (u.1, Function.update u.2 ℓ b) then rates.mutation ℓ b (u.2 ℓ) * x w else 0)
          - if w = u then (∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ (u.2 ℓ) b) * x w else 0 := by
    intro w
    simp only [mutationDriftMatrix, sub_mul, Finset.sum_mul, ite_mul, zero_mul]
  have hswap : ∑ w : FrequencyVariable Deme Locus Allele, ∑ ℓ, ∑ b : Allele ℓ,
        (if w = (u.1, Function.update u.2 ℓ b) then rates.mutation ℓ b (u.2 ℓ) * x w else 0)
      = ∑ ℓ, ∑ b : Allele ℓ,
          rates.mutation ℓ b (u.2 ℓ) * x (u.1, Function.update u.2 ℓ b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_ite_eq']
    simp
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl fun w _ ↦ hentry w, Finset.sum_sub_distrib, hswap, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte, Finset.sum_mul, Finset.sum_sub_distrib]

/-- **Without recombination the drift is linear.**  The drift polynomial of a frequency
coordinate evaluates to the linear drift matrix applied to the frequency vector. -/
theorem eval_driftPolynomial_of_recombination_zero (rates : NeutralRates Deme Locus Allele)
    (hrec : ∀ selector, rates.recombination selector = 0)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (u : FrequencyVariable Deme Locus Allele) :
    eval x (driftPolynomial rates u) = (linearDriftMatrix rates).mulVec x u := by
  rw [linearDriftMatrix, Matrix.add_mulVec, Pi.add_apply, migrationDriftMatrix_mulVec,
    mutationDriftMatrix_mulVec]
  simp only [driftPolynomial, hrec, map_zero, zero_mul, Finset.sum_const_zero, add_zero, map_add,
    map_sum, map_mul, map_sub, eval_C, eval_X]

/-- The linear drift matrix is Metzler: every off-diagonal entry is a nonnegative rate. -/
theorem linearDriftMatrix_isMetzler (rates : NeutralRates Deme Locus Allele) :
    Matrix.IsMetzler (linearDriftMatrix rates) := by
  intro u w hne
  have hmigration : 0 ≤ migrationDriftMatrix rates u w := by
    simp only [migrationDriftMatrix]
    split_ifs with hsecond hfirst
    · exact absurd (Prod.ext hfirst hsecond).symm hne
    · simpa using rates.migration_nonneg u.1 w.1
    · exact le_rfl
  have hmutation : 0 ≤ mutationDriftMatrix rates u w := by
    simp only [mutationDriftMatrix, if_neg (Ne.symm hne), sub_zero]
    exact Finset.sum_nonneg fun ℓ _ ↦ Finset.sum_nonneg fun b _ ↦ by
      split_ifs
      · exact rates.mutation_nonneg _ _ _
      · exact le_rfl
  simpa [linearDriftMatrix] using add_nonneg hmigration hmutation

/-- The deme totals of a frequency vector. -/
def demeTotals (x : FrequencyVariable Deme Locus Allele → ℝ) : Deme → ℝ :=
  fun i ↦ ∑ hap, x (i, hap)

/-- The conservative migration generator on deme totals. -/
def demeMigrationMatrix (rates : NeutralRates Deme Locus Allele) : Matrix Deme Deme ℝ :=
  fun i j ↦ rates.migration i j - if j = i then ∑ k, rates.migration i k else 0

/-- The deme totals of the linear drift are the migration generator applied to the deme totals:
mutation conserves every deme total and migration exchanges totals between demes. -/
theorem demeTotals_linearDrift (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) :
    demeTotals ((linearDriftMatrix rates).mulVec x)
      = (demeMigrationMatrix rates).mulVec (demeTotals x) := by
  have hall : Finset.univ.filter (Satisfies fun ℓ ↦ (none : Option (Allele ℓ)))
      = (Finset.univ : Finset (FullHaplotype Locus Allele)) :=
    Finset.filter_true_of_mem fun _ _ _ ↦ Or.inl rfl
  have htotal : ∀ j, eval x (assignmentPolynomial j fun ℓ ↦ (none : Option (Allele ℓ)))
      = demeTotals x j := by
    intro j
    rw [eval_assignmentPolynomial, hall]
    rfl
  funext i
  have hmigration := sum_migrationDrift rates x i fun ℓ ↦ (none : Option (Allele ℓ))
  rw [hall] at hmigration
  simp only [htotal] at hmigration
  have hmutation : ∀ ℓ, ∑ hap : FullHaplotype Locus Allele, ∑ b : Allele ℓ,
      (rates.mutation ℓ b (hap ℓ) * x (i, Function.update hap ℓ b)
        - rates.mutation ℓ (hap ℓ) b * x (i, hap)) = 0 := by
    intro ℓ
    have h := mutationDrift_unassigned rates x i (fun ℓ ↦ (none : Option (Allele ℓ))) ℓ rfl
    rwa [hall] at h
  show ∑ hap, (linearDriftMatrix rates).mulVec x (i, hap)
    = (demeMigrationMatrix rates).mulVec (demeTotals x) i
  simp only [linearDriftMatrix, Matrix.add_mulVec, Pi.add_apply, migrationDriftMatrix_mulVec,
    mutationDriftMatrix_mulVec, Finset.sum_add_distrib]
  rw [hmigration, Finset.sum_comm, Finset.sum_congr rfl fun ℓ _ ↦ hmutation ℓ,
    Finset.sum_const_zero, add_zero]
  simp only [Matrix.mulVec, dotProduct, demeMigrationMatrix, sub_mul, Finset.sum_sub_distrib,
    mul_sub, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_mul]

/-- The projection of frequency vectors onto deme totals. -/
def demeProjection : Matrix Deme (FrequencyVariable Deme Locus Allele) ℝ :=
  fun i w ↦ if w.1 = i then 1 else 0

/-- The deme projection computes deme totals. -/
theorem demeProjection_mulVec (x : FrequencyVariable Deme Locus Allele → ℝ) :
    (demeProjection (Locus := Locus) (Allele := Allele)).mulVec x = demeTotals x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, demeProjection, demeTotals]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp
  · intro d _ hd
    simp [hd]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- The deme projection intertwines the linear drift with the migration generator on demes. -/
theorem demeProjection_mul_linearDriftMatrix (rates : NeutralRates Deme Locus Allele) :
    demeProjection * linearDriftMatrix rates = demeMigrationMatrix rates * demeProjection := by
  ext i w
  have h := congrFun (demeTotals_linearDrift rates (Pi.single w 1)) i
  rw [← demeProjection_mulVec, ← demeProjection_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

/-- The migration–mutation flow started from the frequency point of per-deme haplotype laws. -/
def flowPoint (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) :
    FrequencyVariable Deme Locus Allele → ℝ :=
  (matrixExponential (linearDriftMatrix rates) t).mulVec (lawPoint law0)

/-- The flow keeps every frequency nonnegative at nonnegative times. -/
theorem flowPoint_nonneg (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) (ht : 0 ≤ t)
    (u : FrequencyVariable Deme Locus Allele) : 0 ≤ flowPoint rates law0 t u := by
  show 0 ≤ ∑ w, matrixExponential (linearDriftMatrix rates) t u w * lawPoint law0 w
  exact Finset.sum_nonneg fun w _ ↦ mul_nonneg
    (matrixExponential_apply_nonneg_of_metzler _ (linearDriftMatrix_isMetzler rates) t ht u w)
    ((law0 w.1).mass_nonneg w.2)

/-- The flow keeps every deme total equal to one. -/
theorem demeTotals_flowPoint (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) :
    demeTotals (flowPoint rates law0 t) = fun _ ↦ (1 : ℝ) := by
  have hinter := matrixExponential_intertwines demeProjection (linearDriftMatrix rates)
    (demeMigrationMatrix rates) (demeProjection_mul_linearDriftMatrix rates) t
  have hstart : demeTotals (lawPoint law0) = fun _ ↦ (1 : ℝ) := by
    funext i
    exact (law0 i).mass_sum
  have hzero : ∀ i, ∑ j, demeMigrationMatrix rates i j = 0 := by
    intro i
    simp [demeMigrationMatrix, Finset.sum_sub_distrib]
  rw [flowPoint, ← demeProjection_mulVec, Matrix.mulVec_mulVec, hinter, ← Matrix.mulVec_mulVec,
    demeProjection_mulVec, hstart, matrixExponential_mulVec_const _ hzero]

/-- The per-deme haplotype laws along the flow; negative times are clamped to time zero. -/
def flowLaw (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) :
    Deme → FiniteReportLaw (FullHaplotype Locus Allele) :=
  fun i ↦
    { mass := fun hap ↦ flowPoint rates law0 (max t 0) (i, hap)
      mass_nonneg := fun hap ↦ flowPoint_nonneg rates law0 (max t 0) (le_max_right t 0) (i, hap)
      mass_sum := congrFun (demeTotals_flowPoint rates law0 (max t 0)) i }

/-- The frequency point of the flow laws is the flow at the clamped time. -/
theorem lawPoint_flowLaw (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) :
    lawPoint (flowLaw rates law0 t) = flowPoint rates law0 (max t 0) :=
  rfl

/-- The Dirac expectation at the flow. -/
def flowExpectation (rates : NeutralRates Deme Locus Allele)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (t : ℝ) :
    ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :=
  ExpFunctional.evalAt (flowLaw rates law0 t)

/-- **The flow satisfies the forward moment equation.**  For neutral rates without coalescence
and without recombination, the Dirac expectation at the migration–mutation flow has, at every
configuration and every time `t ≥ 0`, right derivative equal to the expected neutral generator of
the moment polynomial. -/
theorem flowExpectation_forward (rates : NeutralRates Deme Locus Allele)
    (hcoal : ∀ i, rates.coalescence i = 0) (hrec : ∀ selector, rates.recombination selector = 0)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (capacity : Locus → ℕ) :
    ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity (flowExpectation rates law0) s ξ)
        (flowExpectation rates law0 t fun law ↦
          eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        (Set.Ici 0) t := by
  intro ξ t ht
  have hmax : max t 0 = t := max_eq_left ht
  have hpath : HasDerivAt (flowPoint rates law0)
      ((linearDriftMatrix rates).mulVec (flowPoint rates law0 t)) t :=
    StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec _ _ t
  have heval := hasDerivAt_eval_path (momentPolynomial ξ.1) (flowPoint rates law0) _ t hpath
  have hderiv : ∑ v, eval (flowPoint rates law0 t) (pderiv v (momentPolynomial ξ.1))
        * (linearDriftMatrix rates).mulVec (flowPoint rates law0 t) v
      = eval (flowPoint rates law0 t) (neutralGenerator rates (momentPolynomial ξ.1)) := by
    rw [neutralGenerator_of_coalescence_zero rates hcoal, map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [map_mul, eval_driftPolynomial_of_recombination_zero rates hrec, mul_comm]
  have hvalue : (flowExpectation rates law0 t fun law ↦
        eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
      = eval (flowPoint rates law0 t) (neutralGenerator rates (momentPolynomial ξ.1)) := by
    show eval (lawPoint (flowLaw rates law0 t)) _ = _
    rw [lawPoint_flowLaw, hmax]
  rw [hvalue, ← hderiv]
  refine heval.hasDerivWithinAt.congr (fun s hs ↦ ?_) ?_
  · show configurationMoment (flowLaw rates law0 s) ξ.1
      = eval (flowPoint rates law0 s) (momentPolynomial ξ.1)
    rw [← eval_momentPolynomial, lawPoint_flowLaw, max_eq_left hs]
  · show configurationMoment (flowLaw rates law0 t) ξ.1
      = eval (flowPoint rates law0 t) (momentPolynomial ξ.1)
    rw [← eval_momentPolynomial, lawPoint_flowLaw, hmax]

/-- **NOTE1 (20) without hypotheses, for migration and mutation.**  For neutral rates without
coalescence and without recombination, the dual propagator applied to the configuration moments
of the initial laws gives the configuration moments of the laws along the migration–mutation
flow. -/
theorem flowMoments_eq_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (hcoal : ∀ i, rates.coalescence i = 0) (hrec : ∀ selector, rates.recombination selector = 0)
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (capacity : Locus → ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (fun ξ : BudgetConfiguration Deme Locus Allele capacity ↦
        configurationMoment (flowLaw rates law0 t) ξ.1)
      = (matrixExponential (dualGenerator rates capacity) t).mulVec
          (fun ξ ↦ configurationMoment law0 ξ.1) := by
  have h := expectedMomentVector_eq_matrixExponential rates capacity (flowExpectation rates law0)
    (flowExpectation_forward rates hcoal hrec law0 capacity) t ht
  have hstart : flowLaw rates law0 0 = law0 := by
    funext i
    ext hap
    show flowPoint rates law0 (max 0 0) (i, hap) = (law0 i).mass hap
    rw [max_self, flowPoint, matrixExponential_zero, Matrix.one_mulVec]
    rfl
  have hinitial : (fun ξ : BudgetConfiguration Deme Locus Allele capacity ↦
        configurationMoment law0 ξ.1)
      = expectedMomentVector capacity (flowExpectation rates law0) 0 := by
    funext ξ
    show configurationMoment law0 ξ.1 = configurationMoment (flowLaw rates law0 0) ξ.1
    rw [hstart]
  rw [hinitial]
  exact h

/-- Unit migration and mutation rates with no coalescence and no recombination. -/
def migrationMutationRates : NeutralRates Deme Locus Allele where
  coalescence _ := 0
  migration _ _ := 1
  recombination _ := 0
  mutation _ _ _ := 1
  coalescence_nonneg _ := le_rfl
  migration_nonneg _ _ := zero_le_one
  recombination_nonneg _ := le_rfl
  mutation_nonneg _ _ _ := zero_le_one
  mutation_symm _ _ _ := rfl

/-- NOTE1 (20) at unit migration and mutation rates, with no hypothesis at all. -/
theorem migrationMutationRates_moments
    (law0 : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) (capacity : Locus → ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (fun ξ : BudgetConfiguration Deme Locus Allele capacity ↦
        configurationMoment (flowLaw migrationMutationRates law0 t) ξ.1)
      = (matrixExponential (dualGenerator migrationMutationRates capacity) t).mulVec
          (fun ξ ↦ configurationMoment law0 ξ.1) :=
  flowMoments_eq_matrixExponential migrationMutationRates (fun _ ↦ rfl) (fun _ ↦ rfl) law0
    capacity t ht

end

end Descent.Portability.PartialHaplotypeLinearFlow

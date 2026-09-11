/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
# The exact finite genetic transition and the end-to-end report law

The evolutionary transition of a finite diploid population is built here as an actual
composition of its primitives: fitness-weighted parent selection, a strand path drawn from a
specified recombination law, Mendelian segregation of the chosen parental strands, an
independent per-locus mutation kernel, and independent offspring. Every stage is a
`FiniteReportLaw`, so row stochasticity of the resulting kernel is a consequence of the
construction rather than a separate hypothesis, and the strictly positive fitness sums are
the only denominators anywhere in it. No linkage-disequilibrium approximation occurs: the
state retains every haplotype.

Composing that kernel with the specified sampling, training and evaluation kernel gives the
exact end-to-end report law, its exact expectation of every bounded report statistic, its
explicit sum over complete histories, and the fact that those path probabilities determine
it uniquely.

This is TQ Theorem 6.1, TQ Theorem 6.2 (6.3) and UPT Theorem 8.1 (8.1)-(8.2) in the finite
case. It builds on `ExactFiniteHistoryLaw.propagate`, `pathMass`, `path_sum_eq_expectation`
and `path_mass_sum_one`, and adds the independent product law, the fitness-selection law,
the joint path law as an object, and the genetic kernel itself.

The hypotheses are the manuscript's domain conditions: finitely many loci, individuals and
offspring, and strictly positive fitness. Continuous exposures, continuous effect values and
unbounded mutation-created genomes are not covered by this finite construction, exactly as
the manuscript states.

## Empirical status

None. The bodies here are algebra: the fitnesses, the recombination law and the mutation
kernels are supplied inputs, and what carries an empirical status is a named quantity in a
subsystem module asserting that this algebra computes something measurable. Those names keep
their own docstrings, their own regimes, and their own ledger rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteGeneticTransition

open ExactFiniteHistoryLaw

noncomputable section

/-- The independent product of finitely many finite laws. This is the repeated finite
summation that makes every product stage of the genetic transition normalized. -/
def piLaw {I : Type*} [Fintype I] [DecidableEq I] {V : I → Type*} [∀ i, Fintype (V i)]
    (law : ∀ i, FiniteReportLaw (V i)) : FiniteReportLaw (∀ i, V i) where
  mass := fun assignment ↦ ∏ i, (law i).mass (assignment i)
  mass_nonneg := fun assignment ↦
    Finset.prod_nonneg fun i _ ↦ (law i).mass_nonneg (assignment i)
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp [FiniteReportLaw.mass_sum]

/-- The independent product law assigns exactly the product of the coordinate masses. -/
theorem piLaw_mass {I : Type*} [Fintype I] [DecidableEq I] {V : I → Type*}
    [∀ i, Fintype (V i)] (law : ∀ i, FiniteReportLaw (V i)) (assignment : ∀ i, V i) :
    (piLaw law).mass assignment = ∏ i, (law i).mass (assignment i) := rfl

/-- Fitness-weighted selection. The strictly positive fitness sum is the only denominator
in the whole transition. -/
def selectionLaw {I : Type*} [Fintype I] [Nonempty I] (fitness : I → ℝ)
    (hfit : ∀ i, 0 < fitness i) : FiniteReportLaw I where
  mass := fun i ↦ fitness i / ∑ k, fitness k
  mass_nonneg := fun i ↦
    div_nonneg (hfit i).le (Finset.sum_nonneg fun k _ ↦ (hfit k).le)
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun k _ ↦ hfit k) Finset.univ_nonempty))

/-- The selection law's mass is exactly the relative fitness. -/
theorem selectionLaw_mass {I : Type*} [Fintype I] [Nonempty I] (fitness : I → ℝ)
    (hfit : ∀ i, 0 < fitness i) (i : I) :
    (selectionLaw fitness hfit).mass i = fitness i / ∑ k, fitness k := rfl

variable {State : Type*} [Fintype State]

/-- Complete finite histories carry nonnegative probability. -/
theorem pathMass_nonneg (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) :
    ∀ (n : ℕ) (path : Path State n), 0 ≤ pathMass initial kernel path := by
  intro n
  induction n with
  | zero => exact fun path ↦ initial.mass_nonneg path
  | succ n ih =>
    intro path
    simp only [pathMass]
    exact mul_nonneg (ih path.1) ((kernel n (terminal path.1)).mass_nonneg path.2)

/-- The joint law of complete finite histories, as an object rather than a weight table.
Its normalization is derived from the constructed transitions. -/
def pathLaw (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (n : ℕ) :
    FiniteReportLaw (Path State n) where
  mass := pathMass initial kernel
  mass_nonneg := pathMass_nonneg initial kernel n
  mass_sum := path_mass_sum_one initial kernel n

section Genetics

variable {Locus Individual : Type*} [Fintype Locus] [DecidableEq Locus]
  [Fintype Individual] [DecidableEq Individual] [Nonempty Individual]

/-- Mendelian segregation: at each locus the offspring copies the parental strand the strand
path selects there. -/
def segregatedHaplotype (parent : Bool → Locus → Bool) (strand : Locus → Bool) :
    Locus → Bool := fun locus ↦ parent (strand locus) locus

/-- The gamete law at a fixed strand path: each segregated allele passes through its own
mutation kernel independently. -/
def mutatedGameteLaw (mutate : Locus → Bool → FiniteReportLaw Bool)
    (parent : Bool → Locus → Bool) (strand : Locus → Bool) :
    FiniteReportLaw (Locus → Bool) :=
  piLaw fun locus ↦ mutate locus (segregatedHaplotype parent strand locus)

/-- The complete gamete law: draw a strand path from the specified recombination law, then
segregate and mutate. -/
def gameteLaw (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool) (parent : Bool → Locus → Bool) :
    FiniteReportLaw (Locus → Bool) :=
  strandLaw.bind (mutatedGameteLaw mutate parent)

/-- One transmitted haplotype: select a parent by fitness, then form a gamete from that
parent's two strands. -/
def transmittedHaplotypeLaw (genome : Individual → Bool → Locus → Bool)
    (fitness : Individual → ℝ) (hfit : ∀ i, 0 < fitness i)
    (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool) : FiniteReportLaw (Locus → Bool) :=
  (selectionLaw fitness hfit).bind fun parent ↦ gameteLaw strandLaw mutate (genome parent)

/-- The exact finite evolutionary transition of TQ Theorem 6.1: every individual of the next
generation receives two independently transmitted haplotypes, each built by fitness-weighted
selection, recombination, segregation and mutation from the current population. -/
def geneticKernel (fitness : (Individual → Bool → Locus → Bool) → Individual → ℝ)
    (hfit : ∀ state i, 0 < fitness state i)
    (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool)
    (state : Individual → Bool → Locus → Bool) :
    FiniteReportLaw (Individual → Bool → Locus → Bool) :=
  piLaw fun _ : Individual ↦ piLaw fun _ : Bool ↦
    transmittedHaplotypeLaw state (fitness state) (hfit state) strandLaw mutate

/-- TQ Theorem 6.1: the transition's entries are the explicit finite sums and products of
the stated primitives, with the strictly positive fitness sums as their only denominators. -/
theorem geneticKernel_mass
    (fitness : (Individual → Bool → Locus → Bool) → Individual → ℝ)
    (hfit : ∀ state i, 0 < fitness state i)
    (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool)
    (state next : Individual → Bool → Locus → Bool) :
    (geneticKernel fitness hfit strandLaw mutate state).mass next =
      ∏ individual : Individual, ∏ copy : Bool, ∑ parent : Individual,
        fitness state parent / (∑ k, fitness state k) *
          ∑ strand : Locus → Bool, strandLaw.mass strand *
            ∏ locus : Locus,
              (mutate locus (state parent (strand locus) locus)).mass
                (next individual copy locus) := rfl

/-- TQ Theorem 6.1: every row of the transition sums to one, so the constructed kernel is
row stochastic. This is a consequence of the construction, not an added hypothesis. -/
theorem geneticKernel_row_sum_one
    (fitness : (Individual → Bool → Locus → Bool) → Individual → ℝ)
    (hfit : ∀ state i, 0 < fitness state i)
    (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool)
    (state : Individual → Bool → Locus → Bool) :
    ∑ next, (geneticKernel fitness hfit strandLaw mutate state).mass next = 1 :=
  (geneticKernel fitness hfit strandLaw mutate state).mass_sum

end Genetics

section EndToEnd

variable {Report : Type*} [Fintype Report]

/-- TQ (6.3) and UPT (8.1): the exact report law generated by the initial state law, the
specified evolutionary kernels, and the sampling, training and evaluation kernel. -/
def endToEndReportLaw (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (horizon : ℕ)
    (study : State → FiniteReportLaw Report) : FiniteReportLaw Report :=
  (propagate initial kernel horizon).bind study

/-- UPT (8.2): every bounded report statistic has an exact expectation, computed by
backward evaluation through the specified kernels. -/
theorem expectation_endToEndReportLaw (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (horizon : ℕ)
    (study : State → FiniteReportLaw Report) (metric : Report → ℝ) :
    (endToEndReportLaw initial kernel horizon study).expectation metric =
      initial.expectation (backwardReadout kernel horizon
        fun state ↦ (study state).expectation metric) := by
  rw [endToEndReportLaw, FiniteReportLaw.expectation_bind, expectation_propagate]

/-- TQ Theorem 6.2: the report law is the explicit sum of the chain-rule probability of each
complete history times the conditional report probability at its terminal state. -/
theorem endToEndReportLaw_mass (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (horizon : ℕ)
    (study : State → FiniteReportLaw Report) (report : Report) :
    (endToEndReportLaw initial kernel horizon study).mass report =
      ∑ path : Path State horizon,
        pathMass initial kernel path * (study (terminal path)).mass report := by
  rw [path_sum_eq_expectation initial kernel horizon
    fun state ↦ (study state).mass report]
  rfl

/-- TQ Theorem 6.2: the path probabilities fix the report law uniquely. -/
theorem endToEndReportLaw_unique (initial : FiniteReportLaw State)
    (kernel : ℕ → State → FiniteReportLaw State) (horizon : ℕ)
    (study : State → FiniteReportLaw Report) (candidate : FiniteReportLaw Report)
    (hcandidate : ∀ report, candidate.mass report =
      ∑ path : Path State horizon,
        pathMass initial kernel path * (study (terminal path)).mass report) :
    candidate = endToEndReportLaw initial kernel horizon study := by
  refine FiniteReportLaw.ext fun report ↦ ?_
  rw [hcandidate report, ← endToEndReportLaw_mass]

/-- TQ Theorem 6.2 for the constructed genetic mechanism: the end-to-end report law of the
finite genetic transition composed with the study kernel is a probability law on reports. -/
theorem genetic_endToEndReportLaw_sum_one {Locus Individual : Type*} [Fintype Locus]
    [DecidableEq Locus] [Fintype Individual] [DecidableEq Individual] [Nonempty Individual]
    (initial : FiniteReportLaw (Individual → Bool → Locus → Bool))
    (fitness : (Individual → Bool → Locus → Bool) → Individual → ℝ)
    (hfit : ∀ state i, 0 < fitness state i)
    (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool) (horizon : ℕ)
    (study : (Individual → Bool → Locus → Bool) → FiniteReportLaw Report) :
    ∑ report, (endToEndReportLaw initial
      (fun _ ↦ geneticKernel fitness hfit strandLaw mutate) horizon study).mass report = 1 :=
  (endToEndReportLaw initial
    (fun _ ↦ geneticKernel fitness hfit strandLaw mutate) horizon study).mass_sum

end EndToEnd

end

end Descent.Portability.FiniteGeneticTransition

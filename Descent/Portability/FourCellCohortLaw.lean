/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.FiniteReproductiveKernel
import Mathlib.Algebra.MvPolynomial.Basic

assert_below Descent.Decision Descent.Program

/-!
# The exact law of a permutation-invariant report on an identically distributed cohort

NOTE1 (37) states that for `n` independent target individuals drawn from one four-cell law on
score and outcome, the census vector `(N₀₀, N₀₁, N₁₀, N₁₁)` is multinomial, so every
permutation-invariant cohort report has the exact law obtained by summing multinomial masses
over census vectors. This module proves that statement for an arbitrary finite cell type, and
specialises the mass formula to the four cells `Bool × Bool` of NOTE1 (31), with the score
read off by `Prod.fst` and the outcome by `Prod.snd`.

The cohort law is the corpus independent product `FiniteGeneticTransition.piLaw` of `n` copies
of one law, and the census law is the corpus `FiniteReproductiveKernel.multinomialLaw`;
neither is redefined here. The bridge between them is `card_filter_cellCount`: the number of
cohort samples realising a prescribed census is exactly `Nat.multinomial`. That count is
proved by comparing two expansions of `(∑ cell, X cell) ^ n` in `MvPolynomial H ℕ` — the
expansion over samples and Mathlib's multinomial theorem — and reading off the coefficient of
one monomial. No counting principle is assumed.

Two consequences are recorded. `cohortReport_expectation` is (37) itself: the expectation of
any real cohort report that factors through the census equals its multinomial-weighted sum,
and `fourCell_census_mass` writes that weight in the `n!/(a! b! c! d!)` form of (37).
`pushforward_cohortCounts` states the same fact as an equality of laws, obtained from the
corpus identification theorem rather than by recomputing masses. Separately,
`report_eq_of_cohortCounts` shows that factoring through the census is no restriction on
which reports are covered: a report invariant under relabelling the cohort members is a
function of the census, because two samples with equal censuses differ by a permutation.

Not formalised here: which four-cell law arises from a given demographic history, and any
conditional-on-defined renormalisation. Those are the subject of the definedness, small-cohort
and empirical-AUC modules, which import this one.

## Empirical status

None. The bodies here are algebra: the census law of an independent product is a counting
identity about finitely many functions on a finite set, so no measurement on any cohort can
bear on it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourCellCohortLaw

open FiniteGeneticTransition FiniteReproductiveKernel

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The exact law of a cohort of `n` individuals reporting independently from one law. -/
noncomputable def cohortLaw (law : FiniteReportLaw H) (n : ℕ) : FiniteReportLaw (Fin n → H) :=
  piLaw fun _ : Fin n ↦ law

omit [DecidableEq H] in
/-- A cohort sample carries the product of its members' cell masses. -/
theorem cohortLaw_mass (law : FiniteReportLaw H) (n : ℕ) (sample : Fin n → H) :
    (cohortLaw law n).mass sample = ∏ member, law.mass (sample member) := rfl

/-- The number of cohort members whose report falls in a given cell. -/
def cellCount {n : ℕ} (sample : Fin n → H) (cell : H) : ℕ :=
  (Finset.univ.filter fun member ↦ sample member = cell).card

/-- Every multiplicative weight of a cohort sample is the product of the cell weights raised
to the observed cell counts. -/
theorem prod_eq_prod_cellCount {M : Type*} [CommMonoid M] {n : ℕ} (weight : H → M)
    (sample : Fin n → H) :
    (∏ member, weight (sample member)) = ∏ cell, weight cell ^ cellCount sample cell := by
  rw [← Finset.prod_fiberwise' (Finset.univ : Finset (Fin n)) sample weight]
  exact Finset.prod_congr rfl fun cell _ ↦ Finset.prod_const _

/-- The cell counts of a cohort of `n` individuals sum to `n`. -/
theorem sum_cellCount {n : ℕ} (sample : Fin n → H) : ∑ cell, cellCount sample cell = n := by
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := sample) (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset H))
    fun member _ ↦ Finset.mem_univ (sample member)
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard] at hfiber
  exact hfiber.symm

/-- The census of a cohort sample, as an element of the corpus count type. -/
def cohortCounts {n : ℕ} (sample : Fin n → H) : Counts H n :=
  ⟨cellCount sample, Finset.mem_piAntidiag.mpr
    ⟨sum_cellCount sample, fun cell _ ↦ Finset.mem_univ cell⟩⟩

/-- A census read as a finitely supported exponent vector, for monomial bookkeeping. -/
noncomputable def exponent (census : H → ℕ) : H →₀ ℕ :=
  Finsupp.onFinset Finset.univ census fun cell _ ↦ Finset.mem_univ cell

omit [DecidableEq H] in
/-- Distinct censuses give distinct exponent vectors. -/
theorem exponent_injective (first second : H → ℕ) (heq : exponent first = exponent second) :
    first = second := by
  funext cell
  exact congrArg (fun vector : H →₀ ℕ ↦ vector cell) heq

/-- The number of cohort samples realising a prescribed census is the multinomial coefficient
of that census. This is the combinatorial content of NOTE1 (37). -/
theorem card_filter_cellCount {n : ℕ} (census : H → ℕ) (hcensus : ∑ cell, census cell = n) :
    (Finset.univ.filter fun sample : Fin n → H ↦ cellCount sample = census).card =
      Nat.multinomial Finset.univ census := by
  have hmonomial : ∀ target : H → ℕ,
      (∏ cell, (MvPolynomial.X cell : MvPolynomial H ℕ) ^ target cell) =
        MvPolynomial.monomial (exponent target) 1 := by
    intro target
    have hsupport : (∏ cell ∈ (exponent target).support,
        (MvPolynomial.X cell : MvPolynomial H ℕ) ^ (exponent target) cell) =
        ∏ cell, (MvPolynomial.X cell : MvPolynomial H ℕ) ^ (exponent target) cell := by
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro cell _ hcell
      have hzero : (exponent target) cell = 0 := by
        simpa [Finsupp.mem_support_iff] using hcell
      rw [hzero, pow_zero]
    rw [← MvPolynomial.prod_X_pow_eq_monomial, hsupport]
    exact Finset.prod_congr rfl fun cell _ ↦ by simp [exponent]
  have hsampleMonomial : ∀ sample : Fin n → H,
      (∏ member, (MvPolynomial.X (sample member) : MvPolynomial H ℕ)) =
        MvPolynomial.monomial (exponent (cellCount sample)) (1 : ℕ) := by
    intro sample
    rw [prod_eq_prod_cellCount (fun cell ↦ (MvPolynomial.X cell : MvPolynomial H ℕ)) sample,
      hmonomial]
  have hsample : ((∑ cell, (MvPolynomial.X cell : MvPolynomial H ℕ)) ^ n) =
      ∑ sample : Fin n → H, MvPolynomial.monomial (exponent (cellCount sample)) (1 : ℕ) := by
    have hexpand := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset H))
      fun (_ : Fin n) (cell : H) ↦ (MvPolynomial.X cell : MvPolynomial H ℕ)
    rw [Fintype.piFinset_univ] at hexpand
    have hconst : (∏ _member : Fin n, ∑ cell, (MvPolynomial.X cell : MvPolynomial H ℕ)) =
        (∑ cell, (MvPolynomial.X cell : MvPolynomial H ℕ)) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← hconst, hexpand]
    exact Finset.sum_congr rfl fun sample _ ↦ hsampleMonomial sample
  have hmultinomial : ((∑ cell, (MvPolynomial.X cell : MvPolynomial H ℕ)) ^ n) =
      ∑ target ∈ Finset.piAntidiag (Finset.univ : Finset H) n,
        (Nat.multinomial Finset.univ target : MvPolynomial H ℕ) *
          ∏ cell, (MvPolynomial.X cell : MvPolynomial H ℕ) ^ target cell :=
    Finset.sum_pow_eq_sum_piAntidiag Finset.univ _ n
  have hcoeffTerm : ∀ target : H → ℕ,
      MvPolynomial.coeff (exponent census)
          ((Nat.multinomial Finset.univ target : MvPolynomial H ℕ) *
            ∏ cell, (MvPolynomial.X cell : MvPolynomial H ℕ) ^ target cell) =
        if exponent target = exponent census then Nat.multinomial Finset.univ target else 0 := by
    intro target
    rw [hmonomial target, ← nsmul_eq_mul, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs <;> simp
  have hmem : census ∈ Finset.piAntidiag (Finset.univ : Finset H) n :=
    Finset.mem_piAntidiag.mpr ⟨hcensus, fun cell _ ↦ Finset.mem_univ cell⟩
  have hsingle : (∑ target ∈ Finset.piAntidiag (Finset.univ : Finset H) n,
      if exponent target = exponent census then
        Nat.multinomial Finset.univ target else 0) =
      if exponent census = exponent census then
        Nat.multinomial Finset.univ census else 0 := by
    refine Finset.sum_eq_single_of_mem census hmem ?_
    intro target _ hne
    exact if_neg fun heq ↦ hne (exponent_injective target census heq)
  have hindicator : ∀ sample : Fin n → H,
      (if cellCount sample = census then (1 : ℕ) else 0) =
        if exponent (cellCount sample) = exponent census then (1 : ℕ) else 0 := by
    intro sample
    by_cases hc : cellCount sample = census
    · rw [if_pos hc, if_pos (congrArg exponent hc)]
    · rw [if_neg hc, if_neg fun heq ↦ hc (exponent_injective _ _ heq)]
  calc (Finset.univ.filter fun sample : Fin n → H ↦ cellCount sample = census).card
      = ∑ sample : Fin n → H, if cellCount sample = census then (1 : ℕ) else 0 :=
        Finset.card_filter _ _
    _ = ∑ sample : Fin n → H,
          if exponent (cellCount sample) = exponent census then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl fun sample _ ↦ hindicator sample
    _ = MvPolynomial.coeff (exponent census)
          (∑ sample : Fin n → H,
            MvPolynomial.monomial (exponent (cellCount sample)) (1 : ℕ)) := by
        rw [MvPolynomial.coeff_sum]
        exact Finset.sum_congr rfl fun sample _ ↦
          (MvPolynomial.coeff_monomial _ _ _).symm
    _ = MvPolynomial.coeff (exponent census)
          (∑ target ∈ Finset.piAntidiag (Finset.univ : Finset H) n,
            (Nat.multinomial Finset.univ target : MvPolynomial H ℕ) *
              ∏ cell, (MvPolynomial.X cell : MvPolynomial H ℕ) ^ target cell) := by
        rw [← hsample, ← hmultinomial]
    _ = ∑ target ∈ Finset.piAntidiag (Finset.univ : Finset H) n,
          if exponent target = exponent census then
            Nat.multinomial Finset.univ target else 0 := by
        rw [MvPolynomial.coeff_sum]
        exact Finset.sum_congr rfl fun target _ ↦ hcoeffTerm target
    _ = Nat.multinomial Finset.univ census := by rw [hsingle, if_pos rfl]

/-- NOTE1 (37): a real cohort report that depends only on the census has expectation equal to
the multinomial-weighted sum of its values over census vectors. -/
theorem cohortReport_expectation (law : FiniteReportLaw H) (n : ℕ) (report : Counts H n → ℝ) :
    (cohortLaw law n).expectation (fun sample ↦ report (cohortCounts sample)) =
      (multinomialLaw law n).expectation report := by
  show (∑ sample, (cohortLaw law n).mass sample * report (cohortCounts sample)) =
    ∑ census, (multinomialLaw law n).mass census * report census
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → H)) cohortCounts
    fun sample ↦ (cohortLaw law n).mass sample * report (cohortCounts sample)]
  refine Finset.sum_congr rfl fun census _ ↦ ?_
  have hfiber : ∀ sample ∈ Finset.univ.filter fun s : Fin n → H ↦ cohortCounts s = census,
      (cohortLaw law n).mass sample * report (cohortCounts sample) =
        (∏ cell, law.mass cell ^ census.val cell) * report census := by
    intro sample hsample
    have hc : cohortCounts sample = census := (Finset.mem_filter.mp hsample).2
    have hval : cellCount sample = census.val := congrArg Subtype.val hc
    rw [hc, cohortLaw_mass, prod_eq_prod_cellCount, hval]
  have hcard : (Finset.univ.filter fun sample : Fin n → H ↦ cohortCounts sample = census).card =
      Nat.multinomial Finset.univ census.val := by
    rw [← card_filter_cellCount census.val (counts_sum census)]
    congr 1
    refine Finset.filter_congr ?_
    intro sample _
    exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  have hmass : (multinomialLaw law n).mass census =
      (Nat.multinomial Finset.univ census.val : ℝ) *
        ∏ cell, law.mass cell ^ census.val cell := rfl
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, nsmul_eq_mul, hcard, hmass]
  ring

/-- The census of an identically distributed cohort has exactly the corpus multinomial law. -/
theorem pushforward_cohortCounts (law : FiniteReportLaw H) (n : ℕ) :
    (cohortLaw law n).pushforward cohortCounts = multinomialLaw law n := by
  refine (FiniteReportLaw.eq_iff_all_bounded_expectations_eq _ _).mpr fun metric _ ↦ ?_
  rw [FiniteReportLaw.expectation_pushforward]
  exact cohortReport_expectation law n metric

omit [Fintype H] in
/-- Two cohort samples with the same census differ by a relabelling of the members. -/
theorem exists_perm_of_cellCount {n : ℕ} (first second : Fin n → H)
    (hcounts : cellCount first = cellCount second) :
    ∃ relabel : Equiv.Perm (Fin n), first ∘ relabel = second := by
  have hcard : ∀ cell : H, Fintype.card {member : Fin n // second member = cell} =
      Fintype.card {member : Fin n // first member = cell} := by
    intro cell
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrFun hcounts.symm cell
  refine ⟨(Equiv.sigmaFiberEquiv second).symm.trans
    ((Equiv.sigmaCongrRight fun cell ↦ Fintype.equivOfCardEq (hcard cell)).trans
      (Equiv.sigmaFiberEquiv first)), ?_⟩
  funext member
  exact (Fintype.equivOfCardEq (hcard (second member)) ⟨member, rfl⟩).property

/-- A cohort report invariant under relabelling the members is a function of the census, so
the permutation-invariance hypothesis of NOTE1 (37) restricts nothing else. -/
theorem report_eq_of_cohortCounts {n : ℕ} (report : (Fin n → H) → ℝ)
    (hinvariant : ∀ (sample : Fin n → H) (relabel : Equiv.Perm (Fin n)),
      report (sample ∘ relabel) = report sample)
    (first second : Fin n → H) (hcounts : cohortCounts first = cohortCounts second) :
    report first = report second := by
  obtain ⟨relabel, hrelabel⟩ :=
    exists_perm_of_cellCount first second (congrArg Subtype.val hcounts)
  rw [← hrelabel, hinvariant]

/-- In the four cells of NOTE1 (31) the census records `(N₀₀, N₀₁, N₁₀, N₁₁)`, summing to the
cohort size. -/
theorem fourCell_sum_cellCount {n : ℕ} (sample : Fin n → Bool × Bool) :
    cellCount sample (false, false) + cellCount sample (false, true) +
      cellCount sample (true, false) + cellCount sample (true, true) = n := by
  have hsum := sum_cellCount sample
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hsum
  omega

/-- NOTE1 (37) in the four cells of NOTE1 (31): the census mass is
`n!/(a! b! c! d!) · P₀₀^a P₀₁^b P₁₀^c P₁₁^d`. -/
theorem fourCell_census_mass (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (census : Counts (Bool × Bool) n) :
    (multinomialLaw law n).mass census =
      (Nat.factorial n : ℝ) /
          ((Nat.factorial (census.val (false, false)) : ℝ) *
            (Nat.factorial (census.val (false, true)) : ℝ) *
            (Nat.factorial (census.val (true, false)) : ℝ) *
            (Nat.factorial (census.val (true, true)) : ℝ)) *
        (law.mass (false, false) ^ census.val (false, false) *
          law.mass (false, true) ^ census.val (false, true) *
          law.mass (true, false) ^ census.val (true, false) *
          law.mass (true, true) ^ census.val (true, true)) := by
  rw [multinomialLaw_mass]
  have hfactorial : (∏ cell : Bool × Bool, (Nat.factorial (census.val cell) : ℝ)) =
      (Nat.factorial (census.val (false, false)) : ℝ) *
        (Nat.factorial (census.val (false, true)) : ℝ) *
        (Nat.factorial (census.val (true, false)) : ℝ) *
        (Nat.factorial (census.val (true, true)) : ℝ) := by
    simp only [Fintype.prod_prod_type, Fintype.prod_bool]
    ring
  have hmass : (∏ cell : Bool × Bool, law.mass cell ^ census.val cell) =
      law.mass (false, false) ^ census.val (false, false) *
        law.mass (false, true) ^ census.val (false, true) *
        law.mass (true, false) ^ census.val (true, false) *
        law.mass (true, true) ^ census.val (true, true) := by
    simp only [Fintype.prod_prod_type, Fintype.prod_bool]
    ring
  rw [hfactorial, hmass]

end Descent.Portability.FourCellCohortLaw

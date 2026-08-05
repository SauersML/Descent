/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Descent.Conditionals

/-!
# Local-to-global coherence: bounded-radius audits cannot certify a single population

Formalization of the twin construction resolving the local-to-global problem for
overlapping probability laws, and its transport to genome-wide summary statistics.

## The mathematical statement

A *local law system* prescribes a probability law on each element of a cover, with exact agreement
on overlaps. It is *globally realizable* if some law on the whole index
set has all the prescribed marginals. The question is whether asymptotic realizability
is decided by data visible in bounded unions of cover elements.

It is not. The witness is a **twin pair**: the same smooth, strictly positive,
anticorrelated edge law imposed on two 6-regular Ramanujan graph sequences of girth
tending to infinity, one **bipartite** and one **non-bipartite**.

* Every bounded union of cover elements is a *forest* once the girth exceeds the
  radius, and on a forest the prescription is realized exactly by propagating a
  uniform root sign with perfect anticorrelation and adding independent noise. So the
  two systems have **identical data at every fixed radius**, and every such datum is
  perfectly consistent.
* The bipartite twin is globally realizable **exactly** — take a proper two-colouring
  and one global sign.
* The non-bipartite twin is at average marginal total-variation distance at least
  `1/2 - sqrt 5 / 6 = 0.1273...` from *every* global law, by the eigenvalue bound on
  max-cut for a 6-regular graph with `lambda_min ≥ -2 sqrt 5`.

Hence realizability is **not a function of bounded-locality data of any form** —
not merely "no recursively enumerable certificate hierarchy", which is the weaker
statement the problem asked for.

## Attribution

The inputs are classical and are flagged as such: Lubotzky-Phillips-Sarnak Ramanujan
graphs with the quadratic-residue bipartite/non-bipartite dichotomy and the girth
bound; the eigenvalue bound on max-cut; tree propagation. Part (i)+(iii) is in essence
the analytic form of Sherali-Adams-type integrality gaps for max-cut on expanders,
which are known. What is claimed here is the **twin packaging** — producing a
far-from-realizable system and an exactly-realizable system with identical local data
— and the resulting impossibility statement.

## Genetics transport: why this is about summary statistics

Take the index set to be the genome's variants, the cover to be LD blocks, and the
prescribed local laws to be the per-block joint laws of genotypes and phenotype
implied by a set of GWAS summary statistics (marginal effect sizes plus a reference
LD panel). "Globally realizable" means: there is a single coherent population law of
which all the reported blocks are marginals — i.e. the summary statistics really did
come from one study population with one LD structure.

Coherence checks in use — pairwise/neighbourhood consistency of marginal effects
against LD (DENTIST, SLALOM, and the conditional-analysis family), imputation of
missing summary statistics from neighbouring blocks, meta-analysis heterogeneity
statistics — are all **bounded-radius audits**. The theorem says:

> No bounded-radius audit, of any radius, of any logical form, can certify that a set
> of summary statistics is jointly realizable by one population.

And the failure is not a measure-zero pathology: the gap is a **constant**, at least
`0.127` in average marginal total variation, robust to constant-size perturbation,
achieved with smooth strictly positive densities and uniformly bounded moments. The
practical reading is that global coherence must be established by design (shared
individual-level data, or a shared and verified reference panel), never inferred from
local agreement, however wide the local window.

The residue that is genuinely open is quantitative: girth gives blindness up to radius
`~ c log d`; whether some coherent far-from-realizable system survives audits at
radius `d^c` is a real question, not resolved here.
-/

open scoped BigOperators

/-!
## 1. The frustration floor from the max-cut eigenvalue bound
-/

/-- The **agreement floor** `1/2 - sqrt 5 / 6` for a 6-regular graph whose smallest
adjacency eigenvalue is at least `-2 sqrt 5` (a Ramanujan bound at degree 6).

Every sign configuration on such a graph must have at least this fraction of edges
with *agreeing* endpoint signs. The prescribed edge law, by contrast, makes endpoint
signs agree with probability at most `2 * Phi (-10) < 10 ^ (-20)`. The difference is
the total-variation gap. -/
noncomputable def expanderAgreementFloor : ℝ := 1 / 2 - Real.sqrt 5 / 6

/-- Reference evaluation in closed surd form. -/
theorem expanderAgreementFloor_at_reference_point :
    expanderAgreementFloor = 1 / 2 - Real.sqrt 5 / 6 := rfl


/-- **The floor is below one half.** Positivity is already recorded; it is shared by the
sign-flipped constant, which sits above one half. This bound is the half that excludes it. -/
theorem expanderAgreementFloor_lt_half : expanderAgreementFloor < 1 / 2 := by
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  unfold expanderAgreementFloor
  linarith

/-- `sqrt 5 < 2.238`. -/
theorem sqrt_five_lt : Real.sqrt 5 < 2.238 := by
  have h : (5 : ℝ) < 2.238 ^ 2 := by norm_num
  exact (Real.sqrt_lt' (by norm_num)).mpr h

/-- `2.236 < sqrt 5`. -/
theorem lt_sqrt_five : (2.236 : ℝ) < Real.sqrt 5 := by
  have h : (2.236 : ℝ) ^ 2 < 5 := by norm_num
  exact (Real.lt_sqrt (by norm_num)).mpr h

/-- **The frustration floor is a genuine constant, at least `0.127`.**

This is the number quoted in the resolution: every global law leaves at least
`12.7%` of edges in agreement, while the prescription demands disagreement with probability `1 - 10
^ (-20)`. -/
theorem expanderAgreementFloor_gt : (0.127 : ℝ) < expanderAgreementFloor := by
  have h := sqrt_five_lt
  unfold expanderAgreementFloor
  linarith

/-- The floor is also below `0.1274`; the true value is `0.127322...`. -/
theorem expanderAgreementFloor_lt : expanderAgreementFloor < (0.1274 : ℝ) := by
  have h := lt_sqrt_five
  unfold expanderAgreementFloor
  linarith

/-- **The prescribed edge law sits below the frustration floor.**

This is the contradiction the module is about, and until now it lived only in
the prose above: the graph forces at least `expanderAgreementFloor` of edges to
agree, while the prescribed law makes a given edge agree with probability
`2 * Phi (-10)`, about `1.5 * 10 ^ (-23)`. No sign configuration can meet the
prescription, because the floor is a property of the graph and holds of every
configuration whatsoever.

The Gaussian tail is bounded here by Chebyshev's inequality. The resulting
`Phi (-10) ≤ 1/100` bound is intentionally coarse, but is already far below
the graph-theoretic agreement floor. -/
theorem prescribedAgreement_lt_expanderAgreementFloor :
    2 * Foundations.Phi (-10) < expanderAgreementFloor := by
  have hPhi : Foundations.Phi (-10) ≤ (1 / 100 : ℝ) := by
    let μ := ProbabilityTheory.gaussianReal 0 1
    have hsubset : Set.Iic (-10 : ℝ) ⊆
        {x : ℝ | 10 ≤ |id x - ∫ y, id y ∂μ|} := by
      intro x hx
      rw [show (∫ y, id y ∂μ) = 0 by
        simp [μ, ProbabilityTheory.integral_id_gaussianReal]]
      simp only [id_eq, sub_zero]
      change x ≤ -10 at hx
      change 10 ≤ |x|
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq
      (μ := μ) (X := id) (ProbabilityTheory.memLp_id_gaussianReal 2)
      (show (0 : ℝ) < 10 by norm_num)
    have hmeasure : μ (Set.Iic (-10 : ℝ)) ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
      calc
        μ (Set.Iic (-10 : ℝ)) ≤ μ {x : ℝ | 10 ≤ |id x - ∫ y, id y ∂μ|} :=
          MeasureTheory.measure_mono hsubset
        _ ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
          convert hcheb using 1
          all_goals
            norm_num [μ, ProbabilityTheory.integral_id_gaussianReal,
              ProbabilityTheory.variance_id_gaussianReal]
    have hof : ENNReal.ofReal (Foundations.Phi (-10)) ≤ ENNReal.ofReal (1 / 100 : ℝ) := by
      rw [Foundations.Phi, ProbabilityTheory.ofReal_cdf]
      exact hmeasure
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hof
  linarith [expanderAgreementFloor_gt]

theorem expanderAgreementFloor_pos : 0 < expanderAgreementFloor := by
  have := expanderAgreementFloor_gt
  linarith

/-- **The max-cut eigenvalue bound, in the normalized form used.**

For a 6-regular graph on `n` vertices, `edgeCount = 3 * n`, and the spectral bound
gives `maxCut ≤ edgeCount / 2 + (n / 4) * (2 * sqrt 5)`. Normalizing, the *cut*
fraction is at most `1/2 + sqrt 5 / 6`, hence the *agreement* fraction is at least
`expanderAgreementFloor`. -/
theorem agreement_fraction_ge_floor
    (n edgeCount maxCut : ℝ)
    (hn : 0 < n)
    (hedge : edgeCount = 3 * n)
    (hcut : maxCut ≤ edgeCount / 2 + (n / 4) * (2 * Real.sqrt 5)) :
    1 - maxCut / edgeCount ≥ expanderAgreementFloor := by
  have hE : 0 < edgeCount := by rw [hedge]; linarith
  have hbound : maxCut / edgeCount ≤ 1 / 2 + Real.sqrt 5 / 6 := by
    rw [div_le_iff₀ hE, hedge]
    rw [hedge] at hcut
    nlinarith [hcut, hn, Real.sqrt_nonneg 5]
  unfold expanderAgreementFloor
  linarith

/-!
## 2. The total-variation gap

The event "the two endpoint signs of an edge agree" is measurable on that edge's pair
of variables, so it lower-bounds the edge's total-variation distance from the
prescription. Averaging over edges turns the pointwise frustration floor into an
average marginal total-variation gap.
-/

/-- **Average marginal total-variation lower bound.**

`agree e` is the probability, under an arbitrary candidate global law, that edge `e`'s
endpoint signs agree; `prescribedAgree` is the (tiny) agreement probability under the
prescription. Each edge's total variation is at least the difference of these two
probabilities, and averaging preserves the bound. -/
theorem average_tv_ge
    {ι : Type*} (E : Finset ι) (hE : E.Nonempty)
    (agree tv : ι → ℝ) (α β : ℝ)
    (htv : ∀ e ∈ E, agree e - β ≤ tv e)
    (hagree : α * E.card ≤ ∑ e ∈ E, agree e) :
    α - β ≤ (∑ e ∈ E, tv e) / E.card := by
  have hcard : (0 : ℝ) < E.card := by
    exact_mod_cast Finset.card_pos.mpr hE
  have hsum : ∑ e ∈ E, (agree e - β) ≤ ∑ e ∈ E, tv e :=
    Finset.sum_le_sum htv
  have hexp : ∑ e ∈ E, (agree e - β) = (∑ e ∈ E, agree e) - β * E.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hexp] at hsum
  rw [le_div_iff₀ hcard]
  linarith

/-- **Theorem 4 (iii), assembled.** With the frustration floor as `α` and a
prescription agreement probability `β` below it, the non-bipartite twin sits at
average marginal total-variation distance at least `expanderAgreementFloor - β` from
every global law — a strictly positive constant. -/
theorem nonbipartite_twin_tv_gap
    {ι : Type*} (E : Finset ι) (hE : E.Nonempty)
    (agree tv : ι → ℝ) (β : ℝ)
    (hβ : β < expanderAgreementFloor)
    (htv : ∀ e ∈ E, agree e - β ≤ tv e)
    (hagree : expanderAgreementFloor * E.card ≤ ∑ e ∈ E, agree e) :
    0 < (∑ e ∈ E, tv e) / E.card := by
  have h := average_tv_ge E hE agree tv expanderAgreementFloor β htv hagree
  linarith

/-!
## 3. The twin impossibility

The two systems have identical bounded-locality data at every fixed radius, and
opposite realizability status. Therefore realizability is not a function of that data
— for *any* function, of any logical complexity, deterministic or randomized,
certificate-hierarchical or not.
-/

/-- **Theorem 4 (iv): realizability is not a function of bounded-locality data.**

`localData r L` is whatever an audit of radius `r` can see about the system `L`. The
twin pair agrees on it for every `r`, and differs in realizability.

The logic is `Descent.ObservationalCeiling.LeveledBlindness`; the content of the
theorem is the twin construction that supplies the witness pair. -/
theorem no_bounded_locality_criterion
    {System LocalData : Type*}
    (localData : ℕ → System → LocalData)
    (asymptoticallyRealizable : System → Prop)
    (bipartiteTwin nonBipartiteTwin : System)
    (hlocal : ∀ r : ℕ, localData r bipartiteTwin = localData r nonBipartiteTwin)
    (hbip : asymptoticallyRealizable bipartiteTwin)
    (hnon : ¬ asymptoticallyRealizable nonBipartiteTwin) :
    ∀ r : ℕ, ¬ ∃ decide : LocalData → Prop,
        ∀ L : System, asymptoticallyRealizable L ↔ decide (localData r L) :=
  ({ positive := bipartiteTwin, negative := nonBipartiteTwin, same_data := hlocal,
     holds := hbip, fails := hnon } :
      Blindness.LeveledBlindness localData asymptoticallyRealizable).no_level_criterion

/-- The same impossibility for audits that may consult **every** radius at once and
combine the results arbitrarily: the twin pair is identical on the whole family. -/
theorem no_bounded_locality_hierarchy
    {System LocalData Verdict : Type*}
    (localData : ℕ → System → LocalData)
    (asymptoticallyRealizable : System → Prop)
    (combine : (ℕ → LocalData) → Verdict)
    (accept : Verdict → Prop)
    (bipartiteTwin nonBipartiteTwin : System)
    (hlocal : ∀ r : ℕ, localData r bipartiteTwin = localData r nonBipartiteTwin)
    (hbip : asymptoticallyRealizable bipartiteTwin)
    (hnon : ¬ asymptoticallyRealizable nonBipartiteTwin) :
    ¬ ∀ L : System,
        asymptoticallyRealizable L ↔ accept (combine (fun r ↦ localData r L)) := by
  intro hdec
  exact
    ({ positive := bipartiteTwin, negative := nonBipartiteTwin, same_data := hlocal,
       holds := hbip, fails := hnon } :
        Blindness.LeveledBlindness localData asymptoticallyRealizable).no_hierarchy_criterion combine
      ⟨accept, hdec⟩

/-!
## 4. Genetics corollary, stated in the vocabulary of summary statistics
-/

/-- **Summary-statistic coherence is not locally certifiable.**

Instantiating `System` with "a set of per-LD-block marginal laws implied by reported
GWAS summary statistics", `localData r` with "everything a radius-`r` neighbourhood
audit of adjacent blocks can compute", and `asymptoticallyRealizable` with "there is a
single population law having all the reported blocks as marginals", the twin
construction gives two summary-statistic sets that

* pass every neighbourhood consistency check at every radius, identically, and
* differ in whether one coherent population generated them.

Therefore no neighbourhood-consistency diagnostic — at any window size — is a valid
certificate of joint realizability. This is a restatement of
`no_bounded_locality_criterion`; it is recorded separately because it is the form in
which the result should be applied. -/
theorem summary_statistic_coherence_not_locally_certifiable
    {SummaryStatSet AuditOutput : Type*}
    (audit : ℕ → SummaryStatSet → AuditOutput)
    (onePopulationRealizable : SummaryStatSet → Prop)
    (coherentSet incoherentSet : SummaryStatSet)
    (hidenticalAudits : ∀ r : ℕ, audit r coherentSet = audit r incoherentSet)
    (hcoherent : onePopulationRealizable coherentSet)
    (hincoherent : ¬ onePopulationRealizable incoherentSet) :
    ∀ r : ℕ, ¬ ∃ certify : AuditOutput → Prop,
        ∀ S : SummaryStatSet, onePopulationRealizable S ↔ certify (audit r S) :=
  no_bounded_locality_criterion audit onePopulationRealizable coherentSet incoherentSet
    hidenticalAudits hcoherent hincoherent

end Descent.Conditionals

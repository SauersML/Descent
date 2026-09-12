/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Hidden load filtering: the likelihood of a visible pangenome history

`PANGENOME_HIDDEN_CLOCK.md` §9. A pangenome graph reports which fibers have been joined, and
hides the loads `L_C`, the numbers of true ancestral lineages behind each reported component.
This module builds the exact filter for the loads and proves that it computes the likelihood of
the visible history.

The filter is stated for any finite hidden jump process watched through a report map
`obs : S → ρ`. The transfer matrix of an observed change `R → R'` keeps the generator entries
from hidden states showing `R` to hidden states showing `R'` (`transferMatrix`), and the killed
generator `Q_R` keeps the entries between hidden states showing `R` (`killedGenerator`). Between
observed mergers the unnormalized posterior is `α(0) e^{t Q_R}`, with `e^{t Q_R}` the matrix
exponential `killedPropagator`; at an observed merger it is multiplied by the transfer matrix
(`filterPosterior`). The likelihood of a visible history (`visibleLikelihood`) is the path
density summed over the hidden states just before and just after every observed merger
(`visibleLikelihood_cons_apply`). The final mass of the filter is that likelihood averaged
against the starting weights (`filterPosterior_dotProduct_one`), and from a single hidden state
it is the likelihood itself (`filterPosterior_single_dotProduct_one`).

Between observed mergers the propagator solves the forward equation `P' = P Q_R`
(`hasDerivAt_killedPropagator`, entrywise `hasDerivAt_killedPropagator_apply`) and carries no mass
out of the report (`killedPropagator_apply_eq_zero`). It satisfies the first-jump equation
(`killedPropagator_apply_eq_firstJump`): either the hidden state holds for the whole interval with
survival factor `e^{t G(x, x)}`, or it holds until a time `s`, jumps inside the report, and is
carried the rest of the way. Iterating that equation over the internal jumps sums the densities
of the hidden paths between observed mergers.

The load chain of Theorem A (`loadGenerator`) is the instance. A hidden state assigns a load to
every set of fibers, and its report is the family of sets with a positive load (`loadReport`).
An invisible merger in `C` lowers `L_C` by one at rate `C(L_C, 2)`, a visible merger of two
components replaces them by their union with load `L_C + L_D - 1` at rate `L_C L_D`, and the
total exit rate is `C(K, 2)`. On a hidden state showing `R` the killed generator acts through the
internal rates `C(L_C, 2)` off the diagonal and `-C(K, 2)` on it
(`killedGenerator_mulVec_loadGenerator`). The transfer matrix of an observed report `R'` moves the
mass from `L` to `L^{(CD)}` with weight `L_C L_D`, for every pair whose merger produces `R'`
(`transferMatrix_mulVec_loadGenerator`). The killing rate is the total visible rate
`∑_{C < D} L_C L_D` (`killedGenerator_mulVec_one_loadGenerator`, from
`choose_two_sum_sub_sum_choose_two`). So between observed mergers the posterior mass decays at
the sum over pairs of the observed-filtration intensities `λ̂_CD = E[L_C L_D | visible history]`
(`hasDerivAt_posteriorMass_observedIntensity`).

Scope. The path measure of the continuous-time chain is not constructed. The killed propagator is
characterized by the two equations that define the killed transition function of a finite chain,
the forward equation and the first-jump equation, and the likelihood of a visible history is its
Markov-property decomposition at the observed merger times. Not proved here: that for a load state
whose components partition the fibers the only pair producing the observed report `R'` is the
pair of components `C, D` that `R'` joins.

## Empirical status

None. The bodies here are matrix calculus and finite sums: the generator, the report map and the
visible history are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset MeasureTheory
open scoped Matrix Matrix.Norms.Operator

noncomputable section

/-! ### Filtering a hidden jump process through a report -/

section Filter

variable {S ρ : Type*} [Fintype S] [DecidableEq S] [DecidableEq ρ]

/-- The generator entries from hidden states showing report `R` to hidden states showing report
`R'`, and zero elsewhere: the transfer matrix of an observed change of report. -/
def transferMatrix (G : Matrix S S ℝ) (obs : S → ρ) (R R' : ρ) : Matrix S S ℝ :=
  Matrix.of fun x y ↦ if obs x = R ∧ obs y = R' then G x y else 0

/-- The killed generator `Q_R`: the generator between hidden states showing report `R`, so that
every transition changing the report kills the mass. -/
def killedGenerator (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ) : Matrix S S ℝ :=
  transferMatrix G obs R R

/-- The killed propagator `e^{t Q_R}`, the matrix exponential of the killed generator. -/
def killedPropagator (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ) (t : ℝ) : Matrix S S ℝ :=
  NormedSpace.exp ℝ (t • killedGenerator G obs R)

/-- The unnormalized filter of a visible history. The history lists its stages, each the time
spent under the current report followed by the report the observed merger produced, and `final`
is the time spent under the last report. Between observed mergers the posterior is carried by the
killed propagator, and at an observed merger it is multiplied by the transfer matrix. -/
def filterPosterior (G : Matrix S S ℝ) (obs : S → ρ) :
    ρ → (S → ℝ) → List (ℝ × ρ) → ℝ → S → ℝ
  | R, posterior, [], final => posterior ᵥ* killedPropagator G obs R final
  | R, posterior, (duration, next) :: rest, final =>
    filterPosterior G obs next
      ((posterior ᵥ* killedPropagator G obs R duration) ᵥ* transferMatrix G obs R next) rest final

/-- The likelihood of a visible history from a hidden state: the path density of the history,
summed over the hidden states just before and just after every observed merger. Each interval
between observed mergers contributes an entry of the killed propagator, each observed merger an
entry of the transfer matrix, and the final interval its survival mass. -/
def visibleLikelihood (G : Matrix S S ℝ) (obs : S → ρ) : ρ → List (ℝ × ρ) → ℝ → S → ℝ
  | R, [], final => killedPropagator G obs R final *ᵥ fun _ ↦ 1
  | R, (duration, next) :: rest, final =>
    killedPropagator G obs R duration *ᵥ
      (transferMatrix G obs R next *ᵥ visibleLikelihood G obs next rest final)

/-- One observed merger in the likelihood, summed explicitly over the hidden state just before the
merger and the hidden state just after it. -/
theorem visibleLikelihood_cons_apply (G : Matrix S S ℝ) (obs : S → ρ) (R next : ρ)
    (duration final : ℝ) (rest : List (ℝ × ρ)) (x : S) :
    visibleLikelihood G obs R ((duration, next) :: rest) final x =
      ∑ before, ∑ after, killedPropagator G obs R duration x before *
        transferMatrix G obs R next before after *
          visibleLikelihood G obs next rest final after := by
  simp only [visibleLikelihood, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Spec §9, the filter recursion gives the likelihood of the visible history: the final mass of
the unnormalized filter is the likelihood of the history averaged against the starting weights. -/
theorem filterPosterior_dotProduct_one (G : Matrix S S ℝ) (obs : S → ρ)
    (history : List (ℝ × ρ)) :
    ∀ (R : ρ) (posterior : S → ℝ) (final : ℝ),
      filterPosterior G obs R posterior history final ⬝ᵥ (fun _ ↦ 1) =
        posterior ⬝ᵥ visibleLikelihood G obs R history final := by
  induction history with
  | nil =>
    intro R posterior final
    simp only [filterPosterior, visibleLikelihood]
    exact (Matrix.dotProduct_mulVec _ _ _).symm
  | cons stage rest ih =>
    intro R posterior final
    obtain ⟨duration, next⟩ := stage
    simp only [filterPosterior, visibleLikelihood]
    rw [ih, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]

/-- Started from a single hidden state, the final mass of the filter is the likelihood of the
visible history from that state. -/
theorem filterPosterior_single_dotProduct_one (G : Matrix S S ℝ) (obs : S → ρ)
    (history : List (ℝ × ρ)) (R : ρ) (x : S) (final : ℝ) :
    filterPosterior G obs R (Pi.single x 1) history final ⬝ᵥ (fun _ ↦ 1) =
      visibleLikelihood G obs R history final x := by
  rw [filterPosterior_dotProduct_one]
  simp [dotProduct, Pi.single_apply]

/-- Between observed mergers the posterior solves `α' = α Q_R`: the killed propagator solves the
forward equation of the killed generator. -/
theorem hasDerivAt_killedPropagator (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ) (t : ℝ) :
    HasDerivAt (killedPropagator G obs R)
      (killedPropagator G obs R t * killedGenerator G obs R) t :=
  hasDerivAt_exp_smul_const (killedGenerator G obs R) t

/-- Each entry of the killed propagator solves the forward equation. -/
theorem hasDerivAt_killedPropagator_apply (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ)
    (source target : S) (t : ℝ) :
    HasDerivAt (fun u ↦ killedPropagator G obs R u source target)
      ((killedPropagator G obs R t * killedGenerator G obs R) source target) t := by
  have hentry := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℝ ℝ source target)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_killedPropagator G obs R t)
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap',
    Matrix.entryLinearMap_apply] using hentry

/-- The killed propagator carries no mass from report `R` to a hidden state showing another
report. Assumes: a source showing `R` and a target showing a different report. -/
theorem killedPropagator_apply_eq_zero (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ)
    {source target : S} (hsource : obs source = R) (htarget : obs target ≠ R) (t : ℝ) :
    killedPropagator G obs R t source target = 0 := by
  have hderiv : ∀ u, HasDerivAt (fun v ↦ killedPropagator G obs R v source target) 0 u := by
    intro u
    refine (hasDerivAt_killedPropagator_apply G obs R source target u).congr_deriv ?_
    simp [Matrix.mul_apply, killedGenerator, transferMatrix, htarget]
  have hconst : killedPropagator G obs R t source target =
      killedPropagator G obs R 0 source target :=
    is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt) (fun u ↦ (hderiv u).deriv) t 0
  rw [hconst, killedPropagator, zero_smul, NormedSpace.exp_zero, Matrix.one_apply_ne]
  intro hsame
  exact htarget (hsame ▸ hsource)

/-- The first-jump equation of the killed propagator. Assumes: a source showing report `R`.
Either the hidden state holds at the source for the whole time `t`, with survival factor
`e^{t G(x, x)}`, or it holds until a time `s`, jumps at the killed-generator rate to another hidden
state showing `R`, and is carried the rest of the way. Iterating this equation over the jumps
inside the report sums the path densities of the hidden paths between observed mergers. -/
theorem killedPropagator_apply_eq_firstJump (G : Matrix S S ℝ) (obs : S → ρ) (R : ρ)
    {source : S} (hsource : obs source = R) (target : S) (t : ℝ) :
    killedPropagator G obs R t source target =
      (if source = target then Real.exp (t * G source source) else 0) +
        ∫ s in (0 : ℝ)..t, Real.exp (s * G source source) *
          ∑ middle ∈ univ.erase source, killedGenerator G obs R source middle *
            killedPropagator G obs R (t - s) middle target := by
  have hdiagonal : killedGenerator G obs R source source = G source source := by
    simp [killedGenerator, transferMatrix, hsource]
  have hmatrix : ∀ s, HasDerivAt (fun u ↦ killedPropagator G obs R (t - u))
      ((-1 : ℝ) • (killedGenerator G obs R * killedPropagator G obs R (t - s))) s := fun s ↦
    (hasDerivAt_exp_smul_const' (killedGenerator G obs R) (t - s)).scomp s
      ((hasDerivAt_id s).const_sub t)
  have hentry : ∀ middle s, HasDerivAt (fun u ↦ killedPropagator G obs R (t - u) middle target)
      (-(killedGenerator G obs R * killedPropagator G obs R (t - s)) middle target) s := by
    intro middle s
    have hcomposite := (LinearMap.toContinuousLinearMap
      (Matrix.entryLinearMap ℝ ℝ middle target)).hasFDerivAt.comp_hasDerivAt s (hmatrix s)
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap',
      Matrix.entryLinearMap_apply, Matrix.smul_apply, smul_eq_mul, neg_one_mul] using hcomposite
  have hcontinuous : ∀ middle,
      Continuous fun u ↦ killedPropagator G obs R (t - u) middle target :=
    fun middle ↦ continuous_iff_continuousAt.mpr fun s ↦ (hentry middle s).continuousAt
  have hproduct : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun u ↦ Real.exp (u * G source source) * killedPropagator G obs R (t - u) source target)
      (-(Real.exp (s * G source source) * ∑ middle ∈ univ.erase source,
        killedGenerator G obs R source middle *
          killedPropagator G obs R (t - s) middle target)) s := by
    intro s _
    refine (((hasDerivAt_mul_const (G source source)).exp).mul (hentry source s)).congr_deriv ?_
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ source), hdiagonal]
    ring
  have hintegrand : Continuous fun s ↦ -(Real.exp (s * G source source) *
      ∑ middle ∈ univ.erase source,
        killedGenerator G obs R source middle * killedPropagator G obs R (t - s) middle target) :=
    ((continuous_mul_right _).rexp.mul
      (continuous_finset_sum _ fun middle _ ↦ continuous_const.mul (hcontinuous middle))).neg
  have hfundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt hproduct
    (hintegrand.intervalIntegrable 0 t)
  have hstart : killedPropagator G obs R 0 source target = if source = target then 1 else 0 := by
    rw [killedPropagator, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
  simp only [intervalIntegral.integral_neg, sub_self, sub_zero, zero_mul, Real.exp_zero, one_mul,
    hstart] at hfundamental
  split_ifs at hfundamental ⊢ <;> linarith

/-- The transfer matrix acting on a test function from a hidden state showing `R`: the generator
acting on the test function cut down to the hidden states showing `R'`. Assumes: a hidden state
showing `R`. -/
theorem transferMatrix_mulVec (G : Matrix S S ℝ) (obs : S → ρ) {R : ρ} (R' : ρ) {x : S}
    (hx : obs x = R) (f : S → ℝ) :
    (transferMatrix G obs R R' *ᵥ f) x = (G *ᵥ fun y ↦ if obs y = R' then f y else 0) x := by
  simp only [Matrix.mulVec, dotProduct, transferMatrix, Matrix.of_apply, hx, eq_self_iff_true,
    true_and]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> simp

end Filter

/-! ### The load chain of Theorem A -/

section LoadChain

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- A hidden load state for fibers `α` and at most `n` true lineages: every set of fibers carries
a load, the number of true ancestral lineages hidden behind it. -/
abbrev LoadState (α : Type*) (n : ℕ) : Type _ := Finset α → Fin (n + 1)

/-- The load `L_C` of a set of fibers. -/
def load (x : LoadState α n) (C : Finset α) : ℕ := x C

/-- The report of a load state: the sets of fibers with a positive load. -/
def loadReport (x : LoadState α n) : Finset (Finset α) := univ.filter fun C ↦ 0 < load x C

/-- The total load `K = ∑_C L_C`, the number of true ancestral lineages. -/
def totalLoad (x : LoadState α n) : ℕ := ∑ C, load x C

/-- An invisible merger inside the component `C`: its load drops by one. -/
def internalMerger (x : LoadState α n) (C : Finset α) : LoadState α n :=
  Function.update x C ⟨load x C - 1, lt_of_le_of_lt (Nat.sub_le _ _) (x C).isLt⟩

/-- A visible merger of the components in `pair`: they are replaced by their union, which carries
their pooled load less one, capped at `n` so that the result is a load state. -/
def visibleMerger (x : LoadState α n) (pair : Finset (Finset α)) : LoadState α n :=
  fun E ↦
    if E = pair.sup id then
      ⟨min ((∑ C ∈ pair, load x C) - 1) n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    else if E ∈ pair then 0 else x E

variable (α n) in
/-- The load chain of Theorem A as a generator: an invisible merger in `C` at rate `C(L_C, 2)`,
spec (A1), a visible merger of a pair of components at rate `∏_{C ∈ pair} L_C`, spec (A2), and
total exit rate `C(K, 2)`. -/
def loadGenerator : Matrix (LoadState α n) (LoadState α n) ℝ :=
  Matrix.of fun x y ↦
    (∑ C, if y = internalMerger x C then ((load x C).choose 2 : ℝ) else 0) +
      (∑ pair ∈ univ.powersetCard 2,
        if y = visibleMerger x pair then ∏ C ∈ pair, (load x C : ℝ) else 0) -
      if y = x then ((totalLoad x).choose 2 : ℝ) else 0

/-- Spec (A3) as arithmetic: the pairs of true lineages falling across two components number
`C(K, 2) - ∑_C C(L_C, 2)`, which is half the sum of the ordered cross products. -/
theorem choose_two_sum_sub_sum_choose_two {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ℕ) :
    (((∑ C, L C).choose 2 : ℕ) : ℝ) - ∑ C, (((L C).choose 2 : ℕ) : ℝ) =
      (∑ C, ∑ D ∈ univ.erase C, (L C : ℝ) * L D) / 2 := by
  have hsquare : (∑ C, (L C : ℝ)) * ∑ C, (L C : ℝ) =
      ∑ C, (L C : ℝ) * L C + ∑ C, ∑ D ∈ univ.erase C, (L C : ℝ) * L D := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [Finset.mul_sum, Finset.add_sum_erase univ (fun D ↦ (L C : ℝ) * L D) (Finset.mem_univ C)]
  have hchoose : ∑ C, (((L C).choose 2 : ℕ) : ℝ) =
      (∑ C, (L C : ℝ) * L C - ∑ C, (L C : ℝ)) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [Nat.cast_choose_two]
    ring
  rw [hchoose, Nat.cast_choose_two, Nat.cast_sum]
  linear_combination hsquare / 2

/-- The load of a component after an invisible merger in `C`. -/
theorem load_internalMerger (x : LoadState α n) (C E : Finset α) :
    load (internalMerger x C) E = if E = C then load x C - 1 else load x E := by
  unfold internalMerger load
  rw [Function.update_apply]
  split_ifs <;> rfl

/-- The load of a component after a visible merger of `pair`. -/
theorem load_visibleMerger (x : LoadState α n) (pair : Finset (Finset α)) (E : Finset α) :
    load (visibleMerger x pair) E =
      if E = pair.sup id then min ((∑ C ∈ pair, load x C) - 1) n
      else if E ∈ pair then 0 else load x E := by
  simp only [visibleMerger, load]
  split_ifs <;> simp

/-- An invisible merger in a component hiding at least two lineages leaves the report unchanged.
Assumes: `2 ≤ L_C`. -/
theorem loadReport_internalMerger {x : LoadState α n} {C : Finset α} (hload : 2 ≤ load x C) :
    loadReport (internalMerger x C) = loadReport x := by
  ext E
  simp only [loadReport, Finset.mem_filter, Finset.mem_univ, true_and, load_internalMerger]
  split_ifs with hE
  · subst hE
    constructor <;> intro <;> omega
  · rfl

/-- A visible merger of two components with positive loads changes the report. Assumes: a pair of
distinct components, both with a positive load. -/
theorem loadReport_visibleMerger_ne {x : LoadState α n} {pair : Finset (Finset α)}
    (hpair : pair ∈ univ.powersetCard 2) (hpositive : ∀ C ∈ pair, 0 < load x C) :
    loadReport (visibleMerger x pair) ≠ loadReport x := by
  obtain ⟨C, D, hCD, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hpair).2
  have hexists : ∃ E ∈ ({C, D} : Finset (Finset α)),
      E ≠ ({C, D} : Finset (Finset α)).sup id := by
    by_contra hall
    push_neg at hall
    exact hCD ((hall C (by simp)).trans (hall D (by simp)).symm)
  obtain ⟨E, hE, hne⟩ := hexists
  intro hsame
  have hmember : E ∈ loadReport (visibleMerger x {C, D}) := by
    rw [hsame]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpositive E hE⟩
  have hload := (Finset.mem_filter.mp hmember).2
  rw [load_visibleMerger, if_neg hne, if_pos hE] at hload
  exact lt_irrefl 0 hload

/-- The generator of the load chain acting on a test function: invisible mergers at rates
`C(L_C, 2)`, visible mergers at rates `∏ L_C`, and the total exit rate `C(K, 2)`. -/
theorem loadGenerator_mulVec (f : LoadState α n → ℝ) (x : LoadState α n) :
    (loadGenerator α n *ᵥ f) x =
      ∑ C, ((load x C).choose 2 : ℝ) * f (internalMerger x C) +
        ∑ pair ∈ univ.powersetCard 2, (∏ C ∈ pair, (load x C : ℝ)) * f (visibleMerger x pair) -
          ((totalLoad x).choose 2 : ℝ) * f x := by
  have hinternal : ∑ y, (∑ C, if y = internalMerger x C then ((load x C).choose 2 : ℝ) else 0) *
      f y = ∑ C, ((load x C).choose 2 : ℝ) * f (internalMerger x C) := by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hvisible : ∑ y, (∑ pair ∈ univ.powersetCard 2,
      if y = visibleMerger x pair then ∏ C ∈ pair, (load x C : ℝ) else 0) * f y =
        ∑ pair ∈ univ.powersetCard 2, (∏ C ∈ pair, (load x C : ℝ)) * f (visibleMerger x pair) := by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdiagonal : ∑ y, (if y = x then ((totalLoad x).choose 2 : ℝ) else 0) * f y =
      ((totalLoad x).choose 2 : ℝ) * f x := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, loadGenerator, Matrix.of_apply, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hinternal, hvisible, hdiagonal]

/-- Spec §9, the killed generator of the load chain. Assumes: a hidden state showing report `R`.
The killed generator acts through the internal rates `C(L_C, 2)` off the diagonal and `-C(K, 2)`
on the diagonal. -/
theorem killedGenerator_mulVec_loadGenerator {R : Finset (Finset α)} {x : LoadState α n}
    (hx : loadReport x = R) (f : LoadState α n → ℝ) :
    (killedGenerator (loadGenerator α n) loadReport R *ᵥ f) x =
      ∑ C, ((load x C).choose 2 : ℝ) * f (internalMerger x C) -
        ((totalLoad x).choose 2 : ℝ) * f x := by
  rw [killedGenerator, transferMatrix_mulVec (loadGenerator α n) loadReport R hx,
    loadGenerator_mulVec]
  have hinternal : ∀ C, ((load x C).choose 2 : ℝ) *
      (if loadReport (internalMerger x C) = R then f (internalMerger x C) else 0) =
        ((load x C).choose 2 : ℝ) * f (internalMerger x C) := by
    intro C
    by_cases hload : 2 ≤ load x C
    · rw [loadReport_internalMerger hload, hx, if_pos rfl]
    · rw [Nat.choose_eq_zero_of_lt (by omega : load x C < 2), Nat.cast_zero, zero_mul, zero_mul]
  have hvisible : ∀ pair ∈ univ.powersetCard 2, (∏ C ∈ pair, (load x C : ℝ)) *
      (if loadReport (visibleMerger x pair) = R then f (visibleMerger x pair) else 0) = 0 := by
    intro pair hpair
    by_cases hpositive : ∀ C ∈ pair, 0 < load x C
    · have hchanged : loadReport (visibleMerger x pair) ≠ R := by
        rw [← hx]
        exact loadReport_visibleMerger_ne hpair hpositive
      rw [if_neg hchanged, mul_zero]
    · push_neg at hpositive
      obtain ⟨C, hC, hzero⟩ := hpositive
      rw [Finset.prod_eq_zero hC (by rw [Nat.le_zero.mp hzero, Nat.cast_zero]), zero_mul]
  simp only [hinternal, if_pos hx]
  rw [Finset.sum_eq_zero hvisible, add_zero]

/-- Spec §9, an observed visible merger. Assumes: a hidden state showing report `R` and an observed
report `R' ≠ R`. The transfer matrix moves the mass from `L` to `L^{(CD)}` with weight `L_C L_D`,
for every pair of components whose merger produces the observed report. -/
theorem transferMatrix_mulVec_loadGenerator {R R' : Finset (Finset α)} (hchange : R' ≠ R)
    {x : LoadState α n} (hx : loadReport x = R) (f : LoadState α n → ℝ) :
    (transferMatrix (loadGenerator α n) loadReport R R' *ᵥ f) x =
      ∑ pair ∈ univ.powersetCard 2, if loadReport (visibleMerger x pair) = R' then
        (∏ C ∈ pair, (load x C : ℝ)) * f (visibleMerger x pair) else 0 := by
  rw [transferMatrix_mulVec (loadGenerator α n) loadReport R' hx, loadGenerator_mulVec]
  have hinternal : ∀ C, ((load x C).choose 2 : ℝ) *
      (if loadReport (internalMerger x C) = R' then f (internalMerger x C) else 0) = 0 := by
    intro C
    by_cases hload : 2 ≤ load x C
    · rw [loadReport_internalMerger hload, hx, if_neg hchange.symm, mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (by omega : load x C < 2), Nat.cast_zero, zero_mul]
  have hstays : loadReport x ≠ R' := by
    rw [hx]
    exact hchange.symm
  simp only [hinternal, Finset.sum_const_zero, zero_add, if_neg hstays, mul_zero, sub_zero]
  refine Finset.sum_congr rfl fun pair _ ↦ ?_
  split_ifs <;> simp

/-- Spec §9, the killing rate is the total visible rate. Assumes: a hidden state showing report
`R`. The killed generator removes mass at rate `C(K, 2) - ∑_C C(L_C, 2) = ∑_{C < D} L_C L_D`. -/
theorem killedGenerator_mulVec_one_loadGenerator {R : Finset (Finset α)} {x : LoadState α n}
    (hx : loadReport x = R) :
    (killedGenerator (loadGenerator α n) loadReport R *ᵥ fun _ ↦ 1) x =
      -((∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D) / 2) := by
  rw [killedGenerator_mulVec_loadGenerator hx, ← choose_two_sum_sub_sum_choose_two, totalLoad]
  simp only [mul_one]
  ring

/-- Spec §9, the posterior mass decays at the total visible rate. Assumes: starting weights carried
by the hidden states showing `R`. Between observed mergers the derivative of the unnormalized
posterior mass is minus the unnormalized posterior average of `∑_{C < D} L_C L_D`. -/
theorem hasDerivAt_posteriorMass_loadGenerator (R : Finset (Finset α))
    (posterior : LoadState α n → ℝ) (hposterior : ∀ x, loadReport x ≠ R → posterior x = 0)
    (t : ℝ) :
    HasDerivAt
      (fun u ↦ (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R u) ⬝ᵥ fun _ ↦ 1)
      (-∑ x, (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) x *
        ((∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D) / 2)) t := by
  have hentries : HasDerivAt (fun u ↦ ∑ y, ∑ source, posterior source *
      killedPropagator (loadGenerator α n) loadReport R u source y)
      (∑ y, ∑ source, posterior source *
        (killedPropagator (loadGenerator α n) loadReport R t *
          killedGenerator (loadGenerator α n) loadReport R) source y) t :=
    HasDerivAt.sum fun y _ ↦ HasDerivAt.sum fun source _ ↦
      (hasDerivAt_killedPropagator_apply (loadGenerator α n) loadReport R source y t).const_mul
        (posterior source)
  have hsupport : ∀ z, loadReport z ≠ R →
      (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) z = 0 := by
    intro z hz
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun source _ ↦ ?_
    by_cases hsource : loadReport source = R
    · rw [killedPropagator_apply_eq_zero (loadGenerator α n) loadReport R hsource hz, mul_zero]
    · rw [hposterior source hsource, zero_mul]
  have hvector : (∑ y, ∑ source, posterior source *
      (killedPropagator (loadGenerator α n) loadReport R t *
        killedGenerator (loadGenerator α n) loadReport R) source y) =
      (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) ⬝ᵥ
        (killedGenerator (loadGenerator α n) loadReport R *ᵥ fun _ ↦ 1) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    simp only [dotProduct, Matrix.vecMul, mul_one]
  convert hentries using 1
  · funext u
    simp only [dotProduct, Matrix.vecMul, mul_one]
  · rw [hvector, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : loadReport z = R
    · rw [killedGenerator_mulVec_one_loadGenerator hz, mul_neg]
    · rw [hsupport z hz, zero_mul, zero_mul, neg_zero]

/-- The observed-filtration intensity of a visible merger of `C` and `D`: the expectation of
`L_C L_D` under the normalized posterior, `λ̂_CD = E[L_C L_D | visible history]`. -/
def observedIntensity (posterior : LoadState α n → ℝ) (C D : Finset α) : ℝ :=
  (∑ x, posterior x * ((load x C : ℝ) * load x D)) / ∑ x, posterior x

/-- The unnormalized posterior average of the total visible rate is the sum of the observed
intensities over pairs of components times the posterior mass. Assumes: a nonzero posterior
mass. -/
theorem sum_posterior_mul_visibleRate (posterior : LoadState α n → ℝ)
    (hmass : ∑ x, posterior x ≠ 0) :
    ∑ x, posterior x * ((∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D) / 2) =
      (∑ C, ∑ D ∈ univ.erase C, observedIntensity posterior C D) / 2 * ∑ x, posterior x := by
  have hcancel : ∀ C D, observedIntensity posterior C D * ∑ x, posterior x =
      ∑ x, posterior x * ((load x C : ℝ) * load x D) := by
    intro C D
    rw [observedIntensity, div_mul_eq_mul_div, mul_div_assoc, div_self hmass, mul_one]
  have hswap : ∑ x, posterior x * ∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D =
      ∑ C, ∑ D ∈ univ.erase C, ∑ x, posterior x * ((load x C : ℝ) * load x D) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun C _ ↦ Finset.sum_comm
  have hlhs : ∑ x, posterior x * ((∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D) / 2) =
      (∑ x, posterior x * ∑ C, ∑ D ∈ univ.erase C, (load x C : ℝ) * load x D) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ ↦ (mul_div_assoc _ _ _).symm
  rw [hlhs, hswap, div_mul_eq_mul_div, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun D _ ↦ (hcancel C D).symm

/-- Spec §9, the observed-filtration intensity. Assumes: starting weights carried by the hidden
states showing `R` and a nonzero posterior mass at time `t`. Between observed mergers the
posterior mass decays at the sum over pairs of components of `λ̂_CD = E[L_C L_D | visible
history]`: its derivative is minus that sum times the mass. -/
theorem hasDerivAt_posteriorMass_observedIntensity (R : Finset (Finset α))
    (posterior : LoadState α n → ℝ) (hposterior : ∀ x, loadReport x ≠ R → posterior x = 0)
    (t : ℝ)
    (hmass : ∑ x, (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) x ≠ 0) :
    HasDerivAt
      (fun u ↦ (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R u) ⬝ᵥ fun _ ↦ 1)
      (-((∑ C, ∑ D ∈ univ.erase C, observedIntensity
          (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) C D) / 2 *
        ∑ x, (posterior ᵥ* killedPropagator (loadGenerator α n) loadReport R t) x)) t := by
  rw [← sum_posterior_mul_visibleRate _ hmass]
  exact hasDerivAt_posteriorMass_loadGenerator R posterior hposterior t

end LoadChain

end

end Descent.Pangenome.GraphCoalescent

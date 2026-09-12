/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLimit
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Uniformization: the fixed-time laws of the continuous-time report and of `Z_p`

`Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling` and
`Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLimit` state (F1) and (F3) for the
skeleton chains `kingmanStep` and `multiplicativeStep` run at the rings of a Poisson clock of rate
one, as Poisson mixtures `poissonMixture U` of the skeleton laws. This module identifies those
mixtures with the laws at time `U` of the continuous-time chains whose generators are `K - 1`, so
the qualifier "rate-one uniformization" drops from the fixed-time statements.

**The identity.** For every finite square matrix `K` and `U ≥ 0`,
`e^{U(K - 1)} = Σ_m Pr(N_U = m) K^m` with `N_U` Poisson of mean `U`, as a convergent series of
matrices (`hasSum_poissonPMFReal_smul_pow`) and entrywise (`hasSum_poissonPMFReal_mul_pow_apply`).
The proof splits `U(K - 1)` as `UK` plus the scalar `-U`, which commute, and multiplies the
exponential series of `UK` by `e^{-U}`. The identity needs no stochasticity.

**Fixed-time laws.** The skeleton law is the initial law against the powers of the kernel
(`skeletonLaw_eq_sum_pow`). `continuousLaw P μ₀ U` is `μ₀ e^{U(P - 1)}`, the law at time `U` of
the continuous-time chain with generator `P - 1`, and it is the Poisson mixture of the skeleton
laws (`hasSum_poissonPMFReal_mul_skeletonLaw`, `poissonMixture_skeletonLaw`). For a stochastic
kernel it is a probability vector (`continuousLaw_nonneg`, `sum_continuousLaw`).

**The report and `Z_p`.** `kingmanContinuousLaw n U` is Kingman's `n`-coalescent in scaled time
`u = n² t` at time `U` from the singletons, with generator `kingmanStep n - 1`, every cover at rate
`1/n²`. `reportContinuousLaw s U` is its image under `observed s`, the law of the graph's report.
`multiplicativeContinuousLaw s U` is `Z_p` at time `U` from the interface, with generator
`multiplicativeStep n - 1`, components `C` and `D` merging at rate `c(C) c(D)/n²`.

* `reportConnectionProbability_eq`: the Poisson-mixed connection probability of
  `MultiplicativeConnectionLimit` is the probability that the continuous-time report is connected
  at time `U`.
* `multiplicativeContinuousLaw_top_eq`: the continuous-time `Z_p` is connected at time `U` with the
  Möbius probability `Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ}`.
* `abs_reportContinuousLaw_top_sub_le`: **(F3), quantitative, at a fixed time**. The two
  continuous-time connection probabilities at time `U` are within `U²/(4n)`.
* `report_multiplicative_totalVariation_le`: after `m` skeleton steps the report's law and the law
  of `Z_p` have total variation at most `m(m-1)/(4n)`, through the coupling of
  `MultiplicativeCoupling`.
* `report_multiplicative_continuousTotalVariation_le`: **(F1) at a fixed time**. The laws at time
  `U` of the continuous-time report and of the continuous-time `Z_p` have total variation at most
  `min {1, U²/(4n)}` (`half_sum_abs_sub_le_poissonMixture` carries the bound through the mixture).

Scope. The continuous-time chains enter through their transition semigroups `e^{U(P - 1)}`
applied to the initial law; their path measures are not constructed, and the path-level (F1) of
`MultiplicativeCoupling` remains a statement about the uniformized skeleton. As in
`MultiplicativeConnectionLimit`, `Z_p` runs on the partitions of the individuals, each of mass
`1/n`.

## Empirical status

None. The bodies here are a finite matrix exponential, a Poisson series of matrix powers, and
finite laws on the equivalence relations of a finite set, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.UniformizationIdentity

open Coalescent Finset ProbabilityTheory

open scoped Classical

noncomputable section

/-! ### The uniformization identity -/

/-- **Uniformization as a matrix series**: for a finite square matrix `K` and `U ≥ 0`,
`e^{U(K - 1)} = Σ_m Pr(N_U = m) K^m`, with `N_U` Poisson of mean `U`. -/
theorem hasSum_poissonPMFReal_smul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (U : NNReal) :
    HasSum (fun m : ℕ ↦ poissonPMFReal U m • K ^ m)
      (NormedSpace.exp ℝ ((U : ℝ) • (K - 1))) := by
  have hexp : HasSum (fun m : ℕ ↦ ((m.factorial : ℝ))⁻¹ • ((U : ℝ) • K) ^ m)
      (NormedSpace.exp ℝ ((U : ℝ) • K)) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((U : ℝ) • K)
  have hscalar : NormedSpace.exp ℝ (algebraMap ℝ (Matrix ι ι ℝ) (-(U : ℝ))) =
      algebraMap ℝ (Matrix ι ι ℝ) (Real.exp (-(U : ℝ))) := by
    rw [Real.exp_eq_exp_ℝ]
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (-(U : ℝ))).symm
  have hdecomp : (U : ℝ) • (K - 1) = (U : ℝ) • K + algebraMap ℝ (Matrix ι ι ℝ) (-(U : ℝ)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, neg_smul, sub_eq_add_neg]
  have hsplit : NormedSpace.exp ℝ ((U : ℝ) • (K - 1)) =
      NormedSpace.exp ℝ ((U : ℝ) • K) * algebraMap ℝ (Matrix ι ι ℝ) (Real.exp (-(U : ℝ))) := by
    rw [hdecomp, Matrix.exp_add_of_commute (𝕂 := ℝ) _ _
      (Algebra.commutes (-(U : ℝ)) ((U : ℝ) • K)).symm, hscalar]
  have hterm : (fun m : ℕ ↦ poissonPMFReal U m • K ^ m) = fun m : ℕ ↦
      (((m.factorial : ℝ))⁻¹ • ((U : ℝ) • K) ^ m) *
        algebraMap ℝ (Matrix ι ι ℝ) (Real.exp (-(U : ℝ))) := by
    funext m
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, smul_pow, smul_smul,
      smul_smul, poissonPMFReal]
    congr 1
    ring
  rw [hterm, hsplit]
  exact hexp.mul_right _

/-- **Uniformization, entrywise**: `e^{U(K - 1)}(i, j) = Σ_m Pr(N_U = m) K^m(i, j)`. -/
theorem hasSum_poissonPMFReal_mul_pow_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (U : NNReal) (i j : ι) :
    HasSum (fun m : ℕ ↦ poissonPMFReal U m * (K ^ m) i j)
      (NormedSpace.exp ℝ ((U : ℝ) • (K - 1)) i j) := by
  let entry : Matrix ι ι ℝ →+ ℝ :=
    { toFun := fun M ↦ M i j
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hcont : Continuous entry := continuous_id.matrix_elem i j
  exact (hasSum_poissonPMFReal_smul_pow K U).map entry hcont

/-! ### Fixed-time laws -/

/-- **The skeleton law is the initial law against the powers of the kernel**: `μ₀ P^m`. -/
theorem skeletonLaw_eq_sum_pow {S : Type*} [Fintype S] [DecidableEq S] (P : S → S → ℝ)
    (μ₀ : S → ℝ) (m : ℕ) (t : S) :
    skeletonLaw P μ₀ m t = ∑ r, μ₀ r * (Matrix.of P ^ m) r t := by
  induction m generalizing t with
  | zero => simp [skeletonLaw, Matrix.one_apply, mul_ite]
  | succ m ih =>
    simp only [skeletonLaw, ih, pow_succ, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring

/-- **The law at time `U` of the continuous-time chain with generator `P - 1`**, from the initial
law `μ₀`: `μ₀ e^{U(P - 1)}`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite matrix exponential applied to a vector. -/
def continuousLaw {S : Type*} [Fintype S] [DecidableEq S] (P : S → S → ℝ) (μ₀ : S → ℝ)
    (U : NNReal) (t : S) : ℝ :=
  ∑ r, μ₀ r * NormedSpace.exp ℝ ((U : ℝ) • (Matrix.of P - 1)) r t

/-- **The law at time `U` is the Poisson mixture of the skeleton laws.** -/
theorem hasSum_poissonPMFReal_mul_skeletonLaw {S : Type*} [Fintype S] [DecidableEq S]
    (P : S → S → ℝ) (μ₀ : S → ℝ) (U : NNReal) (t : S) :
    HasSum (fun m ↦ poissonPMFReal U m * skeletonLaw P μ₀ m t) (continuousLaw P μ₀ U t) := by
  simp only [skeletonLaw_eq_sum_pow, continuousLaw, Finset.mul_sum]
  refine hasSum_sum fun r _ ↦ ?_
  convert (hasSum_poissonPMFReal_mul_pow_apply (Matrix.of P) U r t).mul_left (μ₀ r) using 1
  funext m
  ring

/-- `poissonMixture U` of the skeleton laws is the law at time `U`. -/
theorem poissonMixture_skeletonLaw {S : Type*} [Fintype S] [DecidableEq S] (P : S → S → ℝ)
    (μ₀ : S → ℝ) (U : NNReal) (t : S) :
    poissonMixture U (fun m ↦ skeletonLaw P μ₀ m t) = continuousLaw P μ₀ U t :=
  (hasSum_poissonPMFReal_mul_skeletonLaw P μ₀ U t).tsum_eq

/-- For a nonnegative kernel and initial law, the law at time `U` is nonnegative. -/
theorem continuousLaw_nonneg {S : Type*} [Fintype S] [DecidableEq S] {P : S → S → ℝ}
    {μ₀ : S → ℝ} (hP : ∀ r t, 0 ≤ P r t) (hμ : ∀ r, 0 ≤ μ₀ r) (U : NNReal) (t : S) :
    0 ≤ continuousLaw P μ₀ U t :=
  (hasSum_poissonPMFReal_mul_skeletonLaw P μ₀ U t).nonneg fun m ↦
    mul_nonneg poissonPMFReal_nonneg (skeletonLaw_nonneg hP hμ m t)

/-- For a stochastic kernel, the law at time `U` keeps the total mass of the initial law. -/
theorem sum_continuousLaw {S : Type*} [Fintype S] [DecidableEq S] {P : S → S → ℝ}
    {μ₀ : S → ℝ} (hrow : ∀ r, ∑ t, P r t = 1) (U : NNReal) :
    ∑ t, continuousLaw P μ₀ U t = ∑ r, μ₀ r := by
  have h := hasSum_sum fun t (_ : t ∈ (univ : Finset S)) ↦
    hasSum_poissonPMFReal_mul_skeletonLaw P μ₀ U t
  simp only [← Finset.mul_sum, sum_skeletonLaw hrow] at h
  have h2 := (poissonPMFRealSum U).mul_right (∑ r, μ₀ r)
  rw [one_mul] at h2
  exact h.unique h2

/-! ### The report and `Z_p` in continuous time -/

/-- **Kingman's `n`-coalescent in scaled time at time `U`**, from the panel's singletons: the chain
with generator `kingmanStep n - 1`, every cover at rate `1/n²`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite matrix exponential applied to a point mass. -/
def kingmanContinuousLaw (n : ℕ) (U : NNReal) : ER n → ℝ :=
  continuousLaw (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) U

/-- **The graph's report at time `U`**: the image of `kingmanContinuousLaw` under `observed s`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The image of a finite law. -/
def reportContinuousLaw {n : ℕ} (s : Fin n → Fin n) (U : NNReal) (z : ER n) : ℝ :=
  ∑ ξ, kingmanContinuousLaw n U ξ * (if observed s ξ = z then 1 else 0)

/-- **`Z_p` at time `U`**, from the interface: the chain with generator `multiplicativeStep n - 1`,
components `C` and `D` merging at rate `c(C) c(D)/n²`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite matrix exponential applied to a point mass. -/
def multiplicativeContinuousLaw {n : ℕ} (s : Fin n → Fin n) (U : NNReal) : ER n → ℝ :=
  continuousLaw (multiplicativeStep n) (fun ζ ↦ if ζ = graphKer s then 1 else 0) U

/-- Kingman's law at time `U` is a probability vector. -/
theorem sum_kingmanContinuousLaw (n : ℕ) (U : NNReal) : ∑ ξ, kingmanContinuousLaw n U ξ = 1 := by
  show ∑ ξ, continuousLaw (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) U ξ = 1
  rw [sum_continuousLaw sum_kingmanStep]
  simp

/-- The law of `Z_p` at time `U` is a probability vector. -/
theorem sum_multiplicativeContinuousLaw {n : ℕ} (s : Fin n → Fin n) (U : NNReal) :
    ∑ ζ, multiplicativeContinuousLaw s U ζ = 1 := by
  show ∑ ζ, continuousLaw (multiplicativeStep n) (fun ζ ↦ if ζ = graphKer s then 1 else 0) U ζ = 1
  rw [sum_continuousLaw sum_multiplicativeStep]
  simp

/-- Kingman's law at time `U` is the Poisson mixture of the uniformized skeleton laws. -/
theorem hasSum_poissonPMFReal_mul_kingmanLaw (n : ℕ) (U : NNReal) (ξ : ER n) :
    HasSum (fun m ↦ poissonPMFReal U m * kingmanLaw n m ξ) (kingmanContinuousLaw n U ξ) :=
  hasSum_poissonPMFReal_mul_skeletonLaw (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) U ξ

/-- The law of `Z_p` at time `U` is the Poisson mixture of the uniformized skeleton laws. -/
theorem hasSum_poissonPMFReal_mul_multiplicativeLaw {n : ℕ} (s : Fin n → Fin n) (U : NNReal)
    (ζ : ER n) :
    HasSum (fun m ↦ poissonPMFReal U m * multiplicativeLaw s m ζ)
      (multiplicativeContinuousLaw s U ζ) :=
  hasSum_poissonPMFReal_mul_skeletonLaw (multiplicativeStep n)
    (fun ζ ↦ if ζ = graphKer s then 1 else 0) U ζ

/-- The report's law at time `U` is the Poisson mixture of the report's skeleton laws. -/
theorem hasSum_poissonPMFReal_mul_reportLaw {n : ℕ} (s : Fin n → Fin n) (U : NNReal)
    (z : ER n) :
    HasSum (fun m ↦ poissonPMFReal U m *
        ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = z then 1 else 0))
      (reportContinuousLaw s U z) := by
  simp only [Finset.mul_sum, reportContinuousLaw]
  refine hasSum_sum fun ξ _ ↦ ?_
  convert (hasSum_poissonPMFReal_mul_kingmanLaw n U ξ).mul_right
    (if observed s ξ = z then (1 : ℝ) else 0) using 1
  funext m
  ring

/-- **The Poisson-mixed connection probability is the continuous-time one**: the probability that
the graph's report is connected at scaled time `U`, for Kingman's coalescent in continuous time. -/
theorem reportConnectionProbability_eq {n : ℕ} (s : Fin n → Fin n) (U : NNReal) :
    reportConnectionProbability s U = reportContinuousLaw s U ⊤ :=
  (hasSum_poissonPMFReal_mul_reportLaw s U ⊤).tsum_eq

/-- **`Z_p` in continuous time is connected at time `U` with the Möbius probability**
`Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ}`. -/
theorem multiplicativeContinuousLaw_top_eq {n : ℕ} [NeZero n] (s : Fin n → Fin n)
    (U : NNReal) :
    multiplicativeContinuousLaw s U ⊤ =
      ∑ σ, (topMobius (blocks σ) : ℝ) *
        (if graphKer s ≤ σ then Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ)))
          else 0) := by
  have h : HasSum (fun m ↦ poissonPMFReal U m *
      ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0))
      (multiplicativeContinuousLaw s U ⊤) := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    exact hasSum_poissonPMFReal_mul_multiplicativeLaw s U ⊤
  exact h.unique (hasSum_poissonPMFReal_mul_multiplicativeTop s U)

/-- **Theorem F, (F3), quantitative, at a fixed time.** The continuous-time report and the
continuous-time `Z_p` are connected at time `U` with probabilities within `U²/(4n)`.

Assumes: `0 < n`. -/
theorem abs_reportContinuousLaw_top_sub_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (U : NNReal) :
    |reportContinuousLaw s U ⊤ - multiplicativeContinuousLaw s U ⊤| ≤ (U : ℝ) ^ 2 / (4 * n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← reportConnectionProbability_eq, multiplicativeContinuousLaw_top_eq]
  exact abs_reportConnectionProbability_sub_le hn s U

/-! ### (F1) at a fixed time -/

/-- **After `m` skeleton steps the report and `Z_p` differ by at most the separation mass**: both
laws are images of one coupled law, and the two images disagree only on separated states.

Assumes: `0 < n`. -/
theorem report_multiplicative_totalVariation_le_separationMass {n : ℕ} (hn : 0 < n)
    (s : Fin n → Fin n) (m : ℕ) :
    1 / 2 * ∑ z, |∑ ξ, kingmanLaw n m ξ * (if observed s ξ = z then 1 else 0)
        - multiplicativeLaw s m z|
      ≤ separationMass (coupledStep s) (coupledStartLaw s) (coupledSep s) m := by
  have hwt : ∀ X, 0 ≤ skeletonLaw (coupledStep s) (coupledStartLaw s) m X :=
    skeletonLaw_nonneg (coupledStep_nonneg hn s) (coupledStartLaw_nonneg s) m
  have hfst : ∀ z : ER n, ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = z then 1 else 0)
      = ∑ X ∈ univ.filter (fun X : CoupledState n ↦ observed s X.1 = z),
          skeletonLaw (coupledStep s) (coupledStartLaw s) m X := by
    intro z
    rw [sum_kingmanLaw_mul_eq s m, Finset.sum_filter]
    exact Finset.sum_congr rfl fun X _ ↦ by split_ifs <;> simp
  have hsnd : ∀ z : ER n, multiplicativeLaw s m z
      = ∑ X ∈ univ.filter (fun X : CoupledState n ↦ X.2.1 = z),
          skeletonLaw (coupledStep s) (coupledStartLaw s) m X := fun z ↦
    (sum_filter_skeletonLaw_comp_eq (coupledStep s) (coupledStartLaw s) (multiplicativeStep n)
      (fun ζ ↦ if ζ = graphKer s then 1 else 0) (fun X ↦ X.2.1)
      (fun X ζ' ↦ sum_coupledStep_snd s X ζ') (sum_filter_snd_coupledStartLaw s) m z).symm
  simp only [hfst, hsnd]
  have hcouple := sum_abs_sub_fiber_le (skeletonLaw (coupledStep s) (coupledStartLaw s) m) hwt
    (fun X : CoupledState n ↦ observed s X.1) fun X ↦ X.2.1
  refine (mul_le_mul_of_nonneg_left hcouple (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul, separationMass]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun X hX ↦ ?_) fun X _ _ ↦ hwt X
  rw [Finset.mem_filter] at hX ⊢
  exact ⟨Finset.mem_univ X,
    Classical.byContradiction fun hsep ↦ hX.2 (observed_eq_of_not_coupledSep hsep)⟩

/-- **Theorem F, (F1), for the skeleton laws.** After `m` steps the report's law and the law of
`Z_p` have total variation at most `m(m-1)/(4n)`.

Assumes: `0 < n`. -/
theorem report_multiplicative_totalVariation_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (m : ℕ) :
    1 / 2 * ∑ z, |∑ ξ, kingmanLaw n m ξ * (if observed s ξ = z then 1 else 0)
        - multiplicativeLaw s m z|
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) :=
  (report_multiplicative_totalVariation_le_separationMass hn s m).trans
    (coupled_separationMass_le hn s m)

/-- The total variation of the skeleton laws is a probability.

Assumes: `0 < n`. -/
theorem report_multiplicative_totalVariation_le_one {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (m : ℕ) :
    1 / 2 * ∑ z, |∑ ξ, kingmanLaw n m ξ * (if observed s ξ = z then 1 else 0)
        - multiplicativeLaw s m z| ≤ 1 :=
  (report_multiplicative_totalVariation_le_separationMass hn s m).trans
    (sum_filter_not_skeletonLaw_le (coupledStep_nonneg hn s) (sum_coupledStep s)
      (coupledStartLaw_nonneg s) (sum_coupledStartLaw s) (univ.filter (coupledSep s)) m)

/-- **Total variation passes through a Poisson mixture**: if two families of laws mix to `A` and
`B` under the Poisson weights of mean `U`, the total variation between `A` and `B` is at most the
Poisson mixture of the total variations.

Assumes: every total variation of the families is at most one, which makes the mixture summable. -/
theorem half_sum_abs_sub_le_poissonMixture {X : Type*} [Fintype X] {U : NNReal}
    {a b : ℕ → X → ℝ} {A B : X → ℝ}
    (hA : ∀ z, HasSum (fun m ↦ poissonPMFReal U m * a m z) (A z))
    (hB : ∀ z, HasSum (fun m ↦ poissonPMFReal U m * b m z) (B z))
    (hd1 : ∀ m, 1 / 2 * ∑ z, |a m z - b m z| ≤ 1) :
    1 / 2 * ∑ z, |A z - B z| ≤ poissonMixture U fun m ↦ 1 / 2 * ∑ z, |a m z - b m z| := by
  have hD : HasSum (fun m ↦ poissonPMFReal U m * (1 / 2 * ∑ z, |a m z - b m z|))
      (poissonMixture U fun m ↦ 1 / 2 * ∑ z, |a m z - b m z|) := by
    refine Summable.hasSum (Summable.of_nonneg_of_le (fun m ↦ ?_) (fun m ↦ ?_)
      (poissonPMFRealSum U).summable)
    · exact mul_nonneg poissonPMFReal_nonneg
        (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    · calc poissonPMFReal U m * (1 / 2 * ∑ z, |a m z - b m z|) ≤ poissonPMFReal U m * 1 :=
            mul_le_mul_of_nonneg_left (hd1 m) poissonPMFReal_nonneg
        _ = poissonPMFReal U m := mul_one _
  have hE : HasSum
      (fun m ↦ 1 / 2 * ∑ z, (if 0 ≤ A z - B z then (1 : ℝ) else -1) *
        (poissonPMFReal U m * a m z - poissonPMFReal U m * b m z))
      (1 / 2 * ∑ z, (if 0 ≤ A z - B z then (1 : ℝ) else -1) * (A z - B z)) :=
    (hasSum_sum fun z _ ↦ ((hA z).sub (hB z)).mul_left
      (if 0 ≤ A z - B z then (1 : ℝ) else -1)).mul_left (1 / 2)
  have habs : ∑ z, |A z - B z| =
      ∑ z, (if 0 ≤ A z - B z then (1 : ℝ) else -1) * (A z - B z) := by
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (not_le.mp h)]
  rw [habs]
  refine hasSum_le (fun m ↦ ?_) hE hD
  calc 1 / 2 * ∑ z, (if 0 ≤ A z - B z then (1 : ℝ) else -1) *
        (poissonPMFReal U m * a m z - poissonPMFReal U m * b m z)
      ≤ 1 / 2 * ∑ z, poissonPMFReal U m * |a m z - b m z| := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ ↦ ?_) (by norm_num)
        rw [← mul_sub, mul_left_comm]
        refine mul_le_mul_of_nonneg_left ?_ poissonPMFReal_nonneg
        split_ifs
        · rw [one_mul]
          exact le_abs_self _
        · rw [neg_one_mul]
          exact neg_le_abs _
    _ = poissonPMFReal U m * (1 / 2 * ∑ z, |a m z - b m z|) := by
        rw [← Finset.mul_sum]
        ring

/-- **Theorem F, (F1), at a fixed time.** The laws at scaled time `U` of the graph's report, for
Kingman's coalescent in continuous time, and of the multiplicative coalescent `Z_p` in continuous
time, have total variation at most `min {1, U²/(4n)}`.

Assumes: `0 < n`. -/
theorem report_multiplicative_continuousTotalVariation_le {n : ℕ} (hn : 0 < n)
    (s : Fin n → Fin n) (U : NNReal) :
    1 / 2 * ∑ z, |reportContinuousLaw s U z - multiplicativeContinuousLaw s U z|
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n)) :=
  (half_sum_abs_sub_le_poissonMixture (hasSum_poissonPMFReal_mul_reportLaw s U)
    (hasSum_poissonPMFReal_mul_multiplicativeLaw s U)
    (report_multiplicative_totalVariation_le_one hn s)).trans
    (poissonMixture_le_min (by exact_mod_cast hn)
      (fun m ↦ mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
      (report_multiplicative_totalVariation_le_one hn s)
      (report_multiplicative_totalVariation_le hn s))

end

end Descent.Pangenome.GraphCoalescent.UniformizationIdentity

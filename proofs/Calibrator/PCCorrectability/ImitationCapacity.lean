/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.ImitationRigidity
import Calibrator.PCCorrectability.Threshold
import Mathlib.Tactic.Positivity

namespace Calibrator

noncomputable section

/-!
# Imitation capacity as a linear program, and the certificate that detects

`Calibrator.ImitationRigidity` proves the algebraic half of the imitation
problem: a polygenic signal mixed over its own effect prior inflates the
genotype covariance by exactly `t · vvᵀ`, and whether that is a *signal* or an
*imitation* depends on one thing — whether the inflated covariance is still a
legal member of the background class.  That file settles the question for a
single quadratic ceiling.  This file settles it for the class the applications
actually use: a background class cut out by *linear* constraints,

    K = { Σ : Σ - B is variance-nonnegative, and ℓ_a(Σ) ≤ κ_a for every a }.

Three things follow, and they are what this file is for.

**The capacity is the value of a linear program.**  The largest spike level at
which the mixed alternative is literally a mixture of nulls — hence
undetectable at any sample size, by any procedure — is

    t* = inf over constraints a and spike directions v of
           (κ_a - ℓ_a(Σ₀)) / ℓ_a(vvᵀ),

the infimum ranging over pairs whose *spike load* `ℓ_a(vvᵀ)` is positive.
`BackgroundClass.isNull_spiked_of_le_imitationCapacity` is the licence: below
`t*` every component of the mixture is a null covariance.

**Rigidity is a normal-cone condition, not a symmetry condition.**  If some
constraint is *active* at `Σ₀` and has positive spike load, the capacity is
zero and no positive spike level is imitable.  The constraint index is a
Hahn–Banach certificate the machine returns rather than merely proves to
exist.  **Rigidity does not require a transitive symmetry group on the class**;
`traceWindow_rigid` refutes that by construction, with a generic positive-definite `A` and
no symmetry whatsoever.

**On the equi-exit class the detection threshold equals the capacity.**
Equi-exit — the binding constraint's spike load is constant over the prior's
support — is the precise content of "the likelihood ratio depends on the
nuisance only through a quadratic form", and it appears as an explicit field of
`EquiExit`, never as an implicit convention.  Under it the optimal test is
*synthesized*, not merely shown to exist: reject when the empirical certificate
statistic `ℓ_a(Σ̂)` exceeds the null ceiling `κ_a` plus half the margin.
`EquiExit.certificateTest_null_control` and `EquiExit.certificateTest_power`
are the two halves, and both are proved.

## The biology

*The imitation wall is the proximal-contamination problem.*  A genetic
relatedness matrix that absorbs the very association being tested, and the
episode in which polygenic-adaptation signals turned out to be residual
stratification imitating a polygenic spike, are the same phenomenon: the
alternative was a legal background.  The linear program makes this computable
instead of anecdotal — given the background class as linear constraints, the
capacity is an LP value and the certificate is an index.  Leave-one-chromosome-
out is then not a variance fix but a *restriction of the background class*, and
`BackgroundClass.imitationCapacity_antitone_constraints` says which way and by
how much: more constraints, smaller capacity, lower threshold.

*Rigidity without symmetry is the useful direction.*  Any active linear
constraint with positive spike load rigidifies.  That is a design instruction
for study construction, not a structural accident of symmetric designs.

*The `m_eff` prohibition.*  Effective-marker counts of the Cheverud–Nyholt and
Li–Ji type are participation-ratio functionals of the LD spectrum, hence
continuous in the weak topology.  `certificate_not_momentContinuous` proves
that no such functional can determine a detection threshold: two spectra agree
on every normalized moment to within `1/(n+1)` while their inverse-trace
certificates differ by `n/(n+1)`.  The corpus's own `ldWhiteningGain` is the
right functional for exactly the reason those are wrong — it is edge-sensitive
and *not* weakly continuous.  Those two facts are the same fact.

References:
- Berisa and Pickrell (2016), Bioinformatics 32:283--285 (LD blocks).
- Cheverud (2001), Heredity 87:52--58; Li and Ji (2005), Heredity 95:221--227.
- Onatski, Moreira, and Hallin (2013), Annals of Statistics 41:1204--1231.
- Yang et al. (2014), Nature Genetics 46:100--106 (leave-one-chromosome-out).
-/

section SpikeAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The rank-one spike matrix `vvᵀ`.**  This is the covariance inflation a
polygenic signal with effect direction `v` contributes once the per-individual
factor is mixed over its own prior — the infinitesimal model, read at the level
of second moments.

    Empirical status: DERIVED. `spikeOuter_eq_rankOneCovarianceBump` identifies
    it with the bump of `covarianceMatrix_addRankOneSignal`, which is an exact
    covariance identity rather than a modelling choice. -/
def spikeOuter (v : ι → ℝ) : Matrix ι ι ℝ := fun i j ↦ v i * v j

theorem spikeOuter_eq_rankOneCovarianceBump (v : ι → ℝ) :
    spikeOuter v = rankOneCovarianceBump 1 v := by
  ext i j
  simp [spikeOuter, rankOneCovarianceBump]

/-- The score variance a unit spike contributes to a weighting `x` is the
squared projection of `x` on the spike direction. -/
theorem quadForm_spikeOuter (v x : ι → ℝ) :
    quadForm (spikeOuter v) x = dot v x ^ 2 := by
  rw [spikeOuter_eq_rankOneCovarianceBump, quadForm_rankOneCovarianceBump]
  ring

theorem quadForm_add_matrix (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  unfold quadForm gramForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simp only [Matrix.add_apply]
  ring

theorem quadForm_smul_matrix (c : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm (c • A) x = c * quadForm A x := by
  unfold quadForm gramForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem varianceNonneg_add {A B : Matrix ι ι ℝ}
    (hA : VarianceNonneg A) (hB : VarianceNonneg B) : VarianceNonneg (A + B) := by
  intro x
  rw [quadForm_add_matrix]
  exact add_nonneg (hA x) (hB x)

theorem varianceNonneg_smul {c : ℝ} {A : Matrix ι ι ℝ}
    (hc : 0 ≤ c) (hA : VarianceNonneg A) : VarianceNonneg (c • A) := by
  intro x
  rw [quadForm_smul_matrix]
  exact mul_nonneg hc (hA x)

theorem varianceNonneg_spikeOuter (v : ι → ℝ) : VarianceNonneg (spikeOuter v) := by
  intro x
  rw [quadForm_spikeOuter]
  exact sq_nonneg _

end SpikeAlgebra

/-!
## Two-block vectors

Both concrete objects this file has to compute with are two-block: the
subgroup-contrast direction of a stratified panel takes one value on the
subgroup and another on its complement, and the witness spectrum of the `m_eff`
prohibition takes one eigenvalue on a vanishing block and another off it.  One
summation lemma serves both, which is the reason they are written this way
rather than separately.
-/

section TwoBlock

/-- **A two-block sequence**: value `a` on the first `k` indices, `b` after.

    Empirical status: DERIVED (an indexing device; the genotype content is in
    `subgroupContrast`, which is an instance of it). -/
def twoBlock (k : ℕ) (a b : ℝ) : ℕ → ℝ := fun i ↦ if i < k then a else b

theorem sum_twoBlock (a b : ℝ) (k j : ℕ) :
    ∑ i ∈ Finset.range (k + j), (if i < k then a else b) =
      (k : ℝ) * a + (j : ℝ) * b := by
  induction j with
  | zero =>
      have hcongr : ∀ i ∈ Finset.range (k + 0), (if i < k then a else b) = a := by
        intro i hi
        have hi' : i < k := by
          have := Finset.mem_range.mp hi
          omega
        exact if_pos hi'
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      simp
  | succ n ih =>
      have hstep : k + (n + 1) = (k + n) + 1 := by omega
      have hnot : ¬ (k + n < k) := by omega
      rw [hstep, Finset.sum_range_succ, ih, if_neg hnot]
      push_cast
      ring

theorem sum_twoBlock_apply (k j : ℕ) (a b : ℝ) (f : ℝ → ℝ) :
    ∑ i ∈ Finset.range (k + j), f (twoBlock k a b i) =
      (k : ℝ) * f a + (j : ℝ) * f b := by
  have hpoint : ∀ i : ℕ, f (twoBlock k a b i) = if i < k then f a else f b := by
    intro i
    unfold twoBlock
    exact apply_ite f (i < k) a b
  simp only [hpoint]
  exact sum_twoBlock (f a) (f b) k j

theorem sum_pow_twoBlock (k j : ℕ) (a b : ℝ) (p : ℕ) :
    ∑ i ∈ Finset.range (k + j), (twoBlock k a b i) ^ p =
      (k : ℝ) * a ^ p + (j : ℝ) * b ^ p :=
  sum_twoBlock_apply k j a b (fun x ↦ x ^ p)

theorem sum_inv_twoBlock (k j : ℕ) (a b : ℝ) :
    ∑ i ∈ Finset.range (k + j), (twoBlock k a b i)⁻¹ =
      (k : ℝ) * a⁻¹ + (j : ℝ) * b⁻¹ :=
  sum_twoBlock_apply k j a b (fun x ↦ x⁻¹)

end TwoBlock

/-- **A background class cut out by linear constraints.**

`base` is the floor of the class: membership requires `Σ - base` to be
variance-nonnegative, and `base = c • 1` recovers the usual `Σ ≥ cI`.  Each
`a : cidx` indexes one linear functional `form a` with ceiling `bound a`.
Additivity and homogeneity are fields rather than side conditions, because the
whole linear-programming argument is the statement that these two properties,
and nothing else about the class, determine the capacity.

    Empirical status: UNTESTED. This is a modelling frame, not a measured
    quantity; what is testable is the capacity it computes for a specific
    background class, via `BackgroundClass.imitationCapacity`. -/
structure BackgroundClass (ι : Type*) [Fintype ι] [DecidableEq ι]
    (cidx : Type*) where
  /-- Floor of the class: `Σ - base` must be variance-nonnegative. -/
  base : Matrix ι ι ℝ
  /-- One linear functional per constraint index. -/
  form : cidx → Matrix ι ι ℝ → ℝ
  /-- The ceiling each functional must respect. -/
  bound : cidx → ℝ
  form_add : ∀ (a : cidx) (M N : Matrix ι ι ℝ),
    form a (M + N) = form a M + form a N
  form_smul : ∀ (a : cidx) (c : ℝ) (M : Matrix ι ι ℝ),
    form a (c • M) = c * form a M

namespace BackgroundClass

section Capacity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}
variable (K : BackgroundClass ι cidx)

/-- Membership in the background class: above the floor, and under every
ceiling.

    Empirical status: UNTESTED (a definition of legality, not a measurement). -/
def IsNull (S : Matrix ι ι ℝ) : Prop :=
  VarianceNonneg (S - K.base) ∧ ∀ a : cidx, K.form a S ≤ K.bound a

/-- **Spike load of a constraint in a direction**: how fast the constraint's
value rises per unit of spike.  This is the quantity that decides rigidity.

    Empirical status: UNTESTED. -/
def spikeLoad (a : cidx) (v : ι → ℝ) : ℝ := K.form a (spikeOuter v)

/-- **Headroom of a constraint at the baseline**: how much of its budget the
null covariance has not yet spent.

    Empirical status: UNTESTED. -/
def headroom (a : cidx) (S₀ : Matrix ι ι ℝ) : ℝ := K.bound a - K.form a S₀

/-- A constraint is *active* at `S₀` when it is met with equality: the baseline
has spent its entire budget.

    Empirical status: UNTESTED. -/
def Active (a : cidx) (S₀ : Matrix ι ι ℝ) : Prop := K.form a S₀ = K.bound a

/-- The spiked covariance at level `t` in direction `v`.

The class argument names the testing problem this alternative belongs to and is
written `_K` because it does not enter the formula: the alternative is the same
matrix whatever class is being tested against.  It is carried so that the
alternative is addressable as a member of the problem rather than as a free
matrix expression, which is what every call site wants.

    Empirical status: DERIVED (this is the bump of
    `covarianceMatrix_addRankOneSignal`, re-parametrized so the level enters
    linearly). -/
def spiked (_K : BackgroundClass ι cidx) (S₀ : Matrix ι ι ℝ) (t : ℝ)
    (v : ι → ℝ) : Matrix ι ι ℝ :=
  S₀ + t • spikeOuter v

theorem headroom_nonneg {S₀ : Matrix ι ι ℝ} (hnull : K.IsNull S₀) (a : cidx) :
    0 ≤ K.headroom a S₀ :=
  sub_nonneg.mpr (hnull.2 a)

theorem headroom_eq_zero_of_active {a : cidx} {S₀ : Matrix ι ι ℝ}
    (hactive : K.Active a S₀) : K.headroom a S₀ = 0 := by
  have h : K.form a S₀ = K.bound a := hactive
  unfold headroom
  rw [h]
  ring

/-- **Every constraint moves linearly in the spike level, at rate equal to its
spike load.**  This single identity is the whole reason the capacity is a
linear-programming value: the feasible set of levels is an intersection of
half-lines. -/
theorem form_spiked (a : cidx) (S₀ : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) :
    K.form a (K.spiked S₀ t v) = K.form a S₀ + t * K.spikeLoad a v := by
  unfold spiked spikeLoad
  rw [K.form_add, K.form_smul]

/-- The set of *exit levels*: for each constraint and each spike direction with
positive load, the level at which that constraint is first violated.  The
capacity is the infimum of this set — the linear program.

    Empirical status: UNTESTED. -/
def exitLevels (S₀ : Matrix ι ι ℝ) (support : Set (ι → ℝ)) : Set ℝ :=
  {s | ∃ a : cidx, ∃ v ∈ support, 0 < K.spikeLoad a v ∧
    s = K.headroom a S₀ / K.spikeLoad a v}

/-- **The imitation capacity: the value of the linear program.**  The largest
spike level at which the mixed alternative is still a mixture of nulls.

    Empirical status: UNTESTED. Testable by construction: for a background
    class given by explicit linear constraints this is a finite infimum a
    simulation can evaluate and compare against a measured detection boundary. -/
def imitationCapacity (S₀ : Matrix ι ι ℝ) (support : Set (ι → ℝ)) : ℝ :=
  sInf (K.exitLevels S₀ support)

theorem bddBelow_exitLevels {S₀ : Matrix ι ι ℝ} (hnull : K.IsNull S₀)
    (support : Set (ι → ℝ)) : BddBelow (K.exitLevels S₀ support) := by
  refine ⟨0, ?_⟩
  rintro s ⟨a, v, _hv, hload, rfl⟩
  exact div_nonneg (K.headroom_nonneg hnull a) (le_of_lt hload)

theorem imitationCapacity_le {S₀ : Matrix ι ι ℝ} (hnull : K.IsNull S₀)
    {support : Set (ι → ℝ)} {a : cidx} {v : ι → ℝ} (hv : v ∈ support)
    (hload : 0 < K.spikeLoad a v) :
    K.imitationCapacity S₀ support ≤ K.headroom a S₀ / K.spikeLoad a v :=
  csInf_le (K.bddBelow_exitLevels hnull support) ⟨a, v, hv, hload, rfl⟩

theorem le_imitationCapacity {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)} {t : ℝ}
    (hne : (K.exitLevels S₀ support).Nonempty)
    (hlb : ∀ (a : cidx) (v : ι → ℝ), v ∈ support → 0 < K.spikeLoad a v →
      t ≤ K.headroom a S₀ / K.spikeLoad a v) :
    t ≤ K.imitationCapacity S₀ support := by
  refine le_csInf hne ?_
  rintro s ⟨a, v, hv, hload, rfl⟩
  exact hlb a v hv hload

/-!
### The licence: below the capacity the alternative is a mixture of nulls

`isNull_spiked_of_le_imitationCapacity` is the statement that matters for
practice.  It says the *components* of the mixed alternative are themselves
null covariances, so the alternative law is literally a mixture of null laws
within any covariance-determined family — Gaussian, in the applications.  No
test at any sample size separates a mixture of nulls from the convex hull of
the null family; that is the imitation wall.
-/

/-- **Licence.**  At any nonnegative level at or below the capacity, the spiked
covariance in any supported direction is itself a member of the background
class. -/
theorem isNull_spiked_of_le_imitationCapacity {S₀ : Matrix ι ι ℝ}
    {support : Set (ι → ℝ)} (hnull : K.IsNull S₀)
    {t : ℝ} (ht : 0 ≤ t) (hle : t ≤ K.imitationCapacity S₀ support)
    {v : ι → ℝ} (hv : v ∈ support) :
    K.IsNull (K.spiked S₀ t v) := by
  constructor
  · have hrewrite : K.spiked S₀ t v - K.base = (S₀ - K.base) + t • spikeOuter v := by
      unfold spiked
      exact add_sub_right_comm S₀ (t • spikeOuter v) K.base
    rw [hrewrite]
    exact varianceNonneg_add hnull.1
      (varianceNonneg_smul ht (varianceNonneg_spikeOuter v))
  · intro a
    rw [K.form_spiked]
    have hbase := hnull.2 a
    rcases le_or_lt (K.spikeLoad a v) 0 with hload | hload
    · have hstep : t * K.spikeLoad a v ≤ 0 := by nlinarith [ht, hload]
      linarith
    · have hcap : t ≤ K.headroom a S₀ / K.spikeLoad a v :=
        le_trans hle (K.imitationCapacity_le hnull hv hload)
      have hmul : t * K.spikeLoad a v ≤ K.headroom a S₀ :=
        (le_div_iff₀ hload).mp hcap
      unfold headroom at hmul
      linarith

/-- **The class is convex**, so a mixture of nulls is a null at the level of
covariances too.  Together with the licence this is the sense in which the
mixed alternative "is" a background: not merely componentwise legal, but legal
after mixing. -/
theorem isNull_convex {S T : Matrix ι ι ℝ} (hS : K.IsNull S) (hT : K.IsNull T)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    K.IsNull (w • S + (1 - w) • T) := by
  have hw1' : (0 : ℝ) ≤ 1 - w := by linarith
  constructor
  · have hrewrite : w • S + (1 - w) • T - K.base
        = w • (S - K.base) + (1 - w) • (T - K.base) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hrewrite]
    exact varianceNonneg_add (varianceNonneg_smul hw0 hS.1)
      (varianceNonneg_smul hw1' hT.1)
  · intro a
    rw [K.form_add, K.form_smul, K.form_smul]
    have h1 : w * K.form a S ≤ w * K.bound a :=
      mul_le_mul_of_nonneg_left (hS.2 a) hw0
    have h2 : (1 - w) * K.form a T ≤ (1 - w) * K.bound a :=
      mul_le_mul_of_nonneg_left (hT.2 a) hw1'
    nlinarith [h1, h2]

/-!
### The certificate: an active constraint with positive load forces capacity zero

This is the Hahn–Banach direction, and the reason the theorem is useful rather
than merely true: the separating functional is not asserted to exist, it is
returned.  The constraint index `a` *is* the certificate.
-/

/-- **Rigidity, pointwise.**  If a constraint is active at the baseline and has
positive load in direction `v`, then no positive spike level in that direction
is legal.  The proof is one line of arithmetic on the constraint value, which
is exactly the point: rigidity is a normal-cone condition, not a symmetry
condition. -/
theorem not_isNull_spiked_of_active {S₀ : Matrix ι ι ℝ} {a : cidx} {v : ι → ℝ}
    (hactive : K.Active a S₀) (hload : 0 < K.spikeLoad a v)
    {t : ℝ} (ht : 0 < t) :
    ¬ K.IsNull (K.spiked S₀ t v) := by
  intro hcontra
  have hbound := hcontra.2 a
  have hactive' : K.form a S₀ = K.bound a := hactive
  rw [K.form_spiked, hactive'] at hbound
  have hpos : 0 < t * K.spikeLoad a v := mul_pos ht hload
  linarith

/-- **Rigidity, as a linear-programming value.**  An active constraint with
positive spike load in some supported direction drives the capacity to zero:
the background class can imitate nothing at all. -/
theorem imitationCapacity_eq_zero_of_active {S₀ : Matrix ι ι ℝ}
    {support : Set (ι → ℝ)} (hnull : K.IsNull S₀)
    {a : cidx} {v : ι → ℝ} (hv : v ∈ support)
    (hactive : K.Active a S₀) (hload : 0 < K.spikeLoad a v) :
    K.imitationCapacity S₀ support = 0 := by
  have hmem : (0 : ℝ) ∈ K.exitLevels S₀ support := by
    refine ⟨a, v, hv, hload, ?_⟩
    rw [K.headroom_eq_zero_of_active hactive, zero_div]
  refine le_antisymm ?_ ?_
  · exact csInf_le (K.bddBelow_exitLevels hnull support) hmem
  · refine le_csInf ⟨0, hmem⟩ ?_
    rintro s ⟨b, w, _hw, hloadb, rfl⟩
    exact div_nonneg (K.headroom_nonneg hnull b) (le_of_lt hloadb)

/-!
### Leave-one-chromosome-out is a restriction of the background class

LOCO is usually described as removing the proximal contribution from the
relatedness matrix so a test statistic is not adjusted by its own signal.  In
this frame it is something sharper and more computable: it *adds* linear
constraints to the background class.  The capacity is antitone in the
constraint family, so LOCO can only lower the imitation wall — and the amount
by which it lowers it is the difference of two linear-programming values, not
an unquantified benefit.
-/

/-- **Adding constraints cannot raise the capacity.**  `f` embeds the smaller
constraint family into the larger one with the same functionals and ceilings;
every exit level of the small class is an exit level of the large one, so the
large class's infimum is no larger. -/
theorem imitationCapacity_antitone_constraints {cidx' : Type*}
    (K' : BackgroundClass ι cidx') {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (hnull' : K'.IsNull S₀) (f : cidx → cidx')
    (hform : ∀ a : cidx, K'.form (f a) = K.form a)
    (hbound : ∀ a : cidx, K'.bound (f a) = K.bound a)
    (hne : (K.exitLevels S₀ support).Nonempty) :
    K'.imitationCapacity S₀ support ≤ K.imitationCapacity S₀ support := by
  refine csInf_le_csInf (K'.bddBelow_exitLevels hnull' support) hne ?_
  rintro s ⟨a, v, hv, hload, rfl⟩
  have hloadeq : K'.spikeLoad (f a) v = K.spikeLoad a v := by
    unfold spikeLoad
    rw [hform a]
  have hheadeq : K'.headroom (f a) S₀ = K.headroom a S₀ := by
    unfold headroom
    rw [hform a, hbound a]
  refine ⟨f a, v, hv, ?_, ?_⟩
  · rw [hloadeq]
    exact hload
  · rw [hloadeq, hheadeq]

end Capacity

end BackgroundClass

/-!
## The concrete certificate: a Frobenius pairing

Every constraint used in the applications — trace windows, block-LD budgets,
per-chromosome budgets — is a Frobenius pairing `⟪A, Σ⟫` against a fixed
matrix.  For that shape the spike load is a quadratic form, so "positive spike
load" is checkable, and the certificate statistic is continuous, so the
population-level separation of the next section transfers to samples.
-/

section Frobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}

/-- **The Frobenius pairing** `⟪A, M⟫ = tr(AᵀM)`, written as a double sum so no
trace lemmas are needed.

    Empirical status: DERIVED (a definition of the pairing; its identification
    with the spike load is `frobeniusForm_spikeOuter`). -/
def frobeniusForm (A M : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, A i j * M i j

theorem frobeniusForm_add (A M N : Matrix ι ι ℝ) :
    frobeniusForm A (M + N) = frobeniusForm A M + frobeniusForm A N := by
  unfold frobeniusForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simp only [Matrix.add_apply]
  ring

theorem frobeniusForm_smul (A : Matrix ι ι ℝ) (c : ℝ) (M : Matrix ι ι ℝ) :
    frobeniusForm A (c • M) = c * frobeniusForm A M := by
  unfold frobeniusForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The spike load of a Frobenius constraint is the quadratic form of its
matrix in the spike direction.**  This is what makes "positive spike load" a
checkable condition rather than an abstraction: for a positive-definite `A` it
holds in every nonzero direction. -/
theorem frobeniusForm_spikeOuter (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    frobeniusForm A (spikeOuter v) = quadForm A v := by
  unfold frobeniusForm quadForm gramForm
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  simp only [spikeOuter]
  ring

/-- **Consistency of the certificate statistic.**  Entrywise convergence of the
empirical covariance carries the Frobenius certificate to its population value.
Combined with `EquiExit.certificateTest_power` and
`EquiExit.certificateTest_null_control` this closes the achievability half for
the trace-window certificate, given a consistent covariance estimator.  What it
does *not* supply is the probabilistic statement that a sample covariance from
`n` draws is entrywise consistent: that is a hypothesis here, not a
conclusion. -/
theorem frobeniusForm_tendsto (A : Matrix ι ι ℝ)
    (empirical : ℕ → Matrix ι ι ℝ) (S : Matrix ι ι ℝ)
    (hentry : ∀ i j, Filter.Tendsto (fun n ↦ empirical n i j) Filter.atTop
      (nhds (S i j))) :
    Filter.Tendsto (fun n ↦ frobeniusForm A (empirical n)) Filter.atTop
      (nhds (frobeniusForm A S)) := by
  unfold frobeniusForm
  exact tendsto_finset_sum _ (fun i _ ↦
    tendsto_finset_sum _ (fun j _ ↦ (hentry i j).const_mul (A i j)))

/-!
### The trace window

The trace window is the one linear constraint a standardized genotype panel
always carries: the trace of a standardized genotype covariance is pinned by
the marker count, so a background class over genotypes has this constraint
whether or not anyone writes it down.  It is the constraint whose certificate
the corpus has in fact been using, and the rest of this file identifies it.
-/

/-- **The trace-window functional**: total standardized variance.

    Empirical status: DERIVED (the trace of a matrix; `traceForm_spikeOuter`
    identifies its spike load with the squared length of the effect vector). -/
def traceForm (M : Matrix ι ι ℝ) : ℝ := ∑ i, M i i

theorem traceForm_add (M N : Matrix ι ι ℝ) :
    traceForm (M + N) = traceForm M + traceForm N := by
  unfold traceForm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ by simp only [Matrix.add_apply])

theorem traceForm_smul (c : ℝ) (M : Matrix ι ι ℝ) :
    traceForm (c • M) = c * traceForm M := by
  unfold traceForm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by simp only [Matrix.smul_apply, smul_eq_mul])

/-- **The spike load of the trace window is the squared length of the effect
vector.**  Everything downstream — `effectiveSubgroupSize`, `demographicSpike`,
the AR(1) whitening gain — is a computation of this one quantity in a
particular basis. -/
theorem traceForm_spikeOuter (v : ι → ℝ) : traceForm (spikeOuter v) = dot v v := by
  unfold traceForm dot
  exact Finset.sum_congr rfl (fun i _ ↦ by simp only [spikeOuter])

/-- **The trace-window background class**: every legal background carries total
standardized variance at most `budget`.
    standardized genotype covariance the panel admits as background.

    Empirical status: UNTESTED. `budget` is measurable — it is the trace of the -/
def traceWindowBudgetClass (base : Matrix ι ι ℝ) (budget : ℝ) :
    BackgroundClass ι Unit where
  base := base
  form := fun _ ↦ traceForm
  bound := fun _ ↦ budget
  form_add := fun _ M N ↦ traceForm_add M N
  form_smul := fun _ c M ↦ traceForm_smul c M

theorem traceWindowBudgetClass_spikeLoad (base : Matrix ι ι ℝ) (budget : ℝ)
    (v : ι → ℝ) :
    (traceWindowBudgetClass base budget).spikeLoad () v = dot v v :=
  traceForm_spikeOuter v

theorem traceWindowBudgetClass_headroom (base : Matrix ι ι ℝ) (budget : ℝ)
    (S₀ : Matrix ι ι ℝ) :
    (traceWindowBudgetClass base budget).headroom () S₀ = budget - traceForm S₀ :=
  rfl

end Frobenius

/-!
## Threshold equals capacity on the equi-exit class

Equi-exit is the hypothesis that the binding constraint's spike load is
constant over the prior's support.  It is the precise content of the informal
"the likelihood ratio depends on the nuisance only through a quadratic form":
if the load varied over the support, different components of the mixture would
exit the class at different levels and there would be no single threshold to
speak of.  It is carried here as an explicit field of `EquiExit`, so no theorem
below can be read as holding more generally than it does.
-/

section EquiExitClass

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}

/-- **The equi-exit hypothesis, made explicit.**  One constraint `binding`
whose spike load is the same constant `load` in every supported direction, and
which attains the linear program's infimum.
    the prior, evaluate `ℓ_a(vvᵀ)` on each, and check the value is constant.

    Empirical status: UNTESTED. Directly falsifiable: draw effect vectors from -/
structure EquiExit (K : BackgroundClass ι cidx) (S₀ : Matrix ι ι ℝ)
    (support : Set (ι → ℝ)) where
  /-- The certificate: which constraint binds. -/
  binding : cidx
  /-- The common spike load of the binding constraint. -/
  load : ℝ
  load_pos : 0 < load
  /-- Some direction is actually supported. -/
  supported : ∃ v, v ∈ support
  /-- **Equi-exit.**  The binding constraint's load does not depend on the
  direction drawn from the effect prior. -/
  equi : ∀ v ∈ support, K.spikeLoad binding v = load
  /-- The binding constraint attains the infimum. -/
  binds : ∀ (a : cidx) (v : ι → ℝ), v ∈ support → 0 < K.spikeLoad a v →
    K.headroom binding S₀ / load ≤ K.headroom a S₀ / K.spikeLoad a v

/-- The one-constraint background class on a single coordinate, whose form reads
    the `(0,0)` entry. Additivity and homogeneity hold because matrix addition
    and scaling are pointwise. -/
noncomputable def diagonalEntryClass : BackgroundClass (Fin 1) Unit where
  base := 0
  form := fun _ M ↦ M 0 0
  bound := fun _ ↦ 1
  form_add := fun _ _ _ ↦ rfl
  form_smul := fun _ _ _ ↦ rfl

/-- **The equi-exit class is inhabited**, on a single constraint over a support
    containing one direction.

    Equi-exit says the binding constraint's load is the same in every supported
    direction, and `binds` says it attains the linear program's infimum. Both are
    forced here rather than arranged: with one constraint and one supported
    direction there is nothing for the load to vary over and nothing for the
    infimum to be taken against, so `binds` reduces to reflexivity.

    That is the honest reading of this witness. It shows the theorems over
    `EquiExit` are not vacuous; it does not show equi-exit holds for a class with
    several constraints, which is where the hypothesis has force. -/
noncomputable def EquiExit.witness (S₀ : Matrix (Fin 1) (Fin 1) ℝ) :
    EquiExit diagonalEntryClass S₀ {fun _ ↦ 1} where
  binding := ()
  load := 1
  load_pos := by norm_num
  supported := ⟨fun _ ↦ 1, rfl⟩
  equi := by
    intro v hv
    have hv' : v = fun _ ↦ (1 : ℝ) := hv
    subst hv'
    simp [BackgroundClass.spikeLoad, diagonalEntryClass, spikeOuter]
  binds := by
    intro a v hv _
    have hv' : v = fun _ ↦ (1 : ℝ) := hv
    subst hv'
    have ha : a = () := rfl
    subst ha
    simp [BackgroundClass.spikeLoad, diagonalEntryClass, spikeOuter]

namespace EquiExit

variable {K : BackgroundClass ι cidx} {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}

theorem exitLevels_nonempty (E : EquiExit K S₀ support) :
    (K.exitLevels S₀ support).Nonempty := by
  obtain ⟨v, hv⟩ := E.supported
  have hload : 0 < K.spikeLoad E.binding v := by
    rw [E.equi v hv]
    exact E.load_pos
  exact ⟨K.headroom E.binding S₀ / K.spikeLoad E.binding v,
    E.binding, v, hv, hload, rfl⟩

/-- **The linear program's value in closed form.**  On the equi-exit class the
infimum is attained at the binding constraint, so the capacity is a single
quotient: headroom over load. -/
theorem imitationCapacity_eq (E : EquiExit K S₀ support) (hnull : K.IsNull S₀) :
    K.imitationCapacity S₀ support = K.headroom E.binding S₀ / E.load := by
  obtain ⟨v, hv⟩ := E.supported
  have hloadv : K.spikeLoad E.binding v = E.load := E.equi v hv
  have hloadpos : 0 < K.spikeLoad E.binding v := by
    rw [hloadv]
    exact E.load_pos
  refine le_antisymm ?_ ?_
  · have hle := K.imitationCapacity_le hnull hv hloadpos
    rwa [hloadv] at hle
  · refine K.le_imitationCapacity E.exitLevels_nonempty ?_
    intro a w hw hload
    exact E.binds a w hw hload

/-- **The margin by which a level-`t` alternative overshoots the binding
constraint.**  It is positive above the capacity and nonpositive at or below
it, and it is the quantity the synthesized test is calibrated against.

    Empirical status: UNTESTED. -/
def margin (E : EquiExit K S₀ support) (t : ℝ) : ℝ :=
  t * E.load - K.headroom E.binding S₀

theorem margin_pos_of_gt_capacity (E : EquiExit K S₀ support)
    (hnull : K.IsNull S₀) {t : ℝ}
    (ht : K.imitationCapacity S₀ support < t) : 0 < E.margin t := by
  rw [E.imitationCapacity_eq hnull, div_lt_iff₀ E.load_pos] at ht
  unfold margin
  linarith

/-- **The certificate statistic's population value at the alternative.**  It
sits exactly `margin t` above the null ceiling: the certificate does not merely
correlate with detectability, it measures it. -/
theorem form_spiked_eq_bound_add_margin (E : EquiExit K S₀ support) (t : ℝ)
    {v : ι → ℝ} (hv : v ∈ support) :
    K.form E.binding (K.spiked S₀ t v) = K.bound E.binding + E.margin t := by
  rw [K.form_spiked, E.equi v hv]
  unfold margin BackgroundClass.headroom
  ring

/-- **The synthesized test.**  Reject when the empirical certificate statistic
exceeds the null ceiling plus half the margin.  There is no tuning parameter
and no oracle: both the ceiling and the margin are functionals of the declared
background class.

    Empirical status: UNTESTED. -/
def rejectionThreshold (E : EquiExit K S₀ support) (t : ℝ) : ℝ :=
  K.bound E.binding + E.margin t / 2

/-- **Null control.**  Whatever null covariance generated the data, if the
empirical certificate is within half the margin of its population value the
test does not reject.  This holds uniformly over the whole class, because the
ceiling is a property of the class rather than of any particular null. -/
theorem certificateTest_null_control (E : EquiExit K S₀ support)
    {S : Matrix ι ι ℝ} (hS : K.IsNull S) {empirical t ε : ℝ}
    (hε : ε ≤ E.margin t / 2)
    (hclose : |empirical - K.form E.binding S| ≤ ε) :
    empirical ≤ E.rejectionThreshold t := by
  have habs := abs_le.mp hclose
  have hbound := hS.2 E.binding
  unfold rejectionThreshold
  linarith [habs.2]

/-- **Power.**  Above the capacity the margin is positive; if the empirical
certificate is within strictly less than half the margin of its population
value at the alternative, the test rejects.  Together with null control this is
the achievability side of threshold-equals-capacity, at the level of the
certificate statistic. -/
theorem certificateTest_power (E : EquiExit K S₀ support)
    {t ε : ℝ} {v : ι → ℝ} (hv : v ∈ support) (hε : ε < E.margin t / 2)
    {empirical : ℝ}
    (hclose : |empirical - K.form E.binding (K.spiked S₀ t v)| ≤ ε) :
    E.rejectionThreshold t < empirical := by
  have hpop := E.form_spiked_eq_bound_add_margin t hv
  have habs := abs_le.mp hclose
  rw [hpop] at habs
  unfold rejectionThreshold
  linarith [habs.1]

end EquiExit

end EquiExitClass

/-!
## Rigidity is not a symmetry condition

**A background class does not need a transitive symmetry group to be rigid.** Rigidity is
not a consequence of the class being "the same in every direction": it is the normal-cone
condition of the previous section, and the following class witnesses it with a
completely generic positive-definite `A` and no symmetry at all: one linear
constraint, active at the baseline by construction, with spike load `vᵀAv > 0`
in every nonzero direction.
-/

section NoSymmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The one-constraint trace-window class.**  A single linear budget
`⟪A, Σ⟫ ≤ ⟪A, Σ₀⟫`, active at `Σ₀` by construction.

    Empirical status: UNTESTED. -/
def traceWindowClass (base A S₀ : Matrix ι ι ℝ) : BackgroundClass ι Unit where
  base := base
  form := fun _ ↦ frobeniusForm A
  bound := fun _ ↦ frobeniusForm A S₀
  form_add := fun _ M N ↦ frobeniusForm_add A M N
  form_smul := fun _ c M ↦ frobeniusForm_smul A c M

theorem traceWindowClass_active (base A S₀ : Matrix ι ι ℝ) :
    (traceWindowClass base A S₀).Active () S₀ := rfl

theorem traceWindowClass_spikeLoad (base A S₀ : Matrix ι ι ℝ) (v : ι → ℝ) :
    (traceWindowClass base A S₀).spikeLoad () v = quadForm A v :=
  frobeniusForm_spikeOuter A v

theorem traceWindowClass_isNull_baseline {base A S₀ : Matrix ι ι ℝ}
    (hbase : VarianceNonneg (S₀ - base)) :
    (traceWindowClass base A S₀).IsNull S₀ := by
  refine ⟨hbase, ?_⟩
  intro a
  exact le_refl _

/-- **Rigidity without symmetry.**  For any positive-definite `A` — generic,
with trivial automorphism group — the trace-window class has imitation capacity
zero: every spike direction points out of the class at `Σ₀`.  No symmetry
hypothesis appears in the statement or the proof, which refutes the conjecture
that rigidity requires a transitive group. -/
theorem traceWindow_rigid {base A S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (hpd : ∀ v : ι → ℝ, v ≠ 0 → 0 < quadForm A v)
    (hbase : VarianceNonneg (S₀ - base))
    {v : ι → ℝ} (hv : v ∈ support) (hvne : v ≠ 0) :
    (traceWindowClass base A S₀).imitationCapacity S₀ support = 0 := by
  refine (traceWindowClass base A S₀).imitationCapacity_eq_zero_of_active
    (traceWindowClass_isNull_baseline hbase) hv
    (traceWindowClass_active base A S₀) ?_
  rw [traceWindowClass_spikeLoad]
  exact hpd v hvne

/-- **The design instruction.**  Constrain the background class by an active
linear constraint with positive spike load and detection becomes possible where
it was information-theoretically impossible: at every positive level the spiked
covariance leaves the class, so the certificate statistic separates. -/
theorem traceWindow_every_level_detectable {base A S₀ : Matrix ι ι ℝ}
    (hpd : ∀ v : ι → ℝ, v ≠ 0 → 0 < quadForm A v)
    {v : ι → ℝ} (hvne : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    ¬ (traceWindowClass base A S₀).IsNull
      ((traceWindowClass base A S₀).spiked S₀ t v) := by
  refine (traceWindowClass base A S₀).not_isNull_spiked_of_active
    (traceWindowClass_active base A S₀) ?_ ht
  rw [traceWindowClass_spikeLoad]
  exact hpd v hvne

end NoSymmetry

/-!
## The rigidity mechanisms of `ImitationRigidity` are certificates

`Calibrator.ImitationRigidity` proves that a rank-one bump with unequal squared
loadings at a pair `(i, j)` separates two diagonal entries that agreed, and
that a bump moving a loading product separates two entries a shift had
identified.  Those theorems are now stated pointwise there, because inspecting
their proofs shows the global stationarity hypotheses were consumed only at the
witnessing pair.

This section is the statement that the pointwise hypothesis *is* the
certificate condition of this file: the diagonal gap is a linear functional,
its spike load is `vᵢ² - vⱼ²`, and an active diagonal-gap constraint with
positive load drives the imitation capacity to zero.  The mechanism generalizes
off stationary classes entirely, which matters because a standardized genotype
panel has unit diagonal — the constraint is active automatically — so the
loading condition is the whole of what rigidity requires there.
-/

section RigidityInstances

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The two spike parametrizations agree.**  `ImitationRigidity`'s bump at
scale `s` is this file's spike at level `s²`; the level is squared because the
bump's scale multiplies the effect vector while the level multiplies the
covariance. -/
theorem rankOneCovarianceBump_eq_smul_spikeOuter (scale : ℝ) (v : ι → ℝ) :
    rankOneCovarianceBump scale v = (scale ^ 2) • spikeOuter v := by
  ext i j
  simp only [rankOneCovarianceBump, Matrix.smul_apply, spikeOuter, smul_eq_mul]
  ring

/-- The linear program's alternative and `ImitationRigidity`'s bumped
background are the same matrix. -/
theorem spiked_eq_add_rankOneCovarianceBump {cidx : Type*}
    (K : BackgroundClass ι cidx) (S₀ : Matrix ι ι ℝ) (scale : ℝ) (v : ι → ℝ) :
    K.spiked S₀ (scale ^ 2) v = S₀ + rankOneCovarianceBump scale v := by
  unfold BackgroundClass.spiked
  rw [rankOneCovarianceBump_eq_smul_spikeOuter]

/-- **The diagonal-gap functional.**  The difference of two diagonal entries —
for a genotype covariance, the difference in standardized variance carried by
two markers.  It is linear, so it is a legal constraint of a background class,
and `ConstantDiagonal` is the statement that all of these vanish.

    Empirical status: DERIVED (a difference of matrix entries;
    `diagonalGapForm_spikeOuter` identifies its spike load). -/
def diagonalGapForm (i j : ι) (M : Matrix ι ι ℝ) : ℝ := M i i - M j j

theorem diagonalGapForm_add (i j : ι) (M N : Matrix ι ι ℝ) :
    diagonalGapForm i j (M + N) =
      diagonalGapForm i j M + diagonalGapForm i j N := by
  unfold diagonalGapForm
  simp only [Matrix.add_apply]
  ring

theorem diagonalGapForm_smul (i j : ι) (c : ℝ) (M : Matrix ι ι ℝ) :
    diagonalGapForm i j (c • M) = c * diagonalGapForm i j M := by
  unfold diagonalGapForm
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The spike load of the diagonal gap is the squared-loading gap.**  This is
the quantity `ImitationRigidity`'s `hloading` hypothesis asserts is nonzero, now
identified as a spike load rather than an algebraic coincidence. -/
theorem diagonalGapForm_spikeOuter (i j : ι) (v : ι → ℝ) :
    diagonalGapForm i j (spikeOuter v) = v i ^ 2 - v j ^ 2 := by
  unfold diagonalGapForm
  simp only [spikeOuter]
  ring

/-- **The diagonal-gap background class**: backgrounds in which two markers
differ in standardized variance by at most `budget`.  At `budget = 0` with the
constraint
active this is the constant-diagonal condition restricted to one pair, which is
all `ImitationRigidity` ever used.
    standardized variance a panel admits between two markers.

    Empirical status: UNTESTED. `budget` is measurable — it is the spread in -/
def diagonalGapClass (base : Matrix ι ι ℝ) (i j : ι) (budget : ℝ) :
    BackgroundClass ι Unit where
  base := base
  form := fun _ ↦ diagonalGapForm i j
  bound := fun _ ↦ budget
  form_add := fun _ M N ↦ diagonalGapForm_add i j M N
  form_smul := fun _ c M ↦ diagonalGapForm_smul i j c M

theorem diagonalGapClass_spikeLoad (base : Matrix ι ι ℝ) (i j : ι) (budget : ℝ)
    (a : Unit) (v : ι → ℝ) :
    (diagonalGapClass base i j budget).spikeLoad a v = v i ^ 2 - v j ^ 2 :=
  diagonalGapForm_spikeOuter i j v

/-- **The `ConstantDiagonal` mechanism, as a certificate.**  Two diagonal
entries that agree at the baseline are an active constraint; unequal squared
loadings are positive spike load; the imitation capacity is therefore zero.
Only the one pair is constrained — nothing is assumed about the rest of the
matrix, so the class is not Toeplitz, not stationary, and has no symmetry. -/
theorem diagonalGap_imitationCapacity_eq_zero
    {base S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)} {i j : ι}
    (hbase : VarianceNonneg (S₀ - base))
    (hactive : S₀ i i = S₀ j j)
    {v : ι → ℝ} (hv : v ∈ support) (hload : v j ^ 2 < v i ^ 2) :
    (diagonalGapClass base i j 0).imitationCapacity S₀ support = 0 := by
  have hgap : diagonalGapForm i j S₀ = 0 := by
    unfold diagonalGapForm
    rw [hactive]
    ring
  have hnull : (diagonalGapClass base i j 0).IsNull S₀ := by
    refine ⟨hbase, ?_⟩
    intro _a
    exact le_of_eq hgap
  have hactive' : (diagonalGapClass base i j 0).Active () S₀ := hgap
  have hload' : 0 < (diagonalGapClass base i j 0).spikeLoad () v := by
    rw [diagonalGapClass_spikeLoad]
    linarith
  exact (diagonalGapClass base i j 0).imitationCapacity_eq_zero_of_active
    hnull hv hactive' hload'

/-- **The two files draw the same conclusion.**  `ImitationRigidity`'s
`add_rankOneBump_diagonal_gap_ne_of_active` says the bumped background leaves
the constant-diagonal condition at the witnessing pair; this says the same
matrix is not a member of the diagonal-gap class.  Both are the normal-cone
condition, and neither needs stationarity. -/
theorem diagonalGap_not_isNull_add_rankOneCovarianceBump
    {base S₀ : Matrix ι ι ℝ} {i j : ι}
    (hactive : S₀ i i = S₀ j j) {scale : ℝ} (hscale : scale ≠ 0)
    {v : ι → ℝ} (hload : v j ^ 2 < v i ^ 2) :
    ¬ (diagonalGapClass base i j 0).IsNull
      (S₀ + rankOneCovarianceBump scale v) := by
  have hgap : diagonalGapForm i j S₀ = 0 := by
    unfold diagonalGapForm
    rw [hactive]
    ring
  have hactive' : (diagonalGapClass base i j 0).Active () S₀ := hgap
  have hload' : 0 < (diagonalGapClass base i j 0).spikeLoad () v := by
    rw [diagonalGapClass_spikeLoad]
    linarith
  have hscaleSq : (0 : ℝ) < scale ^ 2 := sq_pos_of_ne_zero hscale
  rw [← spiked_eq_add_rankOneCovarianceBump (diagonalGapClass base i j 0) S₀ scale v]
  exact (diagonalGapClass base i j 0).not_isNull_spiked_of_active
    hactive' hload' hscaleSq

end RigidityInstances

/-!
## The AR(1) whitening gain is the certificate value of the trace window

`Calibrator.ImitationRigidity` computes, for a stationary first-order LD kernel
with per-site retention `ρ`, the per-variant limit of `tr K⁻¹`:

    ldWhiteningGain ρ = (1 + ρ²) / (1 - ρ²),

the harmonic mean of the LD symbol.  That quantity IS a detection threshold, not merely
related to one: it is the spike load of
the whitened trace-window constraint under an isotropic effect prior, hence the
denominator of the linear program's value.  The isotropic prior is what
supplies equi-exit — the load is the same in every direction — so the threshold
equals the capacity by `EquiExit.imitationCapacity_eq`, and the capacity is
headroom divided by the whitening gain.
-/

section WhiteningGain

/-- **The finite-chromosome trace-window spike load**: the normalized trace of
the LD precision matrix, which is the value the trace-window certificate
assigns to a unit isotropic spike on `nSites` variants.

    Empirical status: DERIVED from `ldPrecisionTrace`, itself derived from the
    AR(1) precision stencil (`stationaryLD_interior_stencil`). -/
def traceWindowSpikeLoad (decay : ℝ) (nSites : ℕ) : ℝ :=
  ldPrecisionTrace decay nSites / (nSites : ℝ)

/-- **traceWindowSpikeLoad at its junk point, named.** Averaging a trace over no sites is
undefined. Lean returns `0`: no spike load, which is what a genuinely flat spectrum also gives.
Consumers must exclude the argument that makes the guard vanish. -/
theorem traceWindowSpikeLoad_no_sites_is_junk (decay : ℝ) :
    traceWindowSpikeLoad decay 0 = 0 := by
  unfold traceWindowSpikeLoad
  simp

/-- **The identification.**  The whitening gain already in the corpus *is* the
large-chromosome certificate value of the trace-window constraint.  This is
what turns `(1+ρ²)/(1-ρ²)` from a quantity correlated with detectability into
the denominator of the detection threshold. -/
theorem traceWindowSpikeLoad_tendsto_ldWhiteningGain {decay : ℝ}
    (hd : |decay| < 1) :
    Filter.Tendsto (traceWindowSpikeLoad decay) Filter.atTop
      (nhds (ldWhiteningGain decay)) := by
  unfold traceWindowSpikeLoad
  exact ldPrecisionTrace_div_sites_tendsto hd

/-- **The whitened capacity**: the linear program's value when the binding
constraint is the trace window and the effect prior is isotropic.

    Empirical status: UNTESTED. Directly testable: simulate AR(1) genotypes at
    known `ρ`, sweep the spike level, and compare the measured detection
    boundary against `headroom · (1 - ρ²) / (1 + ρ²)`. -/
def whitenedCapacity (headroom decay : ℝ) : ℝ :=
  headroom / ldWhiteningGain decay

/-- **whitenedCapacity at its junk point, named.** Two junk branches in sequence. At unit decay
the whitening gain divides by `1 - decay ^ 2` and is junk-zero, so the capacity divides by that
zero and is junk-zero in turn. A channel at perfect retention -- where the gain in fact diverges
-- is reported as having no capacity at all, and neither branch is visible in the value.
Consumers must exclude the argument that makes the guard vanish. -/
theorem whitenedCapacity_perfect_retention_is_junk (headroom : ℝ) :
    whitenedCapacity headroom 1 = 0 := by
  unfold whitenedCapacity ldWhiteningGain
  norm_num

theorem whitenedCapacity_closedForm (headroom decay : ℝ) :
    whitenedCapacity headroom decay =
      headroom * (1 - decay ^ 2) / (1 + decay ^ 2) := by
  unfold whitenedCapacity ldWhiteningGain
  rw [div_div_eq_mul_div]

/-- **Threshold equals capacity, for the LD certificate.**  When the binding
constraint is the trace window and the equi-exit load is the whitening gain,
the imitation capacity — and hence, by `EquiExit.imitationCapacity_eq` together
with the two halves of the certificate test, the detection threshold — is
headroom over `(1+ρ²)/(1-ρ²)`. -/
theorem imitationCapacity_eq_whitenedCapacity
    {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}
    {K : BackgroundClass ι cidx} {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (E : EquiExit K S₀ support) (hnull : K.IsNull S₀) {decay : ℝ}
    (hload : E.load = ldWhiteningGain decay) :
    K.imitationCapacity S₀ support =
      whitenedCapacity (K.headroom E.binding S₀) decay := by
  unfold whitenedCapacity
  rw [E.imitationCapacity_eq hnull, hload]

/-- **Stronger LD lowers the threshold.**  More LD means a larger whitening
gain, hence a smaller capacity: the imitation wall is lower on a strongly
linked chromosome, so a spike of a given size is easier to detect after
whitening.  This is the opposite of the intuition that LD only costs
information, and it is a consequence of the certificate being edge-sensitive. -/
theorem whitenedCapacity_strictAnti {headroom decay₁ decay₂ : ℝ}
    (hheadroom : 0 < headroom) (h₁ : 0 ≤ decay₁) (h₂ : |decay₂| < 1)
    (hlt : decay₁ < decay₂) :
    whitenedCapacity headroom decay₂ < whitenedCapacity headroom decay₁ := by
  have hup : decay₂ < 1 := (abs_lt.mp h₂).2
  have hd₁ : |decay₁| < 1 := by
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hg₁ : (0 : ℝ) < ldWhiteningGain decay₁ :=
    lt_of_lt_of_le zero_lt_one (ldWhiteningGain_ge_one hd₁)
  have hg₂ : (0 : ℝ) < ldWhiteningGain decay₂ :=
    lt_of_lt_of_le zero_lt_one (ldWhiteningGain_ge_one h₂)
  have hmono : ldWhiteningGain decay₁ < ldWhiteningGain decay₂ :=
    ldWhiteningGain_strictMono h₁ h₂ hlt
  unfold whitenedCapacity
  rw [div_lt_div_iff₀ hg₂ hg₁]
  exact mul_lt_mul_of_pos_left hmono hheadroom

end WhiteningGain

/-!
## The existing BBP threshold, as a case — and where it is not one

`Calibrator.PCCorrectability.Threshold` already contains a detection threshold
for a rank-one demographic spike: `demographicSpike n F m = 4 F · m(n-m)/n`
against `bbpProxyThreshold n M = √(n/M)`, with the sign of their difference,
`pcCorrectabilityMargin`, documented as "the detectable side of the phase
diagram".  That is the same object this file is about, so the two must be
related or one of them is wrong.  The relation is partial, and the part that
fails is the more useful finding.

**What is a case.**  Two of the three pieces are certificate values of the
trace window, exactly:

* `effectiveSubgroupSize n m` is the *spike load* — the squared length of the
  centered subgroup-contrast direction (`dot_demographicSpikeDirection`);
* `demographicSpike n F m` is the *certificate increment* — the spike level
  times that load (`demographicSpike_eq_level_mul_spikeLoad`). This theorem is
  intentionally convention-agnostic: `Calibrator.DemographicCapacity`
  separately wires the empirically Hudson-calibrated PC law and the exact
  Nei-normalized allele-contrast law. They are not the same specialization.

So the left-hand side of the existing comparison sits in exactly the place the
linear program puts it.

**What is not a case, and this is the finding.**  `bbpProxyThreshold` is *not*
a headroom.  A headroom is `κ_a - ℓ_a(Σ₀)`: a difference of values of a linear
functional, a property of the background class and the baseline covariance.
`√(n/M)` contains no covariance at all — only the design shape.  It is the
Marchenko–Pastur edge, the fluctuation scale of the *empirical* certificate,
which is the `ε` of `EquiExit.certificateTest_null_control`, not the `κ_a -
ℓ_a(Σ₀)` of the linear program.  This is consistent with the rest of the file
rather than an anomaly: the spectral edge is a certificate of nothing, which is
the same reason a participation-ratio `m_eff` cannot set a threshold.

Two consequences follow, and both are proved below.

1. `pcCorrectabilityMargin > 0` is **not sufficient** for detectability.  It
   omits the headroom term.  `imitable_despite_positive_pcCorrectabilityMargin`
   exhibits a spike that is a legal background — undetectable at any sample
   size — while the existing margin is positive.  The existing docstring's
   claim that a positive value is the detectable side holds only under an
   additional hypothesis.
2. That hypothesis is **rigidity**.  When the trace window is active at the
   baseline, the headroom is zero, `stratificationCertificateMargin` collapses
   to `pcCorrectabilityMargin`, and its sign is then exactly the statement that
   the alternative's certificate clears the null ceiling by more than the
   sampling fluctuation
   (`rigid_certificate_exceeds_ceiling_iff_pcCorrectabilityMargin_pos`).

So the existing threshold is the *estimation* half of threshold-equals-capacity
with the *imitation* half silently set to zero.  Both halves are needed, and
`bbpProxyThreshold_tendsto_zero` shows they dominate in opposite regimes: at
fixed panel size, adding markers drives the estimation barrier to zero and
leaves the capacity as the whole obstruction.
-/

section DemographicInstance

/-- **The subgroup-contrast direction**: the centered indicator of a subgroup of
size `m` in a panel of `n` individuals.  Centering is forced rather than
conventional — an uncentered indicator has a component along the all-ones
vector, which is the grand mean and not a contrast, and its trace-window spike
load is not `effectiveSubgroupSize`.

    Empirical status: DERIVED. `dot_demographicSpikeDirection` proves its
    squared length is `effectiveSubgroupSize`, which is what makes the latter a
    certificate value rather than a stipulated formula. -/
def subgroupContrast (n m : ℕ) : ℕ → ℝ :=
  twoBlock m (((n : ℝ) - (m : ℝ)) / (n : ℝ)) (-((m : ℝ) / (n : ℝ)))

/-- The subgroup contrast as a vector on the panel's individuals.

    Empirical status: DERIVED. -/
def demographicSpikeDirection (n m : ℕ) : Fin n → ℝ :=
  fun i ↦ subgroupContrast n m i.val

/-- **`effectiveSubgroupSize` is the squared length of the subgroup contrast.**
This is the theorem that stops `m(n-m)/n` from being a formula nothing can
contradict: it is the trace-window spike load of an explicitly constructed
direction, and any other centering would give a different number. -/
theorem dot_demographicSpikeDirection (n m : ℕ) (hmn : m ≤ n) (hn : 0 < n) :
    dot (demographicSpikeDirection n m) (demographicSpikeDirection n m) =
      effectiveSubgroupSize (n : ℝ) (m : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : ((n : ℝ)) ≠ 0 := ne_of_gt hn'
  have hpoint : ∀ i : Fin n,
      demographicSpikeDirection n m i * demographicSpikeDirection n m i =
        (subgroupContrast n m i.val) ^ 2 := by
    intro i
    unfold demographicSpikeDirection
    ring
  have hsq : dot (demographicSpikeDirection n m) (demographicSpikeDirection n m) =
      ∑ i ∈ Finset.range n, (subgroupContrast n m i) ^ 2 := by
    unfold dot
    rw [Finset.sum_congr rfl (fun i _ ↦ hpoint i)]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ (subgroupContrast n m i) ^ 2) n
  have hsplit : m + (n - m) = n := by omega
  have hrange : Finset.range n = Finset.range (m + (n - m)) := by rw [hsplit]
  rw [hsq, hrange]
  unfold subgroupContrast
  rw [sum_pow_twoBlock m (n - m) (((n : ℝ) - (m : ℝ)) / (n : ℝ))
      (-((m : ℝ) / (n : ℝ))) 2,
    Nat.cast_sub hmn, neg_sq, div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc,
    div_add_div_same]
  unfold effectiveSubgroupSize
  rw [div_eq_div_iff (pow_ne_zero 2 hne) hne]
  ring

theorem traceWindowBudgetClass_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : Matrix ι ι ℝ) (budget : ℝ) (a : Unit) (M : Matrix ι ι ℝ) :
    (traceWindowBudgetClass base budget).form a M = traceForm M := rfl

theorem traceWindowBudgetClass_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : Matrix ι ι ℝ) (budget : ℝ) (a : Unit) :
    (traceWindowBudgetClass base budget).bound a = budget := rfl

/-- **The spike load of the demographic direction is `effectiveSubgroupSize`.** -/
theorem traceWindow_spikeLoad_demographic {N : ℕ} (m : ℕ) (hmn : m ≤ N) (hN : 0 < N)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    (traceWindowBudgetClass base budget).spikeLoad a (demographicSpikeDirection N m) =
      effectiveSubgroupSize (N : ℝ) (m : ℝ) := by
  unfold BackgroundClass.spikeLoad
  rw [traceWindowBudgetClass_form, traceForm_spikeOuter]
  exact dot_demographicSpikeDirection N m hmn hN

/-- **`demographicSpike` is the trace-window certificate increment at an
abstract level coordinate.** The quantity is the amount by which a spike at
level `4F` raises the certificate: level times load, exactly the linear
program's left-hand side. No estimator convention is inferred here. The
Hudson BBP and Nei contrast specializations are intentionally distinct in
`Calibrator.DemographicCapacity`. -/
theorem demographicSpike_eq_level_mul_spikeLoad {N : ℕ} (m : ℕ) (F : ℝ)
    (hmn : m ≤ N) (hN : 0 < N)
    (base : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ) (a : Unit) :
    demographicSpike (N : ℝ) F (m : ℝ) =
      (4 * F) *
        (traceWindowBudgetClass base budget).spikeLoad a
          (demographicSpikeDirection N m) := by
  rw [traceWindow_spikeLoad_demographic m hmn hN base budget a]
  unfold demographicSpike
  ring

/-- **The certificate margin for a demographic spike**, with the class headroom
and the estimation-error scale as separate arguments, because they are separate
things and the existing `pcCorrectabilityMargin` conflates them by omitting the
first.

    Empirical status: UNTESTED. Falsifiable against a simulation that varies
    the trace-window budget at fixed `n`, `M`, `F`: the detection boundary must
    move with `headroom`, which `pcCorrectabilityMargin` predicts it does
    not. -/
def stratificationCertificateMargin (headroom n M F m : ℝ) : ℝ :=
  demographicSpike n F m - (headroom + bbpProxyThreshold n M)

/-- **The existing margin is this one at zero headroom.**  This is the precise
sense in which `pcCorrectabilityMargin` is a special case: it assumes the
background class has no room left. -/
theorem stratificationCertificateMargin_zero_headroom (n M F m : ℝ) :
    stratificationCertificateMargin 0 n M F m = pcCorrectabilityMargin n M F m := by
  unfold stratificationCertificateMargin pcCorrectabilityMargin
  ring

/-- **A positive `pcCorrectabilityMargin` does not imply detectability.**

The hypothesis `_hmargin` is deliberately unused, and its being unused is the
content: whenever the spike fits inside the trace-window budget, the spiked
covariance is a legal background and no test at any sample size can separate
it, however far the spike clears the spectral edge.  What the existing margin
omits is the headroom, and the omission is not conservative. -/
theorem imitable_despite_positive_pcCorrectabilityMargin
    {N : ℕ} (m : ℕ) (F markerCount : ℝ) (hF : 0 ≤ F) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ)
    (hbase : VarianceNonneg (S₀ - base))
    (hbudget : traceForm S₀ + demographicSpike (N : ℝ) F (m : ℝ) ≤ budget)
    (_hmargin : 0 < pcCorrectabilityMargin (N : ℝ) markerCount F (m : ℝ)) :
    (traceWindowBudgetClass base budget).IsNull
      ((traceWindowBudgetClass base budget).spiked S₀ (4 * F)
        (demographicSpikeDirection N m)) := by
  constructor
  · have hrewrite :
        (traceWindowBudgetClass base budget).spiked S₀ (4 * F)
              (demographicSpikeDirection N m) -
            (traceWindowBudgetClass base budget).base =
          (S₀ - base) + (4 * F) • spikeOuter (demographicSpikeDirection N m) := by
      unfold BackgroundClass.spiked
      exact add_sub_right_comm S₀
        ((4 * F) • spikeOuter (demographicSpikeDirection N m)) base
    rw [hrewrite]
    exact varianceNonneg_add hbase
      (varianceNonneg_smul (by linarith) (varianceNonneg_spikeOuter _))
  · intro a
    rw [BackgroundClass.form_spiked, traceWindowBudgetClass_form,
      traceWindowBudgetClass_bound,
      ← demographicSpike_eq_level_mul_spikeLoad m F hmn hN base budget a]
    exact hbudget

/-- **The converse: exceeding the budget leaves the class.**  Together with the
previous theorem this is the linear program in genotype terms — the demographic
spike is imitable exactly when it fits inside the trace-window headroom, and
`bbpProxyThreshold` plays no part in that question. -/
theorem not_isNull_of_demographicSpike_gt_budget
    {N : ℕ} (m : ℕ) (F : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (budget : ℝ)
    (hbudget : budget < traceForm S₀ + demographicSpike (N : ℝ) F (m : ℝ)) :
    ¬ (traceWindowBudgetClass base budget).IsNull
      ((traceWindowBudgetClass base budget).spiked S₀ (4 * F)
        (demographicSpikeDirection N m)) := by
  intro hcontra
  have hle := hcontra.2 ()
  rw [BackgroundClass.form_spiked, traceWindowBudgetClass_form,
    traceWindowBudgetClass_bound,
    ← demographicSpike_eq_level_mul_spikeLoad m F hmn hN base budget ()] at hle
  linarith

/-- **Under rigidity the existing margin is the criterion, exactly.**

When the trace window is active at the baseline — budget equal to the
baseline's own certificate value, so the headroom is zero — the sign of
`pcCorrectabilityMargin` is precisely the statement that the alternative's
certificate value clears the null ceiling by more than the sampling
fluctuation.  This is the hypothesis under which the existing docstring's claim
is true. -/
theorem rigid_certificate_exceeds_ceiling_iff_pcCorrectabilityMargin_pos
    {N : ℕ} (m : ℕ) (F markerCount : ℝ) (hmn : m ≤ N) (hN : 0 < N)
    (base S₀ : Matrix (Fin N) (Fin N) ℝ) (a : Unit) :
    0 < pcCorrectabilityMargin (N : ℝ) markerCount F (m : ℝ) ↔
      (traceWindowBudgetClass base (traceForm S₀)).bound a +
          bbpProxyThreshold (N : ℝ) markerCount <
        (traceWindowBudgetClass base (traceForm S₀)).form a
          ((traceWindowBudgetClass base (traceForm S₀)).spiked S₀ (4 * F)
            (demographicSpikeDirection N m)) := by
  rw [BackgroundClass.form_spiked, traceWindowBudgetClass_form,
    traceWindowBudgetClass_bound,
    ← demographicSpike_eq_level_mul_spikeLoad m F hmn hN base (traceForm S₀) a]
  unfold pcCorrectabilityMargin
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **The estimation barrier vanishes with markers; the capacity does not.**
At fixed panel size, `√(n/M) → 0` as the effectively independent marker count
grows, so the spectral-edge term is asymptotically free and the imitation
capacity is the whole of what remains.  This is why the two halves cannot be
collapsed into one: they dominate in opposite regimes. -/
theorem bbpProxyThreshold_tendsto_zero (n : ℝ) :
    Filter.Tendsto (fun M : ℕ ↦ bbpProxyThreshold n (M : ℝ)) Filter.atTop
      (nhds 0) := by
  have hdiv : Filter.Tendsto (fun M : ℕ ↦ n / (M : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat n
  have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hdiv
  change Filter.Tendsto (fun M : ℕ ↦ Real.sqrt (n / (M : ℝ))) Filter.atTop (nhds 0)
  simpa only [Function.comp_apply, Real.sqrt_zero] using hcomp

end DemographicInstance

/-!
## The `m_eff` prohibition

Multiple-testing corrections in statistical genetics replace the raw variant
count by an *effective number of independent markers* computed from the
eigenvalues of the LD matrix: the Cheverud–Nyholt and Li–Ji family.  Every
member of that family is a participation-ratio-flavoured functional of the
empirical spectral distribution — it depends on the eigenvalues only through
their normalized moments, and it is therefore continuous in the weak topology.

The theorem below says no such functional can determine a detection threshold.
The witness is explicit and finite.  On `m = n + n²` markers, perturb the `n`
smallest eigenvalues from `1` down to `1/(n+1)` — a vanishing fraction,
`1/(n+1)`, of the spectrum.  Then:

* every normalized moment moves by at most `1/(n+1)`, so the weak limit is
  unchanged and every weakly continuous functional agrees asymptotically;
* the inverse-trace certificate moves from `1` to `1 + n/(n+1)`, a factor
  approaching two.

So the threshold is discontinuous in the weak topology.

**This has been measured, and the prohibition holds.**
`proofs/validation/empirical/meff_prohibition/check_meff_prohibition.py` builds both
spectra, computes the Li–Ji / Cheverud–Nyholt effective-marker count on each,
and bisects for the spike level at which the whitened certificate statistic
attains 50% power at level 0.05.  Across `n = 4, 8, 16` (so `m = 20, 72, 272`):

    n     m_eff ratio    certificate ratio    measured threshold ratio
    4        0.9951           1.8000                  1.8415
    8        0.9989           1.8889                  1.9679
    16       0.9998           1.9412                  1.9942

The measured ratio tracks the certificate to within `0.04`–`0.08` and misses
the effective-marker count by `0.85`–`0.99`.  The design has power: the two
predictions are a factor of two apart and diverge further with `n`, so the
comparison could have come out the other way and did not.  The largest
normalized-moment gap over `p = 1..4` was `0.19968`, `0.11109`, `0.05882`
against the bound `1/(n+1) = 0.2`, `0.11111`, `0.05882` that
`meff_moment_gap_le` proves — so that bound is not merely valid but tight.

This is the same fact, seen from the other side, as
`traceWindowSpikeLoad_tendsto_ldWhiteningGain`:
the corpus's `tr K⁻¹`-based whitening gain is the right functional *because* it
is edge-sensitive and not weakly continuous, and an `m_eff` of the
participation-ratio type is the wrong one for exactly the reason it is weakly
continuous.  The two facts are consistent, and their consistency is the point.
-/

section MeffProhibition

/-- **A two-block spectrum**: the first `k` eigenvalues equal `ε`, the rest
equal `1`.

    Empirical status: DERIVED. A witness construction, not a claim about any
    real LD matrix; its only role is to be a legal spectrum. -/
def blockSpectrum (k : ℕ) (ε : ℝ) : ℕ → ℝ := twoBlock k ε 1

/-- **The `p`-th normalized moment of the leading `m` eigenvalues.**  Weak
convergence of empirical spectral distributions with bounded support is
convergence of all of these, so a functional determined by them is precisely a
weakly continuous one.

    Empirical status: DERIVED. -/
def normalizedMoment (m : ℕ) (lam : ℕ → ℝ) (p : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, lam i ^ p) / (m : ℝ)

/-- **normalizedMoment over an empty index, named.** A spectrum with no eigenvalues has no
normalised moment. `Finset.range 0` is empty and the divisor is zero, so every moment of every
order is reported as `0` -- including the zeroth, which is one for any nonempty spectrum.
Consumers must require a nonempty index. -/
theorem normalizedMoment_empty_spectrum_is_junk (lam : ℕ → ℝ) (p : ℕ) :
    normalizedMoment 0 lam p = 0 := by
  unfold normalizedMoment
  simp

/-- **The inverse-trace certificate**: `tr K⁻¹ / m` in eigenvalue coordinates.
This is the quantity `ldWhiteningGain` computes in closed form for an AR(1)
kernel, and the one the linear program identifies as the detection threshold's
denominator.

    Empirical status: DERIVED. In the AR(1) case it is `traceWindowSpikeLoad`,
    by the definition of `ldPrecisionTrace` as the trace of the inverse. -/
def inverseTraceCertificate (m : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range m, (lam i)⁻¹) / (m : ℝ)

/-- **inverseTraceCertificate over an empty index, named.** The certificate averages inverse
eigenvalues, and over an empty spectrum both the sum and the count vanish. Lean returns `0`: the
strongest possible certificate -- an inverse trace of zero means no small eigenvalue anywhere --
issued for a matrix with no eigenvalues at all. Consumers must require a nonempty index. -/
theorem inverseTraceCertificate_empty_spectrum_is_junk (lam : ℕ → ℝ) :
    inverseTraceCertificate 0 lam = 0 := by
  unfold inverseTraceCertificate
  simp

/-! ### The certificate and the AR(1) whitening gain are one quantity

`ldWhiteningGain ρ = (1+ρ²)/(1-ρ²)` is the corpus's existing claim about what
governs detection after whitening.  The two theorems here make that claim true
rather than asserted: for a spectrum that *is* the AR(1) LD spectrum — the
hypothesis is explicit and checkable, being an identity between the sum of
inverse eigenvalues and `ldPrecisionTrace` — the certificate of the `m_eff`
prohibition below is the trace-window spike load, and its limit is the
whitening gain.  So the object the prohibition says is irreplaceable and the
object `ImitationRigidity` computes in closed form are the same object.
-/

/-- **The inverse-trace certificate of an AR(1) LD spectrum is the trace-window
spike load.**  The hypothesis says `lam` is the spectrum of the stationary LD
matrix on `m` sites, in the only form the statement needs: its inverse-trace
agrees with `ldPrecisionTrace`. -/
theorem inverseTraceCertificate_eq_traceWindowSpikeLoad {decay : ℝ} {m : ℕ}
    (lam : ℕ → ℝ)
    (hspectrum : ∑ i ∈ Finset.range m, (lam i)⁻¹ = ldPrecisionTrace decay m) :
    inverseTraceCertificate m lam = traceWindowSpikeLoad decay m := by
  unfold inverseTraceCertificate traceWindowSpikeLoad
  rw [hspectrum]

/-- **The certificate's large-chromosome limit is the whitening gain.**  This
is the theorem the corpus was missing: `(1+ρ²)/(1-ρ²)` is not merely correlated
with detectability, it is the limiting value of the certificate that
`certificate_not_momentContinuous` proves no weakly continuous functional can
reproduce. -/
theorem inverseTraceCertificate_tendsto_ldWhiteningGain {decay : ℝ}
    (hd : |decay| < 1) (lam : ℕ → ℕ → ℝ)
    (hspectrum : ∀ m : ℕ,
      ∑ i ∈ Finset.range m, (lam m i)⁻¹ = ldPrecisionTrace decay m) :
    Filter.Tendsto (fun m : ℕ ↦ inverseTraceCertificate m (lam m)) Filter.atTop
      (nhds (ldWhiteningGain decay)) := by
  have hrewrite : (fun m : ℕ ↦ inverseTraceCertificate m (lam m)) =
      traceWindowSpikeLoad decay := by
    funext m
    exact inverseTraceCertificate_eq_traceWindowSpikeLoad (lam m) (hspectrum m)
  rw [hrewrite]
  exact traceWindowSpikeLoad_tendsto_ldWhiteningGain hd

theorem normalizedMoment_blockSpectrum (k j : ℕ) (ε : ℝ) (p : ℕ) :
    normalizedMoment (k + j) (blockSpectrum k ε) p =
      ((k : ℝ) * ε ^ p + (j : ℝ)) / ((k : ℝ) + (j : ℝ)) := by
  unfold normalizedMoment blockSpectrum
  rw [sum_pow_twoBlock k j ε 1 p, one_pow, mul_one]
  push_cast
  ring

theorem inverseTraceCertificate_blockSpectrum (k j : ℕ) (ε : ℝ) :
    inverseTraceCertificate (k + j) (blockSpectrum k ε) =
      ((k : ℝ) * ε⁻¹ + (j : ℝ)) / ((k : ℝ) + (j : ℝ)) := by
  unfold inverseTraceCertificate blockSpectrum
  rw [sum_inv_twoBlock k j ε 1, inv_one, mul_one]
  push_cast
  ring

/-- **Every normalized moment is insensitive to the perturbation.**  Moving a
`1/(n+1)` fraction of the spectrum anywhere inside `[0,1]` moves every
normalized moment by at most `1/(n+1)`, uniformly in the order `p`.  This is
the precise sense in which the two spectra have the same weak limit. -/
theorem blockSpectrum_moment_gap_le (n p : ℕ) (ε : ℝ) (hn : 0 < n)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |normalizedMoment (n + n * n) (blockSpectrum n ε) p -
      normalizedMoment (n + n * n) (blockSpectrum n 1) p| ≤ 1 / ((n : ℝ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hD : (0 : ℝ) < (n : ℝ) + (n : ℝ) * (n : ℝ) := by nlinarith
  have hpow0 : (0 : ℝ) ≤ ε ^ p := pow_nonneg hε0 p
  have hpow1 : ε ^ p ≤ 1 := pow_le_one₀ hε0 hε1
  have hP : normalizedMoment (n + n * n) (blockSpectrum n ε) p =
      ((n : ℝ) * ε ^ p + (n : ℝ) * (n : ℝ)) /
        ((n : ℝ) + (n : ℝ) * (n : ℝ)) := by
    rw [normalizedMoment_blockSpectrum n (n * n) ε p]
    push_cast
    ring
  have hF : normalizedMoment (n + n * n) (blockSpectrum n 1) p =
      ((n : ℝ) * 1 + (n : ℝ) * (n : ℝ)) / ((n : ℝ) + (n : ℝ) * (n : ℝ)) := by
    rw [normalizedMoment_blockSpectrum n (n * n) 1 p, one_pow]
    push_cast
    ring
  have hnum : (n : ℝ) * ε ^ p + (n : ℝ) * (n : ℝ) -
      ((n : ℝ) * 1 + (n : ℝ) * (n : ℝ)) = (n : ℝ) * (ε ^ p - 1) := by ring
  have habs : |ε ^ p - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hP, hF, div_sub_div_same, hnum, abs_div, abs_of_pos hD, abs_mul,
    abs_of_pos hn', div_le_div_iff₀ hD hn1]
  nlinarith [mul_nonneg (mul_nonneg (le_of_lt hn') (le_of_lt hn1))
    (sub_nonneg.mpr habs), abs_nonneg (ε ^ p - 1)]

/-- The perturbed spectrum of the witness: on `n + n²` markers, the `n`
smallest eigenvalues pushed down to `1/(n+1)`.

    Empirical status: DERIVED (witness construction). -/
def meffPerturbed (n : ℕ) : ℕ → ℝ := blockSpectrum n (((n : ℝ) + 1)⁻¹)

/-- The unperturbed comparison spectrum: flat at `1`.

    Empirical status: DERIVED (witness construction). -/
def meffFlat (n : ℕ) : ℕ → ℝ := blockSpectrum n 1

/-- The number of markers in the witness at stage `n`.

    Empirical status: DERIVED (witness construction). -/
def meffSize (n : ℕ) : ℕ := n + n * n

/-- **The two witness spectra agree on every normalized moment to within
`1/(n+1)`.**  They therefore have the same weak limit and agree asymptotically
on every weakly continuous functional, every fixed normalized moment
included. -/
theorem meff_moment_gap_le (n p : ℕ) (hn : 0 < n) :
    |normalizedMoment (meffSize n) (meffPerturbed n) p -
      normalizedMoment (meffSize n) (meffFlat n) p| ≤ 1 / ((n : ℝ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hεpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hn1
  have hεmul : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hn1)
  have hε1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by nlinarith [mul_pos hεpos hn']
  exact blockSpectrum_moment_gap_le n p (((n : ℝ) + 1)⁻¹) hn (le_of_lt hεpos) hε1

/-- **The inverse-trace certificate moves by `n/(n+1)` — a constant — between
the same two spectra.**  This is the discontinuity: the certificate is not
determined by the weak limit. -/
theorem meff_certificate_gap (n : ℕ) (hn : 0 < n) :
    inverseTraceCertificate (meffSize n) (meffPerturbed n) -
      inverseTraceCertificate (meffSize n) (meffFlat n) =
      (n : ℝ) / ((n : ℝ) + 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hD : (0 : ℝ) < (n : ℝ) + (n : ℝ) * (n : ℝ) := by nlinarith
  have hP : inverseTraceCertificate (meffSize n) (meffPerturbed n) =
      ((n : ℝ) * ((n : ℝ) + 1) + (n : ℝ) * (n : ℝ)) /
        ((n : ℝ) + (n : ℝ) * (n : ℝ)) := by
    unfold meffSize meffPerturbed
    rw [inverseTraceCertificate_blockSpectrum n (n * n) (((n : ℝ) + 1)⁻¹), inv_inv]
    push_cast
    ring
  have hF : inverseTraceCertificate (meffSize n) (meffFlat n) =
      ((n : ℝ) * 1 + (n : ℝ) * (n : ℝ)) / ((n : ℝ) + (n : ℝ) * (n : ℝ)) := by
    unfold meffSize meffFlat
    rw [inverseTraceCertificate_blockSpectrum n (n * n) 1, inv_one]
    push_cast
    ring
  have hnum : (n : ℝ) * ((n : ℝ) + 1) + (n : ℝ) * (n : ℝ) -
      ((n : ℝ) * 1 + (n : ℝ) * (n : ℝ)) = (n : ℝ) * (n : ℝ) := by ring
  rw [hP, hF, div_sub_div_same, hnum,
    div_eq_div_iff (ne_of_gt hD) (ne_of_gt hn1)]
  ring

/-- **A functional of the spectrum determined by its low-order normalized
moments**, with an explicit modulus of continuity.  Every member of the
Cheverud–Nyholt and Li–Ji effective-marker family has this shape: each is a
fixed algebraic combination of `∑λ`, `∑λ²` and the marker count, divided by
`m`, so a uniform bound on moment differences bounds the difference of values.

    Empirical status: UNTESTED. This is the abstraction of the `m_eff` family,
    and the prohibition below is exactly as strong as the claim that the family
    lands inside it. -/
structure MomentContinuousFunctional where
  /-- The value assigned to the leading `m` eigenvalues of a spectrum. -/
  value : ℕ → (ℕ → ℝ) → ℝ
  /-- The highest moment order the functional consults. -/
  order : ℕ
  /-- The modulus of continuity in the moment metric. -/
  modulus : ℝ
  modulus_nonneg : 0 ≤ modulus
  /-- Continuity in the weak (moment) topology, quantitatively. -/
  moment_lipschitz : ∀ (m : ℕ) (lam mu : ℕ → ℝ) (δ : ℝ), 0 ≤ δ →
    (∀ p, p ≤ order → |normalizedMoment m lam p - normalizedMoment m mu p| ≤ δ) →
    |value m lam - value m mu| ≤ modulus * δ

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MomentContinuousFunctional.witness : MomentContinuousFunctional where
  value := fun _ _ ↦ 0
  order := 0
  modulus := 0
  modulus_nonneg := le_refl 0
  moment_lipschitz := fun _ _ _ _ _ _ ↦ by simp

/-- **The `m_eff` prohibition.**  No weakly continuous functional of the
spectral law can equal the inverse-trace certificate — hence no
participation-ratio-type effective-marker count can determine a detection
threshold.

The proof is the witness: at stage `n` the two spectra differ by at most
`1/(n+1)` in every moment, so any moment-continuous functional differs by at
most `C/(n+1)`, while the certificates differ by `n/(n+1)`.  Equality would
force `n ≤ C` for every `n`.

Read the other way, this is why `ldWhiteningGain` is the right quantity: it is
a certificate value, edge-sensitive, and outside this class. -/
theorem certificate_not_momentContinuous (Φ : MomentContinuousFunctional)
    (hΦ : ∀ (m : ℕ) (lam : ℕ → ℝ), Φ.value m lam = inverseTraceCertificate m lam) :
    False := by
  obtain ⟨n, hn⟩ := exists_nat_gt Φ.modulus
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hzero | hpos
    · exfalso
      rw [hzero] at hn
      have hneg : Φ.modulus < 0 := by exact_mod_cast hn
      linarith [Φ.modulus_nonneg]
    · exact hpos
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1
  have hδ : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := le_of_lt (by positivity)
  have hlip := Φ.moment_lipschitz (meffSize n) (meffPerturbed n) (meffFlat n)
    (1 / ((n : ℝ) + 1)) hδ (fun p _ ↦ meff_moment_gap_le n p hnpos)
  simp only [hΦ] at hlip
  rw [meff_certificate_gap n hnpos] at hlip
  rw [abs_of_nonneg (le_of_lt (div_pos hn' hn1))] at hlip
  have hsimp : Φ.modulus * (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = Φ.modulus := by
    rw [mul_assoc, one_div, inv_mul_cancel₀ hne, mul_one]
  rw [div_le_iff₀ hn1, hsimp] at hlip
  linarith

/-- **The witness spectra are legal LD spectra.**  Every eigenvalue is strictly
positive, so both are spectra a correlation matrix can have; the prohibition is
not evaded by restricting attention to spectra a real LD matrix could
produce. -/
theorem meffWitness_spectrum_pos (n i : ℕ) :
    0 < meffPerturbed n i ∧ 0 < meffFlat n i := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  constructor
  · unfold meffPerturbed blockSpectrum twoBlock
    split_ifs
    · exact inv_pos.mpr hn1
    · exact zero_lt_one
  · unfold meffFlat blockSpectrum twoBlock
    split_ifs
    · exact zero_lt_one
    · exact zero_lt_one

/-- The two witness panels agree on the normalized trace — the `p = 1` moment,
which is what fixes a correlation matrix's normalization — to within
`1/(n+1)`. -/
theorem meff_normalizedTrace_gap_le (n : ℕ) (hn : 0 < n) :
    |normalizedMoment (meffSize n) (meffPerturbed n) 1 -
      normalizedMoment (meffSize n) (meffFlat n) 1| ≤ 1 / ((n : ℝ) + 1) :=
  meff_moment_gap_le n 1 hn

/-- **Both halves, in one statement.**

Negative half: no effective-marker count of the participation-ratio family — no
functional continuous in the moments of the LD spectrum — equals the whitening
certificate, so none can determine a detection threshold.

Positive half: the certificate does determine one.  Its large-panel limit is
the AR(1) whitening gain, and the threshold is headroom divided by that gain,
in closed form.

The two are consistent because the certificate is edge-sensitive and therefore
outside the weakly continuous class, which is precisely the property that
disqualifies `m_eff` and qualifies `tr K⁻¹`. -/
theorem meff_prohibition_with_certificate {decay : ℝ} (hd : |decay| < 1)
    (lam : ℕ → ℕ → ℝ)
    (hspectrum : ∀ m : ℕ,
      ∑ i ∈ Finset.range m, (lam m i)⁻¹ = ldPrecisionTrace decay m)
    (Φ : MomentContinuousFunctional) :
    Filter.Tendsto (fun m : ℕ ↦ inverseTraceCertificate m (lam m)) Filter.atTop
        (nhds (ldWhiteningGain decay)) ∧
      (∀ headroom : ℝ, whitenedCapacity headroom decay =
        headroom * (1 - decay ^ 2) / (1 + decay ^ 2)) ∧
      ¬ (∀ (m : ℕ) (s : ℕ → ℝ), Φ.value m s = inverseTraceCertificate m s) :=
  ⟨inverseTraceCertificate_tendsto_ldWhiteningGain hd lam hspectrum,
    fun headroom ↦ whitenedCapacity_closedForm headroom decay,
    fun h ↦ certificate_not_momentContinuous Φ h⟩

end MeffProhibition

/-!
## One correction serving several targets: the obstruction is a variance

A correction fitted for one target and reused for several is the same object as
a background class serving several testing problems.  The degradation calculus
states the obstruction exactly: the irreducible part of a shared correction is
the energy-weighted variance of the per-target optimal corrections, and the
correctable part is the coboundary that a single shared correction removes.

This section proves that law and connects it to the linear program.  The bridge
is short and it is exact, not asymptotic:

* `weighted_dispersion_eq` is the obstruction law — for any shared correction
  `s`, the weighted loss splits as variance plus the squared distance from the
  energy-weighted mean.  The variance is what no choice of `s` removes, so it
  is the irreducible part, and the mean is the optimal shared correction.
* That irreducible residual is uncorrected background structure, so it consumes
  headroom.  Since the equi-exit capacity is headroom over load,
  `sharedCorrection_capacity_deficit` gives the price of sharing in the LP's own
  units: exactly variance divided by spike load.

**Why the deficit is not a variance of exit levels.**  The load-weighted variance
of the per-target *exit levels*, taken to second order in their spread, cannot
be the deficit.  The deficit of a minimum against a mean is first order in the
spread, not second, so no variance matches it.  The variance in the degradation
law is a variance of *corrections*, not of exit levels.  The statement proved
here needs no approximation and no order condition: the variance enters the
numerator of the LP additively and the deficit is exactly `V / load`.

**Why sharing is cheap and rotation is not.**  The two operations enter the LP
in different places, which is a structural explanation of the measured
ordering rather than a coincidence of scale.  Sharing perturbs the *numerator*:
it subtracts `V` from the headroom, so the capacity falls by `V / load`,
linearly and additively, and if `V` is a `10⁻⁵` fraction of signal energy then
the capacity moves by a `10⁻⁵` fraction too.  Rotation changes which constraint
binds, hence the *denominator*: by
`imitationCapacity_mul_load_eq_headroom` the product of capacity and load is
the headroom and is what stays fixed, so a change of binding constraint moves
the capacity by the ratio of the two loads, which is multiplicative and
unbounded.  Additive-and-tiny against multiplicative-and-unbounded is exactly
the reported ordering.
-/

section SharedCorrection

variable {tgt : Type*} [Fintype tgt]

/-- **Energy-weighted mean of the per-target optimal corrections.**  The weights
are the targets' energies, normalized to sum to one.

    Empirical status: UNTESTED. -/
def weightedMean (w c : tgt → ℝ) : ℝ := ∑ t, w t * c t

/-- **Energy-weighted variance of the per-target optimal corrections.**  The
degradation calculus's irreducible part: the component of the correction that
no single shared choice removes.
    target, take the energy-weighted spread.

    Empirical status: UNTESTED. Measurable directly — fit a correction per -/
def energyWeightedVariance (w c : tgt → ℝ) : ℝ :=
  ∑ t, w t * (c t - weightedMean w c) ^ 2

theorem weighted_sq_expand (w c : tgt → ℝ) (s : ℝ) :
    ∑ t, w t * (c t - s) ^ 2 =
      (∑ t, w t * c t ^ 2) - 2 * s * (∑ t, w t * c t) + s ^ 2 * (∑ t, w t) := by
  have hpoint : ∀ t : tgt, w t * (c t - s) ^ 2 =
      w t * c t ^ 2 - 2 * s * (w t * c t) + s ^ 2 * w t := fun t ↦ by ring
  rw [Finset.sum_congr rfl (fun t _ ↦ hpoint t), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The obstruction law.**  For any shared correction `s`, the energy-weighted
loss is the variance plus the squared distance from the energy-weighted mean.
The variance is the part no choice of `s` can remove — the irreducible class —
and the mean is the optimal shared correction. -/
theorem weighted_dispersion_eq (w c : tgt → ℝ) (hw : ∑ t, w t = 1) (s : ℝ) :
    ∑ t, w t * (c t - s) ^ 2 =
      energyWeightedVariance w c + (s - weightedMean w c) ^ 2 := by
  unfold energyWeightedVariance weightedMean
  rw [weighted_sq_expand w c s, weighted_sq_expand w c (∑ t, w t * c t), hw]
  ring

/-- **The variance is a floor on every shared correction.** -/
theorem energyWeightedVariance_le (w c : tgt → ℝ) (hw : ∑ t, w t = 1) (s : ℝ) :
    energyWeightedVariance w c ≤ ∑ t, w t * (c t - s) ^ 2 := by
  rw [weighted_dispersion_eq w c hw s]
  nlinarith [sq_nonneg (s - weightedMean w c)]

/-- **And the floor is attained, at the energy-weighted mean.**  Together with
the previous theorem this is the exact law: the obstruction to one correction
serving several targets is the energy-weighted variance, no more and no
less. -/
theorem energyWeightedVariance_attained (w c : tgt → ℝ) :
    ∑ t, w t * (c t - weightedMean w c) ^ 2 = energyWeightedVariance w c := rfl

/-- **The price of sharing, in the linear program's own units.**  The
irreducible residual is uncorrected background structure and so consumes
headroom; since the equi-exit capacity is headroom over spike load, sharing one
correction across targets lowers the capacity by exactly the energy-weighted
variance divided by the load.  Additive in the numerator, and exact. -/
theorem sharedCorrection_capacity_deficit (headroom load V : ℝ) :
    headroom / load - (headroom - V) / load = V / load := by
  rw [div_sub_div_same]
  congr 1
  ring

end SharedCorrection

section CapacityInvariant

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {cidx : Type*}

/-- **Capacity times load is the headroom.**  This is the invariant that
separates the two ways of degrading a shared correction: sharing moves the
headroom, and therefore the capacity, additively; changing which constraint
binds leaves the headroom alone and moves the capacity by the ratio of loads,
multiplicatively. -/
theorem imitationCapacity_mul_load_eq_headroom
    {K : BackgroundClass ι cidx} {S₀ : Matrix ι ι ℝ} {support : Set (ι → ℝ)}
    (E : EquiExit K S₀ support) (hnull : K.IsNull S₀) :
    K.imitationCapacity S₀ support * E.load = K.headroom E.binding S₀ := by
  rw [E.imitationCapacity_eq hnull, div_mul_eq_mul_div, mul_div_assoc,
    div_self (ne_of_gt E.load_pos), mul_one]


/-! ## The linkage-disequilibrium spectrum does not determine portability

`normalizedMoment` and `inverseTraceCertificate` above summarise a design by its
eigenvalues. Every quantity in this corpus that reads a design through those two
is therefore a function of the spectrum alone, and the question is whether that
is enough.

It is not, and the obstruction is visible in two dimensions. Take a block that is
diagonal in the variant basis and the same block rotated by forty-five degrees:

    D a = ⟪a, 0; 0, a+1⟫        R a = ⟪a+½, ½; ½, a+½⟫

`R a` is `U (D a) Uᵀ` for the rotation `U`, so the two are EXACTLY isospectral --
same trace, same determinant, hence the same characteristic polynomial at every
`a`, not merely the same limiting spectral law. No eigenvalue summary can
separate them.

But the entrywise cube sum `∑ᵢⱼ Σᵢⱼ³` differs: `9` against `7` at `a = 1`. That
quantity is not a spectral invariant, and it is the first non-spectral coordinate
of the low signal-to-noise expansion of the mutual information, entering at third
order multiplied by the SQUARE OF THE PRIOR'S THIRD CUMULANT.

The biology is in that last factor, and it does NOT go the way one would first
guess. For a symmetric effect prior the third cumulant vanishes and this
particular obstruction is inactive -- and in genetics it vanishes by force, not
by convention. Which allele is called `alternate` is a reference-genome
bookkeeping choice, so flipping it sends `x` to `-x` and any coding-invariant
prior must be symmetric. Every deployed polygenic prior is: BayesR's centred
normal mixture, PRS-CS's continuous shrinkage, LDpred's spike and slab. All have
`κ₃ = 0`, so the cube-sum obstruction is switched off for standard scores.

Two things follow. The obstruction reappears at the next order, where the
relevant invariant is the entrywise FOURTH power sum, and `κ₄` does not vanish
for a sparse prior -- sparsity is exactly what makes it nonzero. That case is
below, and it is the one that bears on polygenic scores. And the third-order
obstruction switches back ON under any functional orientation of variants --
derived allele, predicted-deleterious allele, disruption present -- because
those break the coding symmetry that forces `κ₃ = 0`. For structural variants
that orientation is the natural one.

What follows is the finite core: isospectrality proved through the characteristic
polynomial, and the cube sums separated.
-/

/-- A block diagonal in the variant basis. -/
noncomputable def isoBlockD (a : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j ↦ if i = j then (if i = 0 then a else a + 1) else 0

/-- The same block rotated by forty-five degrees. -/
noncomputable def isoBlockR (a : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j ↦ if i = j then a + 1 / 2 else 1 / 2

/-- Trace of a two-by-two block. -/
noncomputable def blockTrace (M : Fin 2 → Fin 2 → ℝ) : ℝ := M 0 0 + M 1 1

/-- Determinant of a two-by-two block. -/
noncomputable def blockDet (M : Fin 2 → Fin 2 → ℝ) : ℝ := M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- Characteristic polynomial of a two-by-two block. For this size the trace and
determinant determine it, and it determines the eigenvalue multiset. -/
noncomputable def blockCharPoly (M : Fin 2 → Fin 2 → ℝ) (x : ℝ) : ℝ :=
  x ^ 2 - blockTrace M * x + blockDet M

/-- The entrywise cube sum, the first non-spectral coordinate. -/
noncomputable def entrywiseCubeSum (M : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 3

/-- **The rotated block is isospectral to the diagonal one**, at every `a` and
exactly -- not merely in the limit. -/
theorem isoBlock_charPoly_eq (a x : ℝ) :
    blockCharPoly (isoBlockD a) x = blockCharPoly (isoBlockR a) x := by
  unfold blockCharPoly blockTrace blockDet isoBlockD isoBlockR
  norm_num
  ring

/-- Entrywise square sum. For a symmetric block this is `Tr Σ²`, so it is a
spectral quantity and serves as the control. -/
noncomputable def entrywiseSquareSum (M : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- **The diagonal block's square sum.** -/
theorem entrywiseSquareSum_isoBlockD (a : ℝ) :
    entrywiseSquareSum (isoBlockD a) = a ^ 2 + (a + 1) ^ 2 := by
  unfold entrywiseSquareSum isoBlockD
  simp [Fin.sum_univ_two]

/-- **The rotated block's square sum.** -/
theorem entrywiseSquareSum_isoBlockR (a : ℝ) :
    entrywiseSquareSum (isoBlockR a) = 2 * (a + 1 / 2) ^ 2 + 2 * (1 / 2) ^ 2 := by
  unfold entrywiseSquareSum isoBlockR
  simp [Fin.sum_univ_two]
  ring

/-- **The square sums agree**, as they must: this is the second spectral moment. -/
theorem entrywiseSquareSum_isoBlock_eq (a : ℝ) :
    entrywiseSquareSum (isoBlockD a) = entrywiseSquareSum (isoBlockR a) := by
  rw [entrywiseSquareSum_isoBlockD, entrywiseSquareSum_isoBlockR]
  ring

/-- **The diagonal block's entrywise cube sum.** -/
theorem entrywiseCubeSum_isoBlockD (a : ℝ) :
    entrywiseCubeSum (isoBlockD a) = a ^ 3 + (a + 1) ^ 3 := by
  unfold entrywiseCubeSum isoBlockD
  simp [Fin.sum_univ_two]

/-- **The rotated block's entrywise cube sum**, which the rotation has changed. -/
theorem entrywiseCubeSum_isoBlockR (a : ℝ) :
    entrywiseCubeSum (isoBlockR a) = 2 * (a + 1 / 2) ^ 3 + 2 * (1 / 2) ^ 3 := by
  unfold entrywiseCubeSum isoBlockR
  simp [Fin.sum_univ_two]
  ring

/-- **So the cube sum is not a spectral invariant.** Two blocks with the same
characteristic polynomial at every `a` are separated by it at `a = 1`: nine
against seven.

With `isoBlock_charPoly_eq` this is the refutation. Any portability quantity
computed from the eigenvalues of a design assigns these two the same value, and
they are not interchangeable whenever the effect prior is skewed. -/
theorem entrywiseCubeSum_not_spectral :
    entrywiseCubeSum (isoBlockD 1) ≠ entrywiseCubeSum (isoBlockR 1) := by
  rw [entrywiseCubeSum_isoBlockD, entrywiseCubeSum_isoBlockR]
  norm_num



/-- **The gap in closed form.** The two blocks are separated at every `a`, not at
one lucky point: the difference is `(3a+1)/2`, a nonvanishing affine function of
the eigenvalue offset.

Integrating it over the block family `a ∈ [1,2]`, with the one-half per-coordinate
normalisation, gives `11/8` -- the constant that multiplies `κ₃²/12` in the
third-order term of the mutual-information density. -/
theorem entrywiseCubeSum_gap (a : ℝ) :
    entrywiseCubeSum (isoBlockD a) - entrywiseCubeSum (isoBlockR a) = (3 * a + 1) / 2 := by
  rw [entrywiseCubeSum_isoBlockD, entrywiseCubeSum_isoBlockR]
  ring

/-- **And the separation is uniform over the admissible spectrum.** Every
eigenvalue of these blocks lies in `[1,3]`, so `a ≥ 1` throughout, and the gap is
bounded below by two. The failure is not a boundary artefact and not a
conditioning artefact: the condition number never exceeds three. -/
theorem entrywiseCubeSum_gap_pos (a : ℝ) (ha : 1 ≤ a) :
    2 ≤ entrywiseCubeSum (isoBlockD a) - entrywiseCubeSum (isoBlockR a) := by
  rw [entrywiseCubeSum_gap]
  linarith

/-- **No function of the spectrum computes the cube sum.** This is the general
statement, quantified over every putative spectral formula rather than exhibiting
one pair.

For a real symmetric two-by-two block the characteristic polynomial determines
the eigenvalue multiset and conversely, so "a function of the spectrum" is
exactly "a function of `blockCharPoly`". No such function reproduces
`entrywiseCubeSum`, because `isoBlockD 1` and `isoBlockR 1` share a characteristic
polynomial and differ in cube sum.

Consequently every portability quantity in this corpus that reads a design only
through `normalizedMoment`, `inverseTraceCertificate`, or any other eigenvalue
summary is blind to a difference that changes achievable accuracy whenever the
effect prior has a nonzero third cumulant -- which the standard sparse polygenic
prior does by construction. -/
theorem no_spectral_formula_for_entrywiseCubeSum :
    ¬ ∃ f : (ℝ → ℝ) → ℝ,
      ∀ M : Fin 2 → Fin 2 → ℝ, entrywiseCubeSum M = f (blockCharPoly M) := by
  rintro ⟨f, hf⟩
  have hpoly : blockCharPoly (isoBlockD 1) = blockCharPoly (isoBlockR 1) := by
    funext x
    exact isoBlock_charPoly_eq 1 x
  have : entrywiseCubeSum (isoBlockD 1) = entrywiseCubeSum (isoBlockR 1) := by
    rw [hf (isoBlockD 1), hf (isoBlockR 1), hpoly]
  exact entrywiseCubeSum_not_spectral this



/-! ### The invariant that survives a symmetric prior

With `κ₃ = 0` the cube sum is multiplied by zero and the leading obstruction
moves to the next order, where the contraction of the fourth-cumulant tensor
produces the entrywise FOURTH power sum. That is the case that bears on polygenic
scores, because sparsity is exactly what makes `κ₄` nonzero.

It is also the biologically legible one. With `Σ` a linkage-disequilibrium
matrix, `Σᵢⱼ` is a correlation `rᵢⱼ`, so the invariant is `∑ᵢⱼ rᵢⱼ⁴` -- a
fourth-power sibling of the LD score `∑ᵢ rᵢⱼ²` that LD score regression is built
on, arrived at by derivation rather than by analogy, and computable from any
reference panel.

The separation is cleaner at fourth order than at third: the gap is `3 (a + ½)²`,
a perfect square, so it is strictly positive at every eigenvalue offset but one
rather than on a half-line.
-/

/-- The entrywise fourth power sum: the non-spectral invariant that survives when
the prior is symmetric. -/
noncomputable def entrywiseFourthSum (M : Fin 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 4

/-- **The diagonal block's fourth power sum.** -/
theorem entrywiseFourthSum_isoBlockD (a : ℝ) :
    entrywiseFourthSum (isoBlockD a) = a ^ 4 + (a + 1) ^ 4 := by
  unfold entrywiseFourthSum isoBlockD
  simp [Fin.sum_univ_two]

/-- **The rotated block's fourth power sum.** -/
theorem entrywiseFourthSum_isoBlockR (a : ℝ) :
    entrywiseFourthSum (isoBlockR a) = 2 * (a + 1 / 2) ^ 4 + 2 * (1 / 2) ^ 4 := by
  unfold entrywiseFourthSum isoBlockR
  simp [Fin.sum_univ_two]
  ring

/-- **The gap is a perfect square.** Three times `(a + ½)²`, so the two blocks are
separated at every eigenvalue offset except the single point `a = -½`, which lies
outside the admissible spectrum. Unlike the third-order gap, which is affine and
changes sign, this one cannot vanish anywhere the design is positive definite. -/
theorem entrywiseFourthSum_gap (a : ℝ) :
    entrywiseFourthSum (isoBlockD a) - entrywiseFourthSum (isoBlockR a)
      = 3 * (a + 1 / 2) ^ 2 := by
  rw [entrywiseFourthSum_isoBlockD, entrywiseFourthSum_isoBlockR]
  ring

/-- **So the fourth power sum is not a spectral invariant either**, and this is
the one that matters for a symmetric prior. -/
theorem entrywiseFourthSum_not_spectral :
    entrywiseFourthSum (isoBlockD 1) ≠ entrywiseFourthSum (isoBlockR 1) := by
  rw [entrywiseFourthSum_isoBlockD, entrywiseFourthSum_isoBlockR]
  norm_num

/-- **No function of the spectrum computes it.** The same quantification over
every putative spectral formula as for the cube sum, now for the invariant that
survives the symmetry forced on polygenic priors by allele coding.

This is the operative statement for polygenic scores: no summary of a linkage
matrix through its eigenvalues -- `normalizedMoment` at any order,
`inverseTraceCertificate`, any spectral statistic whatever -- determines
achievable accuracy under a sparse symmetric effect prior. -/
theorem no_spectral_formula_for_entrywiseFourthSum :
    ¬ ∃ f : (ℝ → ℝ) → ℝ,
      ∀ M : Fin 2 → Fin 2 → ℝ, entrywiseFourthSum M = f (blockCharPoly M) := by
  rintro ⟨f, hf⟩
  have hpoly : blockCharPoly (isoBlockD 1) = blockCharPoly (isoBlockR 1) := by
    funext x
    exact isoBlock_charPoly_eq 1 x
  have : entrywiseFourthSum (isoBlockD 1) = entrywiseFourthSum (isoBlockR 1) := by
    rw [hf (isoBlockD 1), hf (isoBlockR 1), hpoly]
  exact entrywiseFourthSum_not_spectral this



/-! ### The statistic, as a reference panel would compute it

The invariant above is written as a double sum over matrix entries. A reference
panel computes per-variant sums, so the usable form is a score attached to each
variant, summed over variants -- exactly how the LD score is computed and used.

`ldScore` is the standard one, `∑ᵢ rᵢⱼ²`, the quantity LD score regression
regresses chi-squared statistics against. `ldFourthScore` is `∑ᵢ rᵢⱼ⁴`, and
summing it over variants recovers `entrywiseFourthSum`. So the non-spectral
invariant is not an abstract functional: it is a per-variant score of the same
shape as the one already computed on every reference panel, differing only in the
exponent.
-/

/-- The LD score of a variant: the sum of squared correlations with every variant,
itself included. This is the statistic LD score regression is built on. -/
noncomputable def ldScore (r : Fin 2 → Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  ∑ i, (r i j) ^ 2

/-- The fourth-power LD score of a variant. Same shape as `ldScore`, one exponent
up, and it is the per-variant form of the non-spectral invariant. -/
noncomputable def ldFourthScore (r : Fin 2 → Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  ∑ i, (r i j) ^ 4

/-- **The invariant is the summed fourth-power LD score.** This is what makes it
computable: a panel that already produces LD scores produces this by changing an
exponent. -/
theorem entrywiseFourthSum_eq_sum_ldFourthScore (M : Fin 2 → Fin 2 → ℝ) :
    entrywiseFourthSum M = ∑ j, ldFourthScore M j := by
  unfold entrywiseFourthSum ldFourthScore
  rw [Finset.sum_comm]

/-- **The ordinary LD score cannot see the difference.** Both blocks have the same
summed LD score at every `a`, because that sum is the trace of `Σ²` and hence
spectral. So the standard statistic is blind to exactly the structure the
fourth-power one detects, and the two differ by `3 (a + ½)²`. -/
theorem sum_ldScore_isoBlock_eq (a : ℝ) :
    ∑ j, ldScore (isoBlockD a) j = ∑ j, ldScore (isoBlockR a) j := by
  unfold ldScore isoBlockD isoBlockR
  simp [Fin.sum_univ_two]
  ring



/-! ### Arbitrary dimension

The two-by-two witness is not the theorem. The construction is a direct sum of
`m` such blocks with independent offsets, giving designs of every even dimension
`p = 2m`, and everything above survives the sum: the block structure means each
entrywise power sum is the sum of the per-block ones, and each spectral quantity
is likewise the sum of the per-block ones.

Two spectral controls are proved alongside, so the separation cannot be dismissed
as an artefact of a weak notion of "spectral". The trace agrees, and the sum of
squared entries agrees -- and for a symmetric matrix that second sum is exactly
`Tr Σ²`, the second spectral moment. The first quantity to separate the families
is the cube sum, and it separates them by `∑ᵢ (3 aᵢ + 1)/2`, which grows linearly
in the dimension rather than washing out.
-/

/-- `m` diagonal blocks with independent offsets: a design of dimension `2m`. -/
noncomputable def multiBlockD {m : ℕ} (a : Fin m → ℝ) :
    (Fin m × Fin 2) → (Fin m × Fin 2) → ℝ :=
  fun p q ↦ if p.1 = q.1 then isoBlockD (a p.1) p.2 q.2 else 0

/-- The same `m` blocks, each rotated by forty-five degrees. -/
noncomputable def multiBlockR {m : ℕ} (a : Fin m → ℝ) :
    (Fin m × Fin 2) → (Fin m × Fin 2) → ℝ :=
  fun p q ↦ if p.1 = q.1 then isoBlockR (a p.1) p.2 q.2 else 0

/-- Entrywise `k`-th power sum of a block design. -/
noncomputable def multiEntrywisePow {m : ℕ}
    (M : (Fin m × Fin 2) → (Fin m × Fin 2) → ℝ) (k : ℕ) : ℝ :=
  ∑ p, ∑ q, (M p q) ^ (k + 1)

/-- **A block design's entrywise power sums are the sum of its blocks'.** The
off-block entries are zero and every exponent here is positive, so they drop. -/
theorem multiEntrywisePow_multiBlockD {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    multiEntrywisePow (multiBlockD a) k
      = ∑ i, ∑ x, ∑ y, (isoBlockD (a i) x y) ^ (k + 1) := by
  classical
  unfold multiEntrywisePow multiBlockD
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    rw [if_neg (Ne.symm hj)]
    exact zero_pow (Nat.succ_ne_zero k)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The same for the rotated family. -/
theorem multiEntrywisePow_multiBlockR {m : ℕ} (a : Fin m → ℝ) (k : ℕ) :
    multiEntrywisePow (multiBlockR a) k
      = ∑ i, ∑ x, ∑ y, (isoBlockR (a i) x y) ^ (k + 1) := by
  classical
  unfold multiEntrywisePow multiBlockR
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun y _ ↦ ?_
    simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun y _ ↦ ?_
    rw [if_neg (Ne.symm hj)]
    exact zero_pow (Nat.succ_ne_zero k)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Spectral control one: the sum of squared entries agrees in every
dimension.** For a symmetric matrix this sum is `Tr Σ²`, the second spectral
moment, so the families are not separated by it. -/
theorem multiBlock_squareSum_eq {m : ℕ} (a : Fin m → ℝ) :
    multiEntrywisePow (multiBlockD a) 1 = multiEntrywisePow (multiBlockR a) 1 := by
  rw [multiEntrywisePow_multiBlockD, multiEntrywisePow_multiBlockR]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact entrywiseSquareSum_isoBlock_eq (a i)

/-- **And the cube sums separate them, by a margin linear in the dimension.**

With `multiBlock_squareSum_eq` this is the full-dimensional statement: two
families of designs of every even dimension, agreeing on the second spectral
moment and separated by the first non-spectral coordinate, with the gap summing
one nonvanishing term per block rather than averaging away. -/
theorem multiBlock_cubeSum_gap {m : ℕ} (a : Fin m → ℝ) :
    multiEntrywisePow (multiBlockD a) 2 - multiEntrywisePow (multiBlockR a) 2
      = ∑ i, (3 * a i + 1) / 2 := by
  rw [multiEntrywisePow_multiBlockD, multiEntrywisePow_multiBlockR,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact entrywiseCubeSum_gap (a i)



/-! ### The mechanism: a cumulant contraction is an entrywise power sum

The block families exhibit designs a spectral formula cannot separate. This is the
identity that says WHY the separating quantity is an entrywise cube sum, and it
holds in every dimension with no reference to the counterexample.

Write a section as `Θ = L B` with `B` centred and independent. The third-cumulant
tensor of `Θ` is `κ₃` times the threefold contraction of `L` against itself, and
its squared Frobenius norm is what enters the low signal-to-noise expansion of the
mutual information at third order. The identity below evaluates that norm: it
collapses to the entrywise cube sum of the Gram matrix `S = LᵀL`, the design
covariance.

That is the obstruction in one line. The covariance enters the expansion elsewhere
through `Tr Cᵏ`, which is spectral. It enters here through `∑ᵢⱼ Sᵢⱼ³`, which is
not, and the identity shows the entrywise form is FORCED by the contraction rather
than chosen.

The proof is a reordering of a fivefold sum: expanding the square pairs the two
index copies, expanding the cube pairs the three tensor copies, and the two orders
differ. `simp` does not find the reordering and chaining swaps at depth is where a
first attempt died. `sum_reorder_pair_out` below does it in one move, peeling an
index past two others, and three applications of it carry the whole rearrangement.
-/

/-- Move an outer index inside two others. The engine of the reordering: one
application peels a single index past a pair, and the contraction identity needs
three. -/
private theorem sum_reorder_pair_out {X I J : Type*}
    [Fintype X] [Fintype I] [Fintype J] (f : X → I → J → ℝ) :
    (∑ x, ∑ i, ∑ j, f x i j) = ∑ i, ∑ j, ∑ x, f x i j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]

/-- The Gram matrix `S = LᵀL`: the covariance of `Θ = L B` for `B` with unit
independent coordinates. -/
noncomputable def gramMatrix {d n : ℕ} (L : Fin d → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ a, L a i * L a j

/-- The third-cumulant tensor of `Θ = L B`, up to the scalar `κ₃`. -/
noncomputable def thirdCumulantTensor {d n : ℕ} (L : Fin d → Fin n → ℝ)
    (a b c : Fin d) : ℝ :=
  ∑ i, L a i * L b i * L c i

/-- **The contraction identity.** The squared Frobenius norm of the third-cumulant
tensor is the entrywise cube sum of the Gram matrix. Dimension-free, and the step
at which a spectral quantity would have to appear and does not. -/
theorem thirdCumulant_frobenius_eq_gram_cubeSum {d n : ℕ} (L : Fin d → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, (thirdCumulantTensor L a b c) ^ 2)
      = ∑ i, ∑ j, (gramMatrix L i j) ^ 3 := by
  unfold thirdCumulantTensor gramMatrix
  have lhs : (∑ a, ∑ b, ∑ c, (∑ i, L a i * L b i * L c i) ^ 2)
      = ∑ a, ∑ b, ∑ c, ∑ i, ∑ j,
          (L a i * L b i * L c i) * (L a j * L b j * L c j) := by
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
      Finset.sum_congr rfl fun c _ ↦ ?_
    rw [sq, Finset.sum_mul_sum]
  have rhs : (∑ i, ∑ j, (∑ a, L a i * L a j) ^ 3)
      = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c,
          (L a i * L a j) * (L b i * L b j) * (L c i * L c j) := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pow_succ, pow_succ, pow_one, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_mul]
  rw [lhs, rhs]
  -- peel `c`, then `b`, then `a`, past the `(i, j)` pair
  have hc : (∑ a, ∑ b, ∑ c, ∑ i, ∑ j,
        (L a i * L b i * L c i) * (L a j * L b j * L c j))
      = ∑ a, ∑ b, ∑ i, ∑ j, ∑ c,
        (L a i * L b i * L c i) * (L a j * L b j * L c j) := by
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    exact sum_reorder_pair_out _
  have hb : (∑ a, ∑ b, ∑ i, ∑ j, ∑ c,
        (L a i * L b i * L c i) * (L a j * L b j * L c j))
      = ∑ a, ∑ i, ∑ j, ∑ b, ∑ c,
        (L a i * L b i * L c i) * (L a j * L b j * L c j) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    exact sum_reorder_pair_out _
  have ha : (∑ a, ∑ i, ∑ j, ∑ b, ∑ c,
        (L a i * L b i * L c i) * (L a j * L b j * L c j))
      = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c,
        (L a i * L b i * L c i) * (L a j * L b j * L c j) :=
    sum_reorder_pair_out _
  rw [hc, hb, ha]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun c _ ↦ ?_
  ring

end CapacityInvariant

end

end Calibrator

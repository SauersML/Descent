/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Graded certificate calculus without theorem-valued inputs

This module formalizes the algebra common to mixture-versus-mixture minimax
certificates.  It deliberately does **not** encode minimax duality, the
Donoho--Liu constant, a moment-comparison inequality, or a deconvolution
envelope as fields of a structure.  Those are theorems, not data, and accepting them as
`Prop`-valued fields would prove consequences by field projection.

What remains is unconditional:

* a modulus is nonnegative by construction;
* the value-formula scale is positive by construction;
* the ungraded calculus is complete relative to its own value definition;
* the deficit is exactly the square of a modulus ratio; and
* exact grade completeness is equivalent to grade-insensitivity.

The literature claim that grade two is within `5/4` in the Donoho--Liu
convex-linear regime remains provenance only: this repository does not yet
contain the white-noise decision model needed to state it faithfully.  The
fixed-grade incompleteness claim is stated below for actual finite predictive
laws, with a visible `sorry` at the missing construction. A citation is never
accepted as a theorem parameter.

## Why that `sorry` stays, and what closing it needs

The witness chooses the target, every moment probe, every parameter's
observation law, and the observation-space size, all after seeing `n`, the grade
and the desired bound.  Three successive guards against that turned out to be
insufficient, and each is now a theorem here rather than a remark:

1. At radius `1` the discrepancy constraint is free, because total variation
   never exceeds one -- `feasible_one_iff_momentMatched`.  Feasibility is moment
   matching, and the observation kernel drops out entirely.
2. A shrinking radius does not repair that by itself.  If every kernel law lies
   within `ε` of one fixed law, every pair of priors is `2ε`-indistinguishable
   -- `totalVariation_le_two_mul_of_close` -- so a witness takes `ε` to be half
   the radius and the collapse returns.
3. Requiring `Informative`, i.e. nonzero pairwise separation, is still not
   enough: it carries no floor, so every pair may sit far below the radius.
   The statements therefore ask for `SeparatedBy (fixedGradeInformationRadius n)`.

A proof that evades these is kernel-valid and statement-valid while failing
mathematical intent, and must not replace the admission.  Closing it honestly
needs, before the bound is stated: a fixed normalized architecture class; a
specified one-observation kernel and its `n`-fold product, or another explicit
growing-data construction; target and moment probes fixed independently of the
desired bound; explicit moment-matched priors in that model; and a proved
total-variation comparison of their prior-predictive laws.

Note also that `n` indexes the parameter catalogue, not a count of independent
observations, so no sample-size rate follows from increasing it on its own.
-/

namespace Calibrator.CertificateGrading

open scoped BigOperators

/-! ## The certificate object itself

The numerical calculus below is useful only after saying what its modulus is.
The following definitions make the usual mixture-versus-mixture construction
literal.  A prior is Mathlib's canonical probability mass function on a
nonempty finite support, including boundary priors with zero-mass atoms.  Thus
there is no caller-supplied mass or positivity theorem.  Grade `K` means equality of
the moments with indices `< K`.  The statistical experiment enters only
through a numerical discrepancy, and the modulus is the supremum of target
separations among feasible pairs.

This is the non-vacuous grading interface: removing the grade constraint gives
the ungraded optimization, while increasing the grade shrinks the feasible
set.  Any claim about the *value* or *rate* of the resulting modulus still has
to be proved for the particular experiment.
-/

/-- A probability law on `n + 1` support points.  This is an alias of
Mathlib's `PMF`, not a custom structure carrying theorem fields. -/
abbrev FinitePrior (n : ℕ) := PMF (Fin (n + 1))

namespace FinitePrior

variable {n : ℕ}

/-- Real-valued mass of an atom. -/
noncomputable def probability (P : FinitePrior n) (i : Fin (n + 1)) : ℝ :=
  (P i).toReal

theorem probability_nonneg (P : FinitePrior n) (i : Fin (n + 1)) :
    0 ≤ FinitePrior.probability P i :=
  ENNReal.toReal_nonneg

theorem probability_le_one (P : FinitePrior n) (i : Fin (n + 1)) :
    FinitePrior.probability P i ≤ 1 := by
  simpa [FinitePrior.probability] using
    ENNReal.toReal_le_coe_of_le_coe (P.coe_le_one i)

/-- Expectation of a function under the derived prior. -/
noncomputable def mean (P : FinitePrior n) (f : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, FinitePrior.probability P i * f i

/-- A finite-prior expectation is bounded by the unweighted absolute sum.
This is deliberately proved from `PMF.coe_le_one`; callers do not supply a
boundedness theorem for the modulus below. -/
theorem abs_mean_le_sum_abs (P : FinitePrior n) (f : Fin (n + 1) → ℝ) :
    |P.mean f| ≤ ∑ i, |f i| := by
  calc
    |P.mean f| ≤ ∑ i, |P.probability i * f i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P.probability i * |f i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (P.probability_nonneg i)]
    _ ≤ ∑ i, 1 * |f i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (P.probability_le_one i) (abs_nonneg _)
    _ = ∑ i, |f i| := by simp

/-- The mean under a point mass is the value at that point. -/
@[simp] theorem mean_pure (i : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    FinitePrior.mean (PMF.pure i) f = f i := by
  unfold FinitePrior.mean FinitePrior.probability
  rw [Finset.sum_eq_single i]
  · simp [PMF.pure_apply]
  · intro j _ hj
    simp [PMF.pure_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

end FinitePrior

/-- The finite probability simplex.  This is the convex parameter class on
which the certificate calculus acts; convexity is not inferred from a
suggestive file-level comment. -/
noncomputable def finitePriorCarrier (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- Every actual finite prior has a probability vector in the simplex. -/
theorem finitePrior_probability_mem {n : ℕ} (P : FinitePrior n) :
    (fun i ↦ P.probability i) ∈ finitePriorCarrier n := by
  constructor
  · exact fun i ↦ P.probability_nonneg i
  · simp only [FinitePrior.probability]
    rw [← ENNReal.toReal_sum (fun i _ ↦ P.apply_ne_top i)]
    -- Two shapes fail here and both were tried against the kernel, so neither
    -- guess is worth repeating.
    --
    -- `simpa only [tsum_fintype] using P.tsum_coe` fails: `PMF.tsum_coe` is
    -- itself a simp lemma, so simp closes the SUPPLIED TERM to `True` and then
    -- reports a mismatch against a goal it never touched. Restricting the simp
    -- set does not prevent this -- the term collapses on its own lemma, not on
    -- `tsum_fintype`.
    --
    -- `rw [← tsum_fintype]` on the goal fails differently: nothing in the goal
    -- pins the summation filter, so the instance is left stuck on
    -- `SummationFilter.LeAtTop ?m`.
    --
    -- Rewriting FORWARD in the hypothesis has neither problem. The term is
    -- already elaborated, so the filter is determined, and simp never gets the
    -- chance to close it.
    have hsum : (∑ i : Fin (n + 1), P i) = 1 := by
      have hcoe := P.tsum_coe
      rwa [tsum_fintype] at hcoe
    rw [hsum]
    norm_num

/-- The prior class underlying every finite mixture experiment is convex;
convexity is proved from the simplex equations, not accepted as an experiment
field. -/
theorem finitePriorCarrier_convex (n : ℕ) :
    Convex ℝ (finitePriorCarrier n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

/-- Numerical ingredients of a finite fuzzy-hypothesis problem.  There are no
`Prop` fields: validity conditions are derived predicates below. -/
structure FiniteMomentCertificateProblem (n : ℕ) where
  target : Fin (n + 1) → ℝ
  moment : ℕ → Fin (n + 1) → ℝ
  pairDiscrepancy : FinitePrior n → FinitePrior n → ℝ

namespace FiniteMomentCertificateProblem

variable {n : ℕ} (E : FiniteMomentCertificateProblem n)

/-- The first `K` selected moments of the two priors agree. -/
def MomentMatched (K : ℕ) (P Q : FinitePrior n) : Prop :=
  ∀ r < K, FinitePrior.mean P (E.moment r) =
    FinitePrior.mean Q (E.moment r)

@[simp] theorem momentMatched_zero (P Q : FinitePrior n) :
    E.MomentMatched 0 P Q := by
  intro r hr
  omega

/-- Higher-grade matching implies every lower grade. -/
theorem momentMatched_mono {K L : ℕ} (hKL : K ≤ L)
    {P Q : FinitePrior n} (h : E.MomentMatched L P Q) :
    E.MomentMatched K P Q := by
  intro r hr
  exact h r (lt_of_lt_of_le hr hKL)

/-- A pair is usable at information radius `h` when it matches the requested
moments and its experiment discrepancy is at most `|h|`. -/
def Feasible (K : ℕ) (h : ℝ) (P Q : FinitePrior n) : Prop :=
  E.MomentMatched K P Q ∧ |E.pairDiscrepancy P Q| ≤ |h|

/-- Absolute separation of the target functional under two priors. -/
noncomputable def targetGap (P Q : FinitePrior n) : ℝ :=
  |FinitePrior.mean P E.target - FinitePrior.mean Q E.target|

theorem targetGap_nonneg (P Q : FinitePrior n) : 0 ≤ E.targetGap P Q :=
  abs_nonneg _

/-- Target gaps carried by feasible mixture pairs. -/
noncomputable def admissibleGaps (K : ℕ) (h : ℝ) : Set ℝ :=
  {d : ℝ | ∃ P Q, E.Feasible K h P Q ∧ d = E.targetGap P Q}

/-- The grade-`K` modulus: the largest target separation carried by a feasible
mixture pair.  Zero is inserted explicitly, so an empty feasible family has
modulus zero instead of relying on the implementation value of `sSup ∅`.
Evaluating this supremum is the hard problem and cannot be installed as a
theorem-valued field. -/
noncomputable def modulus (K : ℕ) (h : ℝ) : ℝ :=
  sSup (insert 0 (E.admissibleGaps K h))

/-- Every target gap is bounded by twice the catalogue's absolute target mass. -/
theorem targetGap_le_catalogueBound (P Q : FinitePrior n) :
    E.targetGap P Q ≤ 2 * ∑ i, |E.target i| := by
  unfold targetGap
  have hP := FinitePrior.abs_mean_le_sum_abs P E.target
  have hQ := FinitePrior.abs_mean_le_sum_abs Q E.target
  calc
    |P.mean E.target - Q.mean E.target| ≤
        |P.mean E.target| + |Q.mean E.target| := abs_sub _ _
    _ ≤ 2 * ∑ i, |E.target i| := by linarith

theorem admissibleGaps_bddAbove (K : ℕ) (h : ℝ) :
    BddAbove (insert 0 (E.admissibleGaps K h)) := by
  refine ⟨2 * ∑ i, |E.target i|, ?_⟩
  intro d hd
  rcases hd with (rfl | hd)
  · positivity
  · rcases hd with ⟨P, Q, _, rfl⟩
    exact E.targetGap_le_catalogueBound P Q

/-- A witnessed feasible pair bounds the modulus from below.

    The modulus is a supremum, so exhibiting one feasible pair is the only way to bound it
    below without evaluating it. -/
theorem le_modulus_of_feasible (K : ℕ) (h : ℝ) (P Q : FinitePrior n)
    (hPQ : E.Feasible K h P Q) :
    E.targetGap P Q ≤ E.modulus K h :=
  le_csSup (E.admissibleGaps_bddAbove K h)
    (Set.mem_insert_iff.mpr (Or.inr ⟨P, Q, hPQ, rfl⟩))

/-- The modulus is bounded above by twice the catalogue's absolute target mass. -/
theorem modulus_le_catalogueBound (K : ℕ) (h : ℝ) :
    E.modulus K h ≤ 2 * ∑ i, |E.target i| := by
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro d (rfl | ⟨P, Q, -, rfl⟩)
  · positivity
  · exact E.targetGap_le_catalogueBound P Q

theorem modulus_nonneg (K : ℕ) (h : ℝ) : 0 ≤ E.modulus K h := by
  apply le_csSup (E.admissibleGaps_bddAbove K h)
  exact Set.mem_insert 0 _

/-- The feasible sets are nested in grade. -/
theorem feasible_mono {K L : ℕ} (hKL : K ≤ L) (h : ℝ)
    {P Q : FinitePrior n} (hfeas : E.Feasible L h P Q) :
    E.Feasible K h P Q :=
  ⟨E.momentMatched_mono hKL hfeas.1, hfeas.2⟩

/-- Requiring more matched moments can only decrease the certificate modulus. -/
theorem modulus_antitone_grade {K L : ℕ} (hKL : K ≤ L) (h : ℝ) :
    E.modulus L h ≤ E.modulus K h := by
  unfold modulus
  apply csSup_le_csSup (E.admissibleGaps_bddAbove K h)
    ⟨0, Set.mem_insert 0 (E.admissibleGaps L h)⟩
  intro d hd
  rcases hd with (rfl | hd)
  · exact Set.mem_insert 0 _
  · rcases hd with ⟨P, Q, hfeas, rfl⟩
    exact Set.mem_insert_iff.mpr <| Or.inr
      ⟨P, Q, E.feasible_mono hKL h hfeas, rfl⟩

end FiniteMomentCertificateProblem

/-! ## A genuine finite experiment, rather than an arbitrary discrepancy

The abstract problem above is useful for algebra.  The structure below is the
statistical specialization used by incompleteness statements: each parameter
has an actual observation law, prior mixtures are formed with `PMF.bind`, and
the discrepancy is total variation computed from those mixture laws.  Thus a
gap theorem cannot choose an arbitrary numerical discrepancy to manufacture a
desired answer.
-/

/-- Finite mixture experiment with numerical target and moment functions. -/
structure FiniteMixtureExperiment (parameterCount observationCount : ℕ) where
  target : Fin (parameterCount + 1) → ℝ
  moment : ℕ → Fin (parameterCount + 1) → ℝ
  observation : Fin (parameterCount + 1) → FinitePrior observationCount

namespace FiniteMixtureExperiment

variable {parameterCount observationCount : ℕ}
    (E : FiniteMixtureExperiment parameterCount observationCount)

/-- Observation law obtained after first drawing a parameter from `P`. -/
noncomputable def mixture (P : FinitePrior parameterCount) :
    FinitePrior observationCount :=
  P.bind E.observation

/-- The prior-predictive mass is the prior-weighted average of the kernel masses.

`PMF.bind` is defined by a `tsum` in `ℝ≥0∞`; over a finite index this is the
ordinary weighted sum after `toReal`, and every factor is finite so the
conversion distributes. -/
theorem mixture_probability (P : FinitePrior parameterCount)
    (x : Fin (observationCount + 1)) :
    FinitePrior.probability (E.mixture P) x =
      ∑ i, FinitePrior.probability P i *
        FinitePrior.probability (E.observation i) x := by
  unfold FinitePrior.probability mixture
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun i _ ↦ ENNReal.mul_ne_top (P.apply_ne_top i)
      ((E.observation i).apply_ne_top x))]
  exact Finset.sum_congr rfl fun i _ ↦ ENNReal.toReal_mul

/-- Total-variation distance between the two prior-predictive laws. -/
noncomputable def totalVariation
    (P Q : FinitePrior parameterCount) : ℝ :=
  (1 / 2 : ℝ) * ∑ x,
    |(E.mixture P).probability x - (E.mixture Q).probability x|

/-- **A kernel whose laws all sit within `ε` of one fixed law makes every pair of
priors `2ε`-indistinguishable**, no matter how many parameters it has.

WHY THIS MATTERS FOR THE ADMITTED RATE THEOREM. `fixedGradeInformationRadius`
replaced radius one precisely so that the discrepancy constraint would bind and
the observation kernel would stay part of the modulus. A shrinking radius is
necessary for that, and this says it is not sufficient: taking `ε` to be half
the radius makes `totalVariation ≤ radius` for EVERY pair, so feasibility
collapses to moment matching again and the kernel drops out exactly as it did at
radius one.

The witness is free to choose the kernel after seeing `n`, so it can always
shrink the kernel's spread faster than the radius shrinks. Closing that needs a
LOWER bound on informativeness -- distinct parameters separated by at least some
fixed total variation, or an explicit one-observation kernel and its `n`-fold
product -- not merely an upper bound on the radius. `SeparatedBy` below is that
floor, and the module docstring lists what a rate theorem still needs beyond it.

The proof is the triangle inequality after subtracting `L`, which is legitimate
because the prior differences sum to zero and so annihilate the constant. -/
theorem totalVariation_le_two_mul_of_close
    (L : FinitePrior observationCount) (ε : ℝ)
    (hclose : ∀ i, (1 / 2 : ℝ) * ∑ x, |FinitePrior.probability (E.observation i) x -
        FinitePrior.probability L x| ≤ ε)
    (P Q : FinitePrior parameterCount) :
    E.totalVariation P Q ≤ 2 * ε := by
  classical
  have hdiff_sum : ∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i) = 0 := by
    rw [Finset.sum_sub_distrib, (finitePrior_probability_mem P).2,
      (finitePrior_probability_mem Q).2, sub_self]
  have hpoint : ∀ x, FinitePrior.probability (E.mixture P) x -
      FinitePrior.probability (E.mixture Q) x =
      ∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i) *
        (FinitePrior.probability (E.observation i) x - FinitePrior.probability L x) := by
    intro x
    have hexp : ∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i) *
        (FinitePrior.probability (E.observation i) x - FinitePrior.probability L x) =
        (∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i) *
          FinitePrior.probability (E.observation i) x) -
        (∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i)) *
          FinitePrior.probability L x := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hexp, hdiff_sum, zero_mul, sub_zero, E.mixture_probability P x,
      E.mixture_probability Q x, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hmass : ∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i| ≤ 2 := by
    calc ∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i|
        ≤ ∑ i, (FinitePrior.probability P i + FinitePrior.probability Q i) :=
          Finset.sum_le_sum fun i _ ↦ by
            refine (abs_sub _ _).trans ?_
            rw [abs_of_nonneg (FinitePrior.probability_nonneg P i),
              abs_of_nonneg (FinitePrior.probability_nonneg Q i)]
      _ = 2 := by
          rw [Finset.sum_add_distrib, (finitePrior_probability_mem P).2,
            (finitePrior_probability_mem Q).2]; norm_num
  have hεnn : 0 ≤ ε := le_trans (by positivity) (hclose 0)
  unfold totalVariation
  rw [show (2 : ℝ) * ε = (1 / 2 : ℝ) * (2 * (2 * ε)) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ x, |FinitePrior.probability (E.mixture P) x -
          FinitePrior.probability (E.mixture Q) x|
      = ∑ x, |∑ i, (FinitePrior.probability P i - FinitePrior.probability Q i) *
          (FinitePrior.probability (E.observation i) x -
            FinitePrior.probability L x)| := by
        exact Finset.sum_congr rfl fun x _ ↦ by rw [hpoint x]
    _ ≤ ∑ x, ∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i| *
          |FinitePrior.probability (E.observation i) x -
            FinitePrior.probability L x| := by
        refine Finset.sum_le_sum fun x _ ↦ ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        exact Finset.sum_congr rfl fun i _ ↦ abs_mul _ _
    _ = ∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i| *
          ∑ x, |FinitePrior.probability (E.observation i) x -
            FinitePrior.probability L x| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i| * (2 * ε) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        linarith [hclose i]
    _ = (∑ i, |FinitePrior.probability P i - FinitePrior.probability Q i|) * (2 * ε) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * (2 * ε) := by
        refine mul_le_mul_of_nonneg_right hmass ?_
        linarith

theorem totalVariation_nonneg (P Q : FinitePrior parameterCount) :
    0 ≤ E.totalVariation P Q := by
  unfold totalVariation
  positivity

/-- **Informative at a stated scale**: distinct parameters are separated by at
least `c`, not merely by something positive.

A predicate asking only that each pairwise total variation be nonzero carries no
floor, so an experiment may satisfy it while every pair sits far below the
information radius. `totalVariation_le_two_mul_of_close` shows what that buys a
witness: if every kernel law lies within `ε` of one fixed law then every pair of
priors is `2ε`-indistinguishable, so taking `ε` to be half the radius makes
`TV ≤ h` hold for all pairs and feasibility collapses to moment matching -- the
collapse that a shrinking radius was introduced to prevent, one step further
back.

The witness chooses the kernel after seeing `n`, so it can always shrink the
kernel's spread faster than the radius shrinks. Only a floor stated at the
radius scale closes that, which is what this supplies. -/
def SeparatedBy (c : ℝ) : Prop :=
  ∀ i j : Fin (parameterCount + 1), i ≠ j →
    c ≤ E.totalVariation (PMF.pure i) (PMF.pure j)

/-- A positive separation floor gives nonzero pairwise separation.  The converse
fails, which is the whole reason the graded statements ask for the floor. -/
theorem pos_totalVariation_of_separatedBy {c : ℝ} (hc : 0 < c) (h : E.SeparatedBy c)
    {i j : Fin (parameterCount + 1)} (hij : i ≠ j) :
    0 < E.totalVariation (PMF.pure i) (PMF.pure j) :=
  lt_of_lt_of_le hc (h i j hij)

/-- **Total variation never exceeds one**, because it halves a difference of two
probability vectors and each has mass one.

This is the ordinary bound, and it is stated because of what it does to the
feasibility constraint at radius `1`; see `feasible_one_iff_momentMatched`. -/
theorem totalVariation_le_one (P Q : FinitePrior parameterCount) :
    E.totalVariation P Q ≤ 1 := by
  unfold totalVariation
  have hP : ∑ x, FinitePrior.probability (E.mixture P) x = 1 :=
    (finitePrior_probability_mem (E.mixture P)).2
  have hQ : ∑ x, FinitePrior.probability (E.mixture Q) x = 1 :=
    (finitePrior_probability_mem (E.mixture Q)).2
  have hsplit : ∑ x, |FinitePrior.probability (E.mixture P) x -
        FinitePrior.probability (E.mixture Q) x| ≤ 2 := by
    calc ∑ x, |FinitePrior.probability (E.mixture P) x -
            FinitePrior.probability (E.mixture Q) x|
        ≤ ∑ x, (FinitePrior.probability (E.mixture P) x +
            FinitePrior.probability (E.mixture Q) x) :=
          Finset.sum_le_sum fun x _ ↦ by
            refine (abs_sub _ _).trans ?_
            rw [abs_of_nonneg (FinitePrior.probability_nonneg _ x),
              abs_of_nonneg (FinitePrior.probability_nonneg _ x)]
      _ = 2 := by rw [Finset.sum_add_distrib, hP, hQ]; norm_num
  linarith

/-- **At radius one the discrepancy constraint is vacuous.**

`Feasible K h` asks for moment matching AND `|discrepancy| ≤ |h|`. The
discrepancy here is total variation, which lies in `[0, 1]` for every pair of
priors and every observation kernel whatsoever. So at `h = 1` the second
conjunct holds always, and feasibility collapses to moment matching.

WHAT THIS COSTS. A modulus evaluated at `h = 1` sees no observation kernel at
all: the same value is obtained from an informative experiment and from the
constant kernel that maps every parameter to one fixed law. Any theorem whose
content is supposed to come from the information structure -- a
`Donoho--Liu`-type rate, in which the graded modulus is small *because* the
discrepancy constraint forces the prior-predictive laws close together --
cannot be expressed at this radius. Expressing it needs a radius that shrinks
with the sample size, so that the constraint binds.

This is why `fixedGrade_incompleteness` and its biology twin remain admitted
rather than proved: at `h = 1` they are provable by a construction with no
statistical content, and a proof of the statement as written would not be a
proof of the claim the name makes. -/
theorem totalVariation_le_one' (P Q : FinitePrior parameterCount) :
    |E.totalVariation P Q| ≤ |(1 : ℝ)| := by
  rw [abs_of_nonneg (E.totalVariation_nonneg P Q), abs_one]
  exact E.totalVariation_le_one P Q

/-- The corresponding graded certificate problem. -/
noncomputable def certificateProblem :
    FiniteMomentCertificateProblem parameterCount where
  target := E.target
  moment := E.moment
  pairDiscrepancy := E.totalVariation

/-- **At radius one, feasibility IS moment matching**, for every experiment.

The consequence is that a modulus evaluated at `h = 1` sees no observation
kernel at all: an informative experiment and the constant kernel that sends
every parameter to one fixed law give the same value. So a claim whose content
is supposed to come from the information structure -- a `Donoho--Liu`-type rate,
where the graded modulus is small *because* the discrepancy constraint pushes
the prior-predictive laws together -- cannot be expressed at this radius, and a
proof of such a statement would not be a proof of the claim its name makes.
Expressing it needs a radius that shrinks with the sample size. -/
theorem feasible_one_iff_momentMatched (K : ℕ) (P Q : FinitePrior parameterCount) :
    E.certificateProblem.Feasible K 1 P Q ↔
      E.certificateProblem.MomentMatched K P Q :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, E.totalVariation_le_one' P Q⟩⟩

/-! ### The constant-channel falsifier, formalized -/

/-- An experiment whose observation law contains no parameter information.

This is a useful negative control, not a witness for an incompleteness rate: target and moment
functions may vary, but every parameter emits the same law. -/
noncomputable def constantObservationExperiment
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (law : FinitePrior observationCount) :
    FiniteMixtureExperiment parameterCount observationCount where
  target := target
  moment := moment
  observation := fun _ ↦ law

@[simp] theorem constantObservationExperiment_mixture
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (law : FinitePrior observationCount) (P : FinitePrior parameterCount) :
    (constantObservationExperiment target moment law).mixture P = law := by
  exact PMF.bind_const P law

@[simp] theorem constantObservationExperiment_totalVariation
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (law : FinitePrior observationCount) (P Q : FinitePrior parameterCount) :
    (constantObservationExperiment target moment law).totalVariation P Q = 0 := by
  unfold totalVariation
  simp

/-- **The constant channel separates at no positive radius**, whenever there are at least
    two parameters. It is the negative control the hypothesis exists to exclude: its total
    variation is zero between every pair, so it satisfies every discrepancy constraint
    vacuously and any gap proved with it says nothing about grading. -/
theorem constantObservationExperiment_not_separatesAtRadius
    (target : Fin (parameterCount + 2) → ℝ)
    (moment : ℕ → Fin (parameterCount + 2) → ℝ)
    (law : FinitePrior observationCount) {h : ℝ} (hh : 0 < h) :
    ¬ (constantObservationExperiment target moment law).SeparatedBy h := by
  intro hsep
  have h01 : (0 : Fin (parameterCount + 2)) ≠ 1 := by
    simp [Fin.ext_iff]
  have hle := hsep 0 1 h01
  rw [constantObservationExperiment_totalVariation] at hle
  linarith

/-- In a constant channel, feasibility is only moment matching at every information radius.
The data-radius constraint contributes nothing because the prior-predictive laws are identical. -/
theorem constantObservationExperiment_feasible_iff
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (law : FinitePrior observationCount) (K : ℕ) (h : ℝ)
    (P Q : FinitePrior parameterCount) :
    (constantObservationExperiment target moment law).certificateProblem.Feasible K h P Q ↔
      (constantObservationExperiment target moment law).certificateProblem.MomentMatched K P Q := by
  constructor
  · exact fun hfeasible ↦ hfeasible.1
  · intro hmatched
    refine ⟨hmatched, ?_⟩
    change |(constantObservationExperiment target moment law).totalVariation P Q| ≤ |h|
    rw [constantObservationExperiment_totalVariation]
    simp [abs_nonneg h]

/-- Consequently the modulus of a constant channel is independent of the information radius.

This is the exact reason such a channel cannot establish a sample-size law: changing the nominal
noise level does not change the optimization problem at all. -/
theorem constantObservationExperiment_modulus_eq
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (law : FinitePrior observationCount) (K : ℕ) (h₁ h₂ : ℝ) :
    (constantObservationExperiment target moment law).certificateProblem.modulus K h₁ =
      (constantObservationExperiment target moment law).certificateProblem.modulus K h₂ := by
  unfold FiniteMomentCertificateProblem.modulus
  apply congrArg sSup
  ext d
  simp only [Set.mem_insert_iff, FiniteMomentCertificateProblem.admissibleGaps]
  constructor
  · rintro (rfl | ⟨P, Q, hfeasible, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q,
        (constantObservationExperiment_feasible_iff target moment law K h₂ P Q).2
          ((constantObservationExperiment_feasible_iff target moment law K h₁ P Q).1 hfeasible),
        rfl⟩
  · rintro (rfl | ⟨P, Q, hfeasible, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q,
        (constantObservationExperiment_feasible_iff target moment law K h₁ P Q).2
          ((constantObservationExperiment_feasible_iff target moment law K h₂ P Q).1 hfeasible),
        rfl⟩

/-- Grade exponent used in the fixed-grade gap theorem.  Writing `K + 1`
makes the theorem total at grade zero while retaining order `1/K`. -/
noncomputable def fixedGradeExponent (K : ℕ) : ℝ :=
  1 / (K + 1 : ℝ)

/-- The chosen exponent is quantitatively of order `1 / K`, with explicit
constants, rather than merely described by asymptotic notation. -/
theorem fixedGradeExponent_bounds (K : ℕ) (hK : 1 ≤ K) :
    1 / (2 * (K : ℝ)) ≤ fixedGradeExponent K ∧
      fixedGradeExponent K ≤ 1 / (K : ℝ) := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hk
  unfold fixedGradeExponent
  constructor
  · rw [div_le_div_iff₀ (mul_pos (by norm_num) hkpos) (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) hkpos]
    nlinarith

/-- The explicit polynomial-over-logarithmic factor from the program. -/
noncomputable def fixedGradeGapScale (K n : ℕ) : ℝ :=
  (n + 2 : ℝ) ^ (fixedGradeExponent K / 2) /
    Real.sqrt (Real.log (n + 2 : ℝ))

/-- Statistical indistinguishability radius for `n` independent observations.

The `+ 2` makes the definition total while preserving the canonical `n⁻¹ʲ²` scale. Unlike
radius one, this radius is strictly below one, so total variation is not automatically feasible
and the observation kernel remains part of the modulus. -/
noncomputable def fixedGradeInformationRadius (n : ℕ) : ℝ :=
  1 / Real.sqrt (n + 2 : ℝ)

theorem fixedGradeInformationRadius_pos (n : ℕ) :
    0 < fixedGradeInformationRadius n := by
  unfold fixedGradeInformationRadius
  exact div_pos zero_lt_one (Real.sqrt_pos.2 (by positivity))

theorem fixedGradeInformationRadius_lt_one (n : ℕ) :
    fixedGradeInformationRadius n < 1 := by
  unfold fixedGradeInformationRadius
  have hbase : (1 : ℝ) < n + 2 := by exact_mod_cast (show 1 < n + 2 by omega)
  have hsqrt : 1 < Real.sqrt (n + 2 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by nlinarith)
  exact (div_lt_one (by positivity)).2 hsqrt

/-- The proposed fixed-grade scale is strictly positive for every grade and catalogue size. -/
theorem fixedGradeGapScale_pos (K n : ℕ) : 0 < fixedGradeGapScale K n := by
  unfold fixedGradeGapScale fixedGradeExponent
  have hbase : (0 : ℝ) < n + 2 := by positivity
  have honeNat : 1 < n + 2 := by omega
  have hone : (1 : ℝ) < n + 2 := by exact_mod_cast honeNat
  exact div_pos (Real.rpow_pos_of_pos hbase _)
    (Real.sqrt_pos.2 (Real.log_pos hone))

/-- Modulus-level certification gap of this actual finite experiment. -/
noncomputable def certificationGap (K : ℕ) (h : ℝ) : ℝ :=
  E.certificateProblem.modulus 0 h /
    E.certificateProblem.modulus K h

/-- The only unproved mathematical construction needed by the finite fixed-grade theorem:
at every fixed positive grade there is a sequence of actual finite mixture experiments whose
ungraded-to-graded modulus ratio is at least

`n^(b_K/2) / sqrt(log n)`, with `b_K = 1/(K+1) = Θ(1/K)`.

Its proof must construct moment-matching priors in a concrete growing-data experiment and compare
their actual prior-predictive total variation laws. The experiment, target, and probes may not be
tuned after reading the desired bound. A constant observation kernel or a residual chosen as the
reciprocal of the conclusion would prove only that this interface is underconstrained.

The automatic convexity of the finite probability simplex is deliberately absent from this
admission. It is proved separately and attached by `fixedGrade_incompleteness`, so the visible
`sorry` covers exactly the missing statistical construction and nothing routine. -/
theorem exists_fixedGrade_gap (K : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ observationCount : ℕ,
        ∃ E : FiniteMixtureExperiment n observationCount,
          E.SeparatedBy (fixedGradeInformationRadius n) ∧
            fixedGradeGapScale K n ≤
              E.certificationGap (K + 1) (fixedGradeInformationRadius n) := by
  sorry

/-- **Fixed-grade incompleteness on a convex problem.**

The substantive gap comes only from `exists_fixedGrade_gap`; convexity is not accepted as part of
that witness. Every finite prior lies in Mathlib's probability simplex, and
`finitePriorCarrier_convex` proves that simplex convex for every catalogue size. Thus this theorem
records the striking convexity clause without enlarging the admitted mathematical core. -/
theorem fixedGrade_incompleteness (K : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ observationCount : ℕ,
        ∃ E : FiniteMixtureExperiment n observationCount,
          Convex ℝ (finitePriorCarrier n) ∧ E.SeparatedBy (fixedGradeInformationRadius n) ∧
            fixedGradeGapScale K n ≤
              E.certificationGap (K + 1) (fixedGradeInformationRadius n) := by
  filter_upwards [exists_fixedGrade_gap K] with n hn
  rcases hn with ⟨observationCount, E, hinf, hgap⟩
  exact ⟨observationCount, E, finitePriorCarrier_convex n, hinf, hgap⟩

end FiniteMixtureExperiment

/-! ## Total, proof-free input data -/

/-- A raw graded modulus.  `Δ` takes an absolute value, so clients cannot attach
an external nonnegativity theorem to the data. -/
structure GradedModulus where
  raw : ℕ → ℝ → ℝ

namespace GradedModulus

/-- The nonnegative modulus represented by `M`. -/
noncomputable def Δ (M : GradedModulus) (K : ℕ) (h : ℝ) : ℝ := |M.raw K h|

@[simp] theorem Δ_nonneg (M : GradedModulus) (K : ℕ) (h : ℝ) :
    0 ≤ M.Δ K h := abs_nonneg _

end GradedModulus

/-- A graded calculus has only numerical data.  The value-formula constant is
`exp logScale`, hence strictly positive without a proof field. -/
structure CertificateCalculus where
  modulus : GradedModulus
  logScale : ℝ

namespace CertificateCalculus

variable (C : CertificateCalculus)

/-- Positive scale in `risk = scale · Δ²`. -/
noncomputable def scale : ℝ := Real.exp C.logScale

@[simp] theorem scale_pos : 0 < C.scale := Real.exp_pos _

/-- Risk certified at grade `K` and information scale `h`. -/
noncomputable def certifiedRisk (K : ℕ) (h : ℝ) : ℝ :=
  C.scale * (C.modulus.Δ K h) ^ 2

/-- The value of the ungraded calculus.  Calling this a minimax risk requires
an actual minimax-duality proof; no such theorem is smuggled into this type. -/
noncomputable def ungradedRisk (h : ℝ) : ℝ :=
  C.scale * (C.modulus.Δ 0 h) ^ 2

theorem certifiedRisk_nonneg (K : ℕ) (h : ℝ) :
    0 ≤ C.certifiedRisk K h :=
  mul_nonneg C.scale_pos.le (sq_nonneg _)

@[simp] theorem ungradedRisk_eq_certifiedRisk_zero (h : ℝ) :
    C.ungradedRisk h = C.certifiedRisk 0 h := rfl

/-- Ratio of the ungraded value to the grade-`K` value. -/
noncomputable def deficit (K : ℕ) (h : ℝ) : ℝ :=
  C.ungradedRisk h / C.certifiedRisk K h

/-- Matching `K` moments costs no modulus at this scale. -/
def GradeInsensitive (K : ℕ) (h : ℝ) : Prop :=
  C.modulus.Δ K h = C.modulus.Δ 0 h

/-- The grade-`K` value equals the ungraded value. -/
def IsComplete (K : ℕ) (h : ℝ) : Prop :=
  C.certifiedRisk K h = C.ungradedRisk h

end CertificateCalculus

open CertificateCalculus

/-! ## Unconditional calculus laws -/

@[simp] theorem ungraded_isComplete (C : CertificateCalculus) (h : ℝ) :
    C.IsComplete 0 h := rfl

/-- The zero-grade deficit is total: it is `0` at a zero modulus and `1`
otherwise.  This removes the previous nonzero theorem parameter. -/
theorem ungraded_deficit_eq_ite (C : CertificateCalculus) (h : ℝ) :
    C.deficit 0 h = if C.modulus.Δ 0 h = 0 then 0 else 1 := by
  by_cases hz : C.modulus.Δ 0 h = 0
  · simp [CertificateCalculus.deficit, CertificateCalculus.ungradedRisk,
      CertificateCalculus.certifiedRisk, hz]
  · have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
    have hv : C.scale * (C.modulus.Δ 0 h) ^ 2 ≠ 0 :=
      mul_ne_zero hs (pow_ne_zero 2 hz)
    simp [CertificateCalculus.deficit, CertificateCalculus.ungradedRisk,
      CertificateCalculus.certifiedRisk, hz, hv]

/-- The certificate deficit is exactly the square of the modulus ratio.  The
positive scale cancels; no analytic theorem is an argument. -/
theorem deficit_eq_modulus_ratio_sq (C : CertificateCalculus) (K : ℕ) (h : ℝ) :
    C.deficit K h = (C.modulus.Δ 0 h / C.modulus.Δ K h) ^ 2 := by
  have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
  unfold CertificateCalculus.deficit CertificateCalculus.ungradedRisk
    CertificateCalculus.certifiedRisk
  rw [div_pow, mul_div_mul_left _ _ hs]

/-- Grade completeness is exactly grade-insensitivity.  Nonnegativity needed
to remove the square is derived from `abs`, not supplied by a caller. -/
theorem isComplete_iff_gradeInsensitive
    (C : CertificateCalculus) (K : ℕ) (h : ℝ) :
    C.IsComplete K h ↔ C.GradeInsensitive K h := by
  unfold CertificateCalculus.IsComplete CertificateCalculus.GradeInsensitive
    CertificateCalculus.certifiedRisk CertificateCalculus.ungradedRisk
  constructor
  · intro hEq
    have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
    have hsq : (C.modulus.Δ K h) ^ 2 = (C.modulus.Δ 0 h) ^ 2 :=
      mul_left_cancel₀ hs hEq
    have hroot := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (C.modulus.Δ_nonneg K h),
      abs_of_nonneg (C.modulus.Δ_nonneg 0 h)] at hroot
    exact hroot
  · intro hEq
    rw [hEq]

/-- An explicit numerical calculus used for examples and executable checks.
It carries no hidden envelope, moment-comparison, or duality theorem. -/
noncomputable def explicitCalculus
    (raw : ℕ → ℝ → ℝ) (logScale : ℝ) : CertificateCalculus where
  modulus := ⟨raw⟩
  logScale := logScale

@[simp] theorem explicitCalculus_modulus
    (raw : ℕ → ℝ → ℝ) (logScale : ℝ) (K : ℕ) (h : ℝ) :
    (explicitCalculus raw logScale).modulus.Δ K h = |raw K h| := rfl

end Calibrator.CertificateGrading

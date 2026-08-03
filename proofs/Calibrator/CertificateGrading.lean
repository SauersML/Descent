/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Graded certificate calculus without theorem-valued inputs

This module formalizes the algebra common to mixture-versus-mixture minimax
certificates.  It deliberately does **not** encode minimax duality, the
Donoho--Liu constant, a moment-comparison inequality, or a deconvolution
envelope as fields of a structure.  Those are theorems, not data.  Earlier
versions accepted them as `Prop`-valued fields and then proved consequences by
field projection.  That architecture has been removed.

What remains is unconditional:

* a modulus is nonnegative by construction;
* the value-formula scale is positive by construction;
* the ungraded calculus is complete relative to its own value definition;
* the deficit is exactly the square of a modulus ratio; and
* exact grade completeness is equivalent to grade-insensitivity.

The literature claims that grade two is within `5/4` in the Donoho--Liu
convex-linear regime and that some nonsmooth problems exhibit fixed-grade
incompleteness are recorded only as provenance in the surrounding research
documents.  They become Lean theorems here only when their proofs are present
in the repository.  A citation is never accepted as a theorem parameter.
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

end FinitePrior

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

/-- Total-variation distance between the two prior-predictive laws. -/
noncomputable def totalVariation
    (P Q : FinitePrior parameterCount) : ℝ :=
  (1 / 2 : ℝ) * ∑ x,
    |(E.mixture P).probability x - (E.mixture Q).probability x|

/-- The corresponding graded certificate problem. -/
noncomputable def certificateProblem :
    FiniteMomentCertificateProblem parameterCount where
  target := E.target
  moment := E.moment
  pairDiscrepancy := E.totalVariation

/-- Grade exponent used in the fixed-grade gap theorem.  Writing `K + 1`
makes the theorem total at grade zero while retaining order `1/K`. -/
noncomputable def fixedGradeExponent (K : ℕ) : ℝ :=
  1 / (K + 1 : ℝ)

/-- The explicit polynomial-over-logarithmic factor from the program. -/
noncomputable def fixedGradeGapScale (K n : ℕ) : ℝ :=
  (n + 2 : ℝ) ^ (fixedGradeExponent K / 2) /
    Real.sqrt (Real.log (n + 2 : ℝ))

/-- Modulus-level certification gap of this actual finite experiment. -/
noncomputable def certificationGap (K : ℕ) (h : ℝ) : ℝ :=
  E.certificateProblem.modulus 0 h /
    E.certificateProblem.modulus K h

/-- **Fixed-grade incompleteness.**  At every fixed positive grade there is a
sequence of finite mixture experiments whose ungraded-to-graded modulus ratio
is at least

`n^(b_K/2) / sqrt(log n)`, with `b_K = 1/(K+1) = Θ(1/K)`.

This is intentionally a visible proof obligation.  Its proof must construct
the moment-matching priors and compare their actual prior-predictive total
variation laws.  A conditional crossing hypothesis, an arbitrary discrepancy,
or a cited moment-comparison theorem is not accepted in its place. -/
theorem fixedGrade_incompleteness (K : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ observationCount : ℕ,
        ∃ E : FiniteMixtureExperiment n observationCount,
          fixedGradeGapScale K n ≤ E.certificationGap (K + 1) 1 := by
  sorry

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

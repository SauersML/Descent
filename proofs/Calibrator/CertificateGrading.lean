/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Certificate calculus without theorem-valued inputs

This module formalizes the algebra common to mixture-versus-mixture minimax
certificates.  It deliberately does **not** encode minimax duality, the
Donoho--Liu constant, a moment-comparison inequality, or a deconvolution
envelope as fields of a structure.  Those are theorems, not data, and accepting them as
`Prop`-valued fields would prove consequences by field projection.

What remains is unconditional:

* every modulus is nonnegative by construction;
* matching more moments can only shrink a moment-constrained modulus;
* allowing more atoms can only enlarge a certificate-complexity modulus;
* the value-formula scale is positive by construction; and
* equality with the unrestricted modulus is exactly modulus insensitivity.

The literature claim that two-point certificates are within `5/4` in the
Donoho--Liu convex-linear regime remains provenance only: this repository does
not yet contain the white-noise decision model needed to state it faithfully.
A citation is never accepted as a theorem parameter.

## The formulation repair

An earlier version called the number of moments the priors were *forced* to
match a certificate grade.  That reverses method power: increasing that number
removes feasible pairs, as `modulus_antitone_grade` proves.  It is a useful
approximation hierarchy, but it is not a hierarchy of increasingly powerful
lower-bound methods.  The repaired method grade is the total number of atoms
available to the two mixing priors.  Increasing it enlarges the feasible
family, and grade two is literally a point-versus-point certificate.

The removed fixed-grade rate statement also let its witness choose the target,
every moment probe, every parameter's observation law, and the observation
space after seeing `n`, the grade, and the requested bound.  Three guards were
not enough, and each failure remains a theorem here:

1. At radius `1` the discrepancy constraint is free, because total variation
   never exceeds one -- `feasible_one_iff_momentMatched`.  Feasibility is moment
   matching, and the observation kernel drops out entirely.
2. A shrinking radius does not repair that by itself.  If every kernel law lies
   within `ε` of one fixed law, every pair of priors is `2ε`-indistinguishable
   -- `totalVariation_le_two_mul_of_close` -- so a witness takes `ε` to be half
   the radius and the collapse returns.
3. Requiring `Informative`, i.e. nonzero pairwise separation, is still not
   enough: it carries no floor, so every pair may sit far below the radius.
   A quantitative floor such as `SeparatedBy` excludes that collapse, but does
   not turn catalogue size into sample size.

Consequently this module proves the calculus laws and the falsifiers, but makes
no polynomial-rate claim without a fixed growing-data experiment.  In
particular, `n` below indexes a parameter catalogue, not independent
observations.
-/

namespace Calibrator.CertificateGrading

open scoped BigOperators

/-! ## The certificate object itself

The numerical calculus below is useful only after saying what its modulus is.
The following definitions make the usual mixture-versus-mixture construction
literal.  A prior is Mathlib's canonical probability mass function on a
nonempty finite support, including boundary priors with zero-mass atoms.  Thus
there is no caller-supplied mass or positivity theorem.  Moment order `K` means
equality of the moments with indices `< K`.  The statistical experiment enters only
through a numerical discrepancy, and the modulus is the supremum of target
separations among feasible pairs.

Removing the moment constraint gives the unrestricted optimization, while
increasing the order shrinks the feasible set.  Any claim about the *value* or
*rate* of the resulting modulus still has to be proved for the particular
experiment.
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

/-- Atoms carrying positive mass.  This is derived from the PMF; callers do not
supply a support set. -/
noncomputable def activeAtoms (P : FinitePrior n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i ↦ P.probability i ≠ 0

/-- Number of atoms actually used by a finite prior. -/
noncomputable def atomCount (P : FinitePrior n) : ℕ :=
  P.activeAtoms.card

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

namespace FinitePrior

variable {n : ℕ}

/-- A probability law uses at least one atom. -/
theorem atomCount_pos (P : FinitePrior n) : 0 < P.atomCount := by
  classical
  by_contra h
  have hcard : P.activeAtoms.card = 0 := by
    exact Nat.eq_zero_of_not_pos h
  have hempty : P.activeAtoms = ∅ := Finset.card_eq_zero.mp hcard
  have hz : ∀ i, P.probability i = 0 := by
    intro i
    by_contra hi
    have himem : i ∈ P.activeAtoms := by
      simp [activeAtoms, hi]
    rw [hempty] at himem
    simp at himem
  have hsum := (finitePrior_probability_mem P).2
  simp only [hz, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- A point mass uses exactly one atom. -/
@[simp] theorem atomCount_pure (i : Fin (n + 1)) :
    atomCount (PMF.pure i) = 1 := by
  classical
  unfold atomCount activeAtoms probability
  have hfilter : Finset.univ.filter
      (fun j : Fin (n + 1) ↦ ((PMF.pure i) j).toReal ≠ 0) = {i} := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [PMF.pure_apply]
    · simp [PMF.pure_apply, hji]
  rw [hfilter]
  simp

end FinitePrior

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

/-- Vanishing identity: a prior compared with itself has no target gap. -/
theorem targetGap_self_eq_zero (P : FinitePrior n) :
    E.targetGap P P = 0 := by
  unfold targetGap
  simp


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

/-! ## Certificate complexity: atoms, not forced equalities

`modulus` above is the modulus after imposing `K` moment equalities.  It is
antitone in `K`, so `K` there is an approximation order, not method power.
The definitions below grade a mixture-versus-mixture certificate by the total
number of atoms in its two priors.  This feasible family grows with `K`.
-/

/-- A grade-`K` certificate uses at most `K` atoms across its two mixing
priors and satisfies the experiment's information constraint. -/
def AtomFeasible (K : ℕ) (h : ℝ) (P Q : FinitePrior n) : Prop :=
  P.atomCount + Q.atomCount ≤ K ∧ |E.pairDiscrepancy P Q| ≤ |h|

/-- Target gaps carried by certificates of atom complexity at most `K`. -/
noncomputable def admissibleAtomGaps (K : ℕ) (h : ℝ) : Set ℝ :=
  {d : ℝ | ∃ P Q, E.AtomFeasible K h P Q ∧ d = E.targetGap P Q}

/-- Certificate-complexity modulus.  Unlike the moment-constrained modulus,
this is monotone increasing in its grade. -/
noncomputable def atomModulus (K : ℕ) (h : ℝ) : ℝ :=
  sSup (insert 0 (E.admissibleAtomGaps K h))

theorem admissibleAtomGaps_bddAbove (K : ℕ) (h : ℝ) :
    BddAbove (insert 0 (E.admissibleAtomGaps K h)) := by
  refine ⟨2 * ∑ i, |E.target i|, ?_⟩
  intro d hd
  rcases hd with (rfl | ⟨P, Q, _, rfl⟩)
  · positivity
  · exact E.targetGap_le_catalogueBound P Q

theorem atomModulus_nonneg (K : ℕ) (h : ℝ) : 0 ≤ E.atomModulus K h := by
  apply le_csSup (E.admissibleAtomGaps_bddAbove K h)
  exact Set.mem_insert 0 _

/-- Increasing certificate complexity preserves every feasible certificate. -/
theorem atomFeasible_mono {K L : ℕ} (hKL : K ≤ L) (h : ℝ)
    {P Q : FinitePrior n} (hfeas : E.AtomFeasible K h P Q) :
    E.AtomFeasible L h P Q :=
  ⟨hfeas.1.trans hKL, hfeas.2⟩

/-- Method power is monotone: allowing more atoms can only enlarge the
certificate modulus. -/
theorem atomModulus_mono {K L : ℕ} (hKL : K ≤ L) (h : ℝ) :
    E.atomModulus K h ≤ E.atomModulus L h := by
  unfold atomModulus
  apply csSup_le_csSup (E.admissibleAtomGaps_bddAbove L h)
    ⟨0, Set.mem_insert 0 (E.admissibleAtomGaps K h)⟩
  intro d hd
  rcases hd with (rfl | ⟨P, Q, hfeas, rfl⟩)
  · exact Set.mem_insert 0 _
  · exact Set.mem_insert_iff.mpr <| Or.inr
      ⟨P, Q, E.atomFeasible_mono hKL h hfeas, rfl⟩

/-- No certificate can use fewer than two atoms: each probability law uses at
least one. -/
theorem not_atomFeasible_of_grade_lt_two {K : ℕ} (hK : K < 2) (h : ℝ)
    (P Q : FinitePrior n) : ¬ E.AtomFeasible K h P Q := by
  intro hfeas
  have hP := P.atomCount_pos
  have hQ := Q.atomCount_pos
  have hsum := hfeas.1
  omega

/-- Grade two contains every ordinary point-versus-point certificate. -/
theorem atomFeasible_two_pure_iff (h : ℝ) (i j : Fin (n + 1)) :
    E.AtomFeasible 2 h (PMF.pure i) (PMF.pure j) ↔
      |E.pairDiscrepancy (PMF.pure i) (PMF.pure j)| ≤ |h| := by
  simp [AtomFeasible]

/-- Every atom-bounded certificate is an unrestricted certificate. -/
theorem atomModulus_le_unrestricted (K : ℕ) (h : ℝ) :
    E.atomModulus K h ≤ E.modulus 0 h := by
  unfold atomModulus modulus
  apply csSup_le_csSup (E.admissibleGaps_bddAbove 0 h)
    ⟨0, Set.mem_insert 0 (E.admissibleAtomGaps K h)⟩
  intro d hd
  rcases hd with (rfl | ⟨P, Q, hfeas, rfl⟩)
  · exact Set.mem_insert 0 _
  · exact Set.mem_insert_iff.mpr <| Or.inr
      ⟨P, Q, ⟨E.momentMatched_zero P Q, hfeas.2⟩, rfl⟩

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

/-- Vanishing identity: a prior compared with itself has no total variation. -/
theorem totalVariation_self_eq_zero (P : FinitePrior parameterCount) :
    E.totalVariation P P = 0 := by
  unfold totalVariation
  simp


/-- **A kernel whose laws all sit within `ε` of one fixed law makes every pair of
priors `2ε`-indistinguishable**, no matter how many parameters it has.

WHY THIS MATTERS FOR RATE THEOREMS. A shrinking radius is necessary for the
discrepancy constraint to bind, but this says it is not sufficient: taking `ε`
to be half the radius makes `totalVariation ≤ radius` for EVERY pair, so
feasibility collapses to its algebraic constraints and the kernel drops out
exactly as it does at radius one.

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

This is why no sample-size incompleteness theorem is stated at `h = 1`: it
would be provable by a construction with no statistical content. -/
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
    simp
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

/-- Ratio between the unrestricted modulus and the certificates available with
at most `K` total atoms.  A quantitative incompleteness theorem for a concrete
experiment is a lower bound on this derived number; it is not an input field. -/
noncomputable def atomCertificationGap (K : ℕ) (h : ℝ) : ℝ :=
  E.certificateProblem.modulus 0 h /
    E.certificateProblem.atomModulus K h

/-- The two notions of grade have opposite monotonicity.  Moment order is
antitone because it imposes constraints; certificate complexity is monotone
because it permits constructions.  This is the formal reason they cannot be
identified. -/
theorem grading_direction_repair {K L : ℕ} (hKL : K ≤ L) (h : ℝ) :
    E.certificateProblem.modulus L h ≤ E.certificateProblem.modulus K h ∧
      E.certificateProblem.atomModulus K h ≤
        E.certificateProblem.atomModulus L h :=
  ⟨E.certificateProblem.modulus_antitone_grade hKL h,
    E.certificateProblem.atomModulus_mono hKL h⟩

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

/-- **The vanishing modulus**: no deviation at any grade or step.

`GradedModulus` had no exhibited inhabitant, so `Δ_nonneg` was a lower bound on a
quantity nothing had been shown to have. -/
def zero : GradedModulus where
  raw := fun _grade _step ↦ 0

instance instNonempty : Nonempty GradedModulus := ⟨zero⟩

/-- **The nonnegativity floor is attained.** `Δ_nonneg` alone is compatible with a
strictly positive floor -- an irreducible modulus no certificate could beat --
and this rules that out: zero is a value the graded modulus actually takes. -/
@[simp] theorem Δ_zero (K : ℕ) (h : ℝ) : zero.Δ K h = 0 := by
  unfold Δ zero
  simp

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

/-- Reference evaluation: the scale is the exponential of the recorded log scale. -/
theorem scale_at_reference_point : C.scale = Real.exp C.logScale := rfl


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

/-- A grade whose certified value is zero divides by zero and Mathlib returns `0`, so the
deficit reads as no shortfall exactly where the certificate carries no value at all. -/
theorem deficit_at_zero_certified_value_is_junk (K : ℕ) (h : ℝ)
    (hzero : C.certifiedRisk K h = 0) :
    C.deficit K h = 0 := by
  unfold deficit
  rw [hzero, div_zero]


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

/-! ## Two-point certificates are strictly incomplete

`atomModulus_mono` says allowing more atoms cannot hurt. On its own that is
compatible with the hierarchy being constant, in which case `atomCertificationGap`
is one everywhere and grading a certificate by its atom count distinguishes
nothing. Ruling that out needs an experiment where a higher grade strictly wins,
and this section exhibits one.

Three parameters emit an observation whose success probability is `0`, `1/2` and
`1`, and the target is `1` at the two extremes and `0` in the middle. The target
is therefore a strictly convex function of the observable, so it is not a
function of the prior-predictive law's mean.

At information radius zero, feasibility says the two prior-predictive laws
coincide. A point-versus-point certificate must then use the same parameter
twice, because the three success probabilities are distinct, and it carries no
target separation at all. Splitting one side across the two extremes holds the
predictive law fixed and moves the target by a full unit. So

    atomModulus 2 0 = 0 < 1 ≤ modulus 0 0

and the two-atom method misses the entire available separation.

Empirical status: DERIVED. The experiment is exhibited, not measured; the claim
is about what the certificate calculus can express.
-/

namespace FinitePrior

/-- **A one-atom law is a point mass.** This is what makes grade two literally the
point-versus-point method rather than merely containing it. -/
theorem eq_pure_of_atomCount_eq_one {n : ℕ} (P : FinitePrior n)
    (h : P.atomCount = 1) : ∃ i, P = PMF.pure i := by
  classical
  have hcard : P.activeAtoms.card = 1 := h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hzero : ∀ j, j ≠ i → P.probability j = 0 := by
    intro j hj
    by_contra hne
    have hmem : j ∈ P.activeAtoms := by simp [activeAtoms, hne]
    rw [hi, Finset.mem_singleton] at hmem
    exact hj hmem
  have hone : P.probability i = 1 := by
    have hsum := (finitePrior_probability_mem P).2
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ hzero j hj)
      (fun hc ↦ absurd (Finset.mem_univ i) hc)] at hsum
  refine ⟨i, PMF.ext fun j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj
    have hPj : P j = 1 := by
      have h1 : (P j).toReal = 1 := hone
      exact (ENNReal.toReal_eq_one_iff _).mp h1
    simp [hPj, PMF.pure_apply]
  · have hPj : P j = 0 := by
      have h0 : (P j).toReal = 0 := hzero j hj
      rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with hz | ht
      · exact hz
      · exact absurd ht (P.apply_ne_top j)
    simp [hPj, PMF.pure_apply, hj]

end FinitePrior

namespace FiniteMomentCertificateProblem

/-! ### The moment probes are invisible to both ends of the hierarchy

Grade zero imposes no moment equality and `AtomFeasible` never mentions the
moment field at all, so the two moduli compared below depend only on the target
and the discrepancy. Without this, a client with its own moment probes would
have to redo the whole computation to inherit the separation. -/

theorem admissibleGaps_zero_congr {n : ℕ} (E F : FiniteMomentCertificateProblem n)
    (ht : E.target = F.target) (hd : E.pairDiscrepancy = F.pairDiscrepancy) (h : ℝ) :
    E.admissibleGaps 0 h = F.admissibleGaps 0 h := by
  have hgap : ∀ P Q, E.targetGap P Q = F.targetGap P Q := by
    intro P Q; unfold targetGap; rw [ht]
  ext d
  constructor
  · rintro ⟨P, Q, hf, rfl⟩
    exact ⟨P, Q, ⟨F.momentMatched_zero P Q, by rw [← hd]; exact hf.2⟩, hgap P Q⟩
  · rintro ⟨P, Q, hf, rfl⟩
    exact ⟨P, Q, ⟨E.momentMatched_zero P Q, by rw [hd]; exact hf.2⟩, (hgap P Q).symm⟩

theorem modulus_zero_congr {n : ℕ} (E F : FiniteMomentCertificateProblem n)
    (ht : E.target = F.target) (hd : E.pairDiscrepancy = F.pairDiscrepancy) (h : ℝ) :
    E.modulus 0 h = F.modulus 0 h := by
  unfold modulus
  rw [admissibleGaps_zero_congr E F ht hd h]

theorem admissibleAtomGaps_congr {n : ℕ} (E F : FiniteMomentCertificateProblem n)
    (ht : E.target = F.target) (hd : E.pairDiscrepancy = F.pairDiscrepancy)
    (K : ℕ) (h : ℝ) :
    E.admissibleAtomGaps K h = F.admissibleAtomGaps K h := by
  have hgap : ∀ P Q, E.targetGap P Q = F.targetGap P Q := by
    intro P Q; unfold targetGap; rw [ht]
  ext d
  constructor
  · rintro ⟨P, Q, hf, rfl⟩
    exact ⟨P, Q, ⟨hf.1, by rw [← hd]; exact hf.2⟩, hgap P Q⟩
  · rintro ⟨P, Q, hf, rfl⟩
    exact ⟨P, Q, ⟨hf.1, by rw [hd]; exact hf.2⟩, (hgap P Q).symm⟩

theorem atomModulus_congr {n : ℕ} (E F : FiniteMomentCertificateProblem n)
    (ht : E.target = F.target) (hd : E.pairDiscrepancy = F.pairDiscrepancy)
    (K : ℕ) (h : ℝ) :
    E.atomModulus K h = F.atomModulus K h := by
  unfold atomModulus
  rw [admissibleAtomGaps_congr E F ht hd K h]

end FiniteMomentCertificateProblem

namespace FiniteMixtureExperiment

/-- Total variation is a function of the observation kernel alone. -/
theorem totalVariation_congr {p o : ℕ} (E F : FiniteMixtureExperiment p o)
    (h : E.observation = F.observation) (P Q : FinitePrior p) :
    E.totalVariation P Q = F.totalVariation P Q := by
  unfold totalVariation mixture
  rw [h]

end FiniteMixtureExperiment

/-- Observation laws whose success probabilities are `0`, `1/2`, `1`. The third
observation point carries no mass; it is present only so the observation space
matches the parameter space, which is the shape a catalogue-indexed biological
experiment has. -/
noncomputable def convexTargetObservation : Fin (2 + 1) → FinitePrior 2 :=
  ![PMF.pure 0,
    PMF.ofFintype ![1 / 2, 1 / 2, 0] (by
      rw [Fin.sum_univ_three]
      simp
      exact ENNReal.inv_two_add_inv_two),
    PMF.pure 1]

/-- The separating experiment: a strictly convex target over a one-dimensional
observable. -/
noncomputable def convexTargetExperiment : FiniteMixtureExperiment 2 2 where
  target := ![1, 0, 1]
  moment := fun _ _ ↦ 0
  observation := convexTargetObservation

/-- Prior-predictive probability of the observation `1`. -/
noncomputable def predictiveOne (P : FinitePrior 2) : ℝ :=
  P.probability 1 / 2 + P.probability 2

theorem convexTargetExperiment_mixture_one (P : FinitePrior 2) :
    (convexTargetExperiment.mixture P).probability 1 = predictiveOne P := by
  rw [convexTargetExperiment.mixture_probability P 1]
  simp [convexTargetExperiment, convexTargetObservation, predictiveOne,
    Fin.sum_univ_three, FinitePrior.probability, PMF.pure_apply,
    PMF.ofFintype_apply]
  ring

theorem convexTargetExperiment_mixture_zero (P : FinitePrior 2) :
    (convexTargetExperiment.mixture P).probability 0 = 1 - predictiveOne P := by
  have hmass : P.probability 0 + P.probability 1 + P.probability 2 = 1 := by
    have := (finitePrior_probability_mem P).2
    rwa [Fin.sum_univ_three] at this
  simp only [FinitePrior.probability] at hmass
  rw [convexTargetExperiment.mixture_probability P 0]
  simp [convexTargetExperiment, convexTargetObservation, predictiveOne,
    Fin.sum_univ_three, FinitePrior.probability, PMF.pure_apply,
    PMF.ofFintype_apply]
  linarith

theorem convexTargetExperiment_mixture_two (P : FinitePrior 2) :
    (convexTargetExperiment.mixture P).probability 2 = 0 := by
  rw [convexTargetExperiment.mixture_probability P 2]
  simp [convexTargetExperiment, convexTargetObservation,
    Fin.sum_univ_three, FinitePrior.probability, PMF.pure_apply,
    PMF.ofFintype_apply]

/-- The discrepancy of this experiment is the gap between prior-predictive
success probabilities. -/
theorem convexTargetExperiment_totalVariation (P Q : FinitePrior 2) :
    convexTargetExperiment.totalVariation P Q = |predictiveOne P - predictiveOne Q| := by
  unfold FiniteMixtureExperiment.totalVariation
  rw [Fin.sum_univ_three, convexTargetExperiment_mixture_zero,
    convexTargetExperiment_mixture_zero, convexTargetExperiment_mixture_one,
    convexTargetExperiment_mixture_one, convexTargetExperiment_mixture_two,
    convexTargetExperiment_mixture_two]
  rw [show (1 - predictiveOne P) - (1 - predictiveOne Q)
      = -(predictiveOne P - predictiveOne Q) by ring, abs_neg]
  simp
  ring

/-- The target mean is the mass at the two extreme parameters. -/
theorem convexTargetExperiment_mean (P : FinitePrior 2) :
    P.mean convexTargetExperiment.target = P.probability 0 + P.probability 2 := by
  unfold FinitePrior.mean
  simp [convexTargetExperiment, Fin.sum_univ_three]

theorem predictiveOne_pure (i : Fin (2 + 1)) :
    predictiveOne (PMF.pure i) = ![0, 1 / 2, 1] i := by
  fin_cases i <;>
    simp [predictiveOne, FinitePrior.probability, PMF.pure_apply]

/-- The three success probabilities are distinct, so equal prior-predictive laws
force the same parameter. -/
theorem pure_eq_of_predictiveOne_eq {i j : Fin (2 + 1)}
    (h : predictiveOne (PMF.pure i) = predictiveOne (PMF.pure j)) : i = j := by
  rw [predictiveOne_pure, predictiveOne_pure] at h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; norm_num at h)

/-! ### The two sides of the separation -/

/-- The certificate that splits one side across both extremes. -/
noncomputable def splitCertificate : FinitePrior 2 :=
  PMF.ofFintype ![1 / 2, 0, 1 / 2] (by
    rw [Fin.sum_univ_three]
    simp
    exact ENNReal.inv_two_add_inv_two)

theorem splitCertificate_probability :
    splitCertificate.probability 0 = 1 / 2 ∧ splitCertificate.probability 1 = 0 ∧
      splitCertificate.probability 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [splitCertificate, FinitePrior.probability, PMF.ofFintype_apply]

/-- **A grade-three certificate carries the full unit of separation.** -/
theorem one_le_convexTarget_modulus :
    (1 : ℝ) ≤ convexTargetExperiment.certificateProblem.modulus 0 0 := by
  obtain ⟨h0, h1, h2⟩ := splitCertificate_probability
  have hpsplit : predictiveOne splitCertificate = 1 / 2 := by
    unfold predictiveOne; rw [h1, h2]; norm_num
  have hppure : predictiveOne (PMF.pure (1 : Fin (2 + 1))) = 1 / 2 := by
    rw [predictiveOne_pure]; norm_num
  have hfeas : convexTargetExperiment.certificateProblem.Feasible 0 0
      splitCertificate (PMF.pure 1) := by
    refine ⟨convexTargetExperiment.certificateProblem.momentMatched_zero _ _, ?_⟩
    show |convexTargetExperiment.totalVariation splitCertificate (PMF.pure 1)| ≤ |(0 : ℝ)|
    rw [convexTargetExperiment_totalVariation, hpsplit, hppure]
    norm_num
  have hgap : convexTargetExperiment.certificateProblem.targetGap
      splitCertificate (PMF.pure 1) = 1 := by
    unfold FiniteMomentCertificateProblem.targetGap
    have h21 : ¬((2 : Fin (2 + 1)) = 1) := by decide
    show |FinitePrior.mean splitCertificate convexTargetExperiment.target -
      FinitePrior.mean (PMF.pure (1 : Fin (2 + 1))) convexTargetExperiment.target| = 1
    rw [convexTargetExperiment_mean, convexTargetExperiment_mean, h0, h2]
    norm_num [FinitePrior.probability, PMF.pure_apply, h21]
  have := convexTargetExperiment.certificateProblem.le_modulus_of_feasible 0 0
    splitCertificate (PMF.pure 1) hfeas
  rwa [hgap] at this

/-- **Every grade-two certificate carries none.** Both sides are point masses, the
discrepancy constraint forces the same parameter, and a parameter does not
separate from itself. -/
theorem convexTarget_atomModulus_two :
    convexTargetExperiment.certificateProblem.atomModulus 2 0 = 0 := by
  refine le_antisymm ?_ (convexTargetExperiment.certificateProblem.atomModulus_nonneg 2 0)
  refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
  rintro d (rfl | ⟨P, Q, hfeas, rfl⟩)
  · exact le_rfl
  · have hPpos := P.atomCount_pos
    have hQpos := Q.atomCount_pos
    have hPone : P.atomCount = 1 := by have := hfeas.1; omega
    have hQone : Q.atomCount = 1 := by have := hfeas.1; omega
    obtain ⟨i, rfl⟩ := P.eq_pure_of_atomCount_eq_one hPone
    obtain ⟨j, rfl⟩ := Q.eq_pure_of_atomCount_eq_one hQone
    have hd : |convexTargetExperiment.totalVariation (PMF.pure i) (PMF.pure j)| ≤ |(0 : ℝ)| :=
      hfeas.2
    rw [convexTargetExperiment_totalVariation, abs_abs] at hd
    norm_num at hd
    have hij : i = j := pure_eq_of_predictiveOne_eq (by linarith)
    subst hij
    unfold FiniteMomentCertificateProblem.targetGap
    simp

/-- **The certificate hierarchy is strict**: for this experiment the
point-versus-point method certifies nothing while the unrestricted method
certifies a full unit. This is what `atomModulus_mono` alone does not give, and
without it the atom grade would be a distinction with no difference. -/
theorem twoAtom_certificates_incomplete :
    convexTargetExperiment.certificateProblem.atomModulus 2 0 <
      convexTargetExperiment.certificateProblem.modulus 0 0 := by
  rw [convexTarget_atomModulus_two]
  linarith [one_le_convexTarget_modulus]

/-- **The ratio form of the gap is junk exactly where the gap is largest.**

`atomCertificationGap` divides by `atomModulus`, and Lean's `x / 0 = 0`, so at the
one experiment where the two-atom method fails completely the ratio reports zero
-- its smallest possible value -- rather than the unbounded loss it is meant to
name. `twoAtom_certificates_incomplete` is the statement to read; this theorem
exists so the ratio is not read instead. -/
theorem convexTarget_atomCertificationGap_is_junk :
    convexTargetExperiment.atomCertificationGap 2 0 = 0 := by
  unfold FiniteMixtureExperiment.atomCertificationGap
  rw [convexTarget_atomModulus_two, div_zero]

end Calibrator.CertificateGrading

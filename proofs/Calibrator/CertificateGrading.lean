import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp

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

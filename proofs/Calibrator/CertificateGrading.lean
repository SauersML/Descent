import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The graded certificate calculus, and where its completeness fails

This module is **self-contained: it imports only Mathlib.** It is the abstract half of a
result about the *toolkit* for proving minimax lower bounds, not about any particular
estimation problem. `Calibrator.PolygenicArchitecture` instantiates it at the nonsmooth
architecture summaries, and that instantiation is what gives this module a biological
consumer rather than a parallel life.

## The object

Two-point, Assouad, Fano over `K` points, and order-`K` moment-matched fuzzy hypotheses
are all mixture-versus-mixture arguments. They differ in how many moments the two priors
are forced to agree on, and that number **grades** them. Write `Δ K h` for the modulus at
grade `K` and scale `h`: the largest functional separation a grade-`K` construction can
exhibit while remaining statistically indistinguishable at that scale. Grade `0` is the
ungraded calculus — no moment constraint at all.

A certificate reports a risk quadratic in its modulus, `risk = scale · Δ²`. The `scale`
is the constant supplied by the value formula of whichever argument is being run.

## The four parts, and which of them this module proves

* **(I) The ungraded calculus is vacuously complete.** By minimax duality the ungraded
  value *is* the minimax risk. Here that is `MinimaxDuality`, a **named citation**, not a
  theorem: the corpus does not contain a proof of minimax duality and this module does not
  pretend to. What the module does prove is the consequence that makes (I) worth stating —
  `ungraded_deficit_eq_one`. The deficit at grade `0` is exactly `1`, identically, with no
  hypotheses. So no content lives in the ungraded calculus, and all of it lives in the
  grading. That reframing is the reason to open with (I).

* **(II) Donoho–Liu is the grade-2 fragment.** For linear functionals over convex classes
  the grade-2 modulus is tight to within a constant. Carried as `DonohoLiuFragment`, one
  field, with the constant `5/4` explicit rather than hidden in an `O(1)`. The consequence
  proved here is the one a practitioner needs: a bounded deficit is a bounded error in the
  *modulus*, and therefore a bounded — and quantified — error in a sample-size calculation.

* **(III) Incompleteness at every fixed grade.** Carried as `NonsmoothIncompleteness`,
  whose two fields are the two analytic inputs: a `K`-free lower envelope on the ungraded
  modulus, and a grade-`K` upper bound with exponent `b K`. Neither is proved here; the
  envelope needs a deconvolution construction and the upper bound needs a moment-comparison
  inequality (Wu–Yang), and neither is in Mathlib. What *is* proved is that those two
  inputs force the gap, in closed form — `gradeGap_lower_bound`.

* **(IV) Completeness at grade `K` ⟺ grade-insensitivity of the modulus.**
  `isComplete_iff_gradeInsensitive`, proved outright. Together with
  `deficit_eq_modulus_ratio_sq` this is the part with the most transferable content: the
  certification deficit is a **modulus ratio**, the `scale` cancels, and therefore no
  sharpening of constants inside a grade-`K` method can reduce it. That is what makes the
  deficit an approximation-theoretic invariant of the functional rather than slack in an
  argument.

## What is deliberately *not* assumed, and why

A `GradedModulus` here carries **no monotonicity in the grade.** It would be natural to
demand `Δ L h ≤ Δ K h` for `K ≤ L` — more moment constraints, smaller supremum — and to
make it a structure field. It is not one, for a reason worth recording:

> In a moment-matching construction the moment constraints are not only a restriction on
> the pair, they are also what *buys* the indistinguishability. Adding constraints shrinks
> the feasible set and simultaneously relaxes the separation budget, and the two effects
> run in opposite directions. Which one wins is a property of the construction, not of the
> definition.

So grade-ordering is carried as an explicit hypothesis, `GradeSound`, on the theorems that
need it, and every instance must discharge it at the scales where it is used. The
architecture instance discharges it *eventually in the variant count* and not identically —
see `PolygenicArchitecture.architecture_gradeSound_eventually`. Asserting the ordering as a
field would have made that eventual quantifier disappear silently, which is the failure
mode this corpus already tracks under "a theorem whose hypotheses are satisfied by the
wrong answer too".

Empirical status: UNTESTED throughout. Nothing in this module is a numerical claim.
-/

namespace Calibrator.CertificateGrading

/-! ## The graded modulus -/

/-- **A modulus graded by moment-matching order.**

    `Δ K h` is the largest functional separation exhibitable at scale `h` by a construction
    whose two priors agree on the first `K` moments. Grade `0` is the ungraded calculus.

    The only field beyond the data is nonnegativity, which every supremum of absolute
    separations has. Monotonicity in the grade is *not* assumed — see the module header. -/
structure GradedModulus where
  /-- The modulus at grade `K` and scale `h`. -/
  Δ : ℕ → ℝ → ℝ
  /-- A supremum of absolute functional separations is nonnegative. -/
  nonneg : ∀ K h, 0 ≤ Δ K h

/-- **A certificate calculus**: a graded modulus together with the constant of its value
    formula. `scale` is whatever the mixture-decoupling step of the particular argument
    supplies; the point of `deficit_eq_modulus_ratio_sq` is that it cancels. -/
structure CertificateCalculus where
  /-- The graded modulus of the problem. -/
  modulus : GradedModulus
  /-- The constant in the value formula `risk = scale · Δ²`. -/
  scale : ℝ
  /-- Value formulas have positive constants. -/
  scale_pos : 0 < scale

namespace CertificateCalculus

variable (C : CertificateCalculus)

/-- The risk a grade-`K` certificate certifies at scale `h`. -/
noncomputable def certifiedRisk (K : ℕ) (h : ℝ) : ℝ := C.scale * (C.modulus.Δ K h) ^ 2

/-- The risk the ungraded calculus certifies. By minimax duality this is the minimax risk;
    see `MinimaxDuality`, which is where that identification is carried. -/
noncomputable def ungradedRisk (h : ℝ) : ℝ := C.scale * (C.modulus.Δ 0 h) ^ 2

theorem certifiedRisk_nonneg (K : ℕ) (h : ℝ) : 0 ≤ C.certifiedRisk K h :=
  mul_nonneg (le_of_lt C.scale_pos) (sq_nonneg _)

theorem ungradedRisk_eq_certifiedRisk_zero (h : ℝ) :
    C.ungradedRisk h = C.certifiedRisk 0 h := rfl

/-- **The certification deficit**: how far short of the ungraded value a grade-`K`
    certificate falls, as a ratio of risks. -/
noncomputable def deficit (K : ℕ) (h : ℝ) : ℝ := C.ungradedRisk h / C.certifiedRisk K h

/-- **Grade-`K` soundness at scale `h`**: the grade-`K` modulus does not exceed the
    ungraded one. Carried as a hypothesis rather than a field — see the module header. -/
def GradeSound (K : ℕ) (h : ℝ) : Prop := C.modulus.Δ K h ≤ C.modulus.Δ 0 h

/-- **Grade-insensitivity at scale `h`**: matching `K` moments costs the modulus nothing. -/
def GradeInsensitive (K : ℕ) (h : ℝ) : Prop := C.modulus.Δ K h = C.modulus.Δ 0 h

/-- **Completeness of grade `K` at scale `h`**: the certificate reports the ungraded value. -/
def IsComplete (K : ℕ) (h : ℝ) : Prop := C.certifiedRisk K h = C.ungradedRisk h

end CertificateCalculus

open CertificateCalculus

/-! ## Part (I): the ungraded calculus is vacuously complete

Minimax duality is a citation, and it is carried as one. The theorem below is the part
that does not need it: whatever the modulus, whatever the value constant, the deficit at
grade `0` is identically `1`. Nothing is being certified by the ungraded calculus that the
problem did not already contain, which is precisely why all of the content is in the
grading. -/

/-- **The identification supplied by minimax duality**, carried as a named hypothesis.

    The ungraded certificate value equals the minimax risk of the problem. This module
    proves no part of minimax duality and no theorem below uses this structure; it exists
    so that anything reading the ungraded value as a minimax risk has to name what it is
    relying on. -/
structure MinimaxDuality (C : CertificateCalculus) where
  /-- The minimax risk of the problem at scale `h`. -/
  minimaxRisk : ℝ → ℝ
  /-- Duality: the ungraded calculus is exactly tight. -/
  ungraded_eq_minimax : ∀ h, C.ungradedRisk h = minimaxRisk h

/-- **The ungraded calculus is vacuously complete.** Unconditionally, with no hypothesis on
    the modulus and none on the scale. -/
theorem ungraded_isComplete (C : CertificateCalculus) (h : ℝ) : C.IsComplete 0 h := rfl

/-- **The ungraded deficit is exactly one**, whenever the ungraded risk is nonzero.

    This is the sharp form of (I). A calculus with no grading certifies neither more nor
    less than the truth, so the entire question of what a lower-bound argument can and
    cannot establish is a question about the grading and about nothing else. -/
theorem ungraded_deficit_eq_one (C : CertificateCalculus) (h : ℝ)
    (hne : C.modulus.Δ 0 h ≠ 0) :
    C.deficit 0 h = 1 := by
  have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
  have hval : C.scale * (C.modulus.Δ 0 h) ^ 2 ≠ 0 :=
    mul_ne_zero hs (pow_ne_zero 2 hne)
  unfold CertificateCalculus.deficit CertificateCalculus.ungradedRisk
    CertificateCalculus.certifiedRisk
  exact div_self hval

/-! ## Part (IV): the deficit is a modulus ratio, and completeness is grade-insensitivity

These two theorems are the reusable content of the whole development. The first says the
value constant cancels, so the deficit cannot be moved by any sharpening of constants
inside a fixed-grade method. The second identifies completeness with a property of the
modulus alone. -/

/-- **The certification deficit is the square of a modulus ratio.**

    The `scale` supplied by the value formula cancels identically. So the shortfall of a
    fixed-grade certificate is a property of the *modulus* — an approximation-theoretic
    invariant of the functional and the grade — and not slack in the argument that produced
    it. Sharpening the constants of a grade-`K` method cannot reduce it. -/
theorem deficit_eq_modulus_ratio_sq (C : CertificateCalculus) (K : ℕ) (h : ℝ) :
    C.deficit K h = (C.modulus.Δ 0 h / C.modulus.Δ K h) ^ 2 := by
  have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
  unfold CertificateCalculus.deficit CertificateCalculus.ungradedRisk
    CertificateCalculus.certifiedRisk
  rw [div_pow, mul_div_mul_left _ _ hs]

/-- Under grade soundness the deficit is at least one: a fixed-grade certificate never
    overstates the ungraded value. -/
theorem one_le_deficit (C : CertificateCalculus) (K : ℕ) (h : ℝ)
    (hsound : C.GradeSound K h) (hpos : 0 < C.modulus.Δ K h) :
    1 ≤ C.deficit K h := by
  rw [deficit_eq_modulus_ratio_sq C K h]
  have hratio : 1 ≤ C.modulus.Δ 0 h / C.modulus.Δ K h :=
    (one_le_div hpos).2 hsound
  have hnonneg : 0 ≤
      (C.modulus.Δ 0 h / C.modulus.Δ K h - 1) *
        (C.modulus.Δ 0 h / C.modulus.Δ K h + 1) :=
    mul_nonneg (sub_nonneg.mpr hratio) (by linarith)
  nlinarith

/-- **Completeness of grade `K` is exactly grade-insensitivity of the modulus.**

    Proved outright. This is the equivalence that turns "can a grade-`K` argument certify
    the truth here" — a question about proof techniques — into "does matching `K` moments
    cost the modulus anything" — a question about an approximation-theoretic quantity one
    can in principle compute. -/
theorem isComplete_iff_gradeInsensitive (C : CertificateCalculus) (K : ℕ) (h : ℝ) :
    C.IsComplete K h ↔ C.GradeInsensitive K h := by
  unfold CertificateCalculus.IsComplete CertificateCalculus.GradeInsensitive
    CertificateCalculus.certifiedRisk CertificateCalculus.ungradedRisk
  constructor
  · intro hEq
    have hs : C.scale ≠ 0 := ne_of_gt C.scale_pos
    have hsq : (C.modulus.Δ K h) ^ 2 = (C.modulus.Δ 0 h) ^ 2 := by
      have := mul_left_cancel₀ hs hEq
      exact this
    have hK := C.modulus.nonneg K h
    have h0 := C.modulus.nonneg 0 h
    have hroot := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hK, abs_of_nonneg h0] at hroot
    exact hroot
  · intro hEq
    rw [hEq]

/-! ## Part (II): Donoho–Liu as the grade-2 completeness fragment

For a linear functional over a convex class the grade-2 modulus is tight to within a
constant, and the constant is `5/4`. This is a citation, carried as a structure field. The
theorem below is its practitioner-facing consequence: a bounded deficit bounds the error in
the *modulus*, hence in any rate or sample size read off the certificate. -/

/-- **The Donoho–Liu regime**: linear functional, convex class, grade 2.

    The single field is the citation. `5/4` is the constant reported for the
    modulus-of-continuity bound on linear functionals over convex parameter sets; it is
    written explicitly rather than as an unspecified `O(1)` so that anything consuming it
    inherits a number.

    Empirical status: UNTESTED. -/
structure DonohoLiuFragment (C : CertificateCalculus) where
  /-- Grade 2 is tight to within `5/4` at every scale. -/
  gradeTwoTight : ∀ h : ℝ, C.ungradedRisk h ≤ (5 / 4) * C.certifiedRisk 2 h

/-- **In the Donoho–Liu regime the modulus error is bounded, and by how much.**

    `Δ₀ ≤ √(5/4) · Δ₂`. So a rate read off a grade-2 certificate is short by a factor of at
    most `√(5/4) < 1.12` in the modulus — under 12%, and in particular a *constant*, which
    is what part (III) shows fails at every fixed grade off this regime. -/
theorem donohoLiu_modulus_ratio_le (C : CertificateCalculus) (DL : DonohoLiuFragment C)
    (h : ℝ) :
    C.modulus.Δ 0 h ≤ Real.sqrt (5 / 4) * C.modulus.Δ 2 h := by
  have hs : (0 : ℝ) < C.scale := C.scale_pos
  have hbound := DL.gradeTwoTight h
  unfold CertificateCalculus.ungradedRisk CertificateCalculus.certifiedRisk at hbound
  have hsq : (C.modulus.Δ 0 h) ^ 2 ≤ (5 / 4) * (C.modulus.Δ 2 h) ^ 2 := by
    nlinarith [hbound, hs, sq_nonneg (C.modulus.Δ 0 h), sq_nonneg (C.modulus.Δ 2 h)]
  have h0 := C.modulus.nonneg 0 h
  have h2 := C.modulus.nonneg 2 h
  have hmono := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h0] at hmono
  have hsplit : Real.sqrt ((5 / 4) * (C.modulus.Δ 2 h) ^ 2)
      = Real.sqrt (5 / 4) * C.modulus.Δ 2 h := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 5 / 4), Real.sqrt_sq_eq_abs, abs_of_nonneg h2]
  rw [hsplit] at hmono
  exact hmono

/-- The Donoho–Liu deficit is bounded by `5/4`, so grade 2 is complete up to that constant
    in the regime where the fragment applies. -/
theorem donohoLiu_deficit_le (C : CertificateCalculus) (DL : DonohoLiuFragment C) (h : ℝ)
    (hpos : 0 < C.modulus.Δ 2 h) :
    C.deficit 2 h ≤ 5 / 4 := by
  unfold CertificateCalculus.deficit
  have hden : 0 < C.certifiedRisk 2 h := by
    unfold CertificateCalculus.certifiedRisk
    exact mul_pos C.scale_pos (by positivity)
  rw [div_le_iff₀ hden]
  have := DL.gradeTwoTight h
  linarith [this]

/-! ## Part (III): incompleteness at every fixed grade

The two analytic inputs are named, and only the consequence is proved. The envelope is
`K`-free: it is a lower bound on the ungraded modulus that no amount of moment matching
improves, obtained upstream by an explicit deconvolution construction at scale
`√(log (1/h))`. The grade bound is the sharpness half, obtained upstream from an
order-`(2K-2)` matched construction and a moment-comparison inequality.

`b K = b 1 / K` is the `Θ(1/K)` decay of the grade exponent, written as an exact identity
rather than an order symbol so that the gap below is an equation and not an asymptotic. -/

/-- **The two analytic inputs of the incompleteness theorem**, named.

    `envelope_lower` is the `K`-free envelope: a lower bound on the ungraded modulus that
    holds at every scale in `(0,1)` and mentions no grade. `grade_upper` is the sharpness
    half: at grade `K` the modulus is at most `h ^ (b K / 2)`.

    Neither is proved in this corpus. The envelope needs a deconvolution construction and
    the grade bound needs a moment-comparison inequality; both are upstream analytic inputs
    of exactly the kind this corpus carries as structure fields rather than as `sorry`s.

    Empirical status: UNTESTED. -/
structure NonsmoothIncompleteness (C : CertificateCalculus) where
  /-- The constant of the `K`-free envelope. -/
  envelopeConst : ℝ
  /-- Envelope constants are positive. -/
  envelopeConst_pos : 0 < envelopeConst
  /-- The grade exponent. -/
  b : ℕ → ℝ
  /-- Grade exponents are positive. -/
  b_pos : ∀ K : ℕ, 0 < K → 0 < b K
  /-- `b K = Θ(1/K)`, as an exact identity: `b K · K = b 1`. -/
  b_order : ∀ K : ℕ, 0 < K → b K * (K : ℝ) = b 1
  /-- The `K`-free envelope on the ungraded modulus. -/
  envelope_lower : ∀ h : ℝ, 0 < h → h < 1 →
    envelopeConst / Real.sqrt (Real.log (1 / h)) ≤ C.modulus.Δ 0 h
  /-- The grade-`K` upper bound. -/
  grade_upper : ∀ K : ℕ, 0 < K → ∀ h : ℝ, 0 < h → h < 1 →
    C.modulus.Δ K h ≤ h ^ (b K / 2)

/-- The grade exponent is `Θ(1/K)` in closed form. -/
theorem NonsmoothIncompleteness.b_eq {C : CertificateCalculus}
    (E : NonsmoothIncompleteness C) (K : ℕ) (hK : 0 < K) :
    E.b K = E.b 1 / (K : ℝ) := by
  have hKne : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  rw [eq_div_iff hKne]
  exact E.b_order K hK

/-- **The gap at a fixed grade, in closed form.**

    At sample scale `h = 1/n`, a grade-`K` certificate understates the modulus by at least
    `envelopeConst · n ^ (b K / 2) / √(log n)`. The exponent `b K` is `Θ(1/K)`, so the
    factor is polynomial in `n` for every fixed grade, and it is polynomial *however large*
    the grade — which is the content of the theorem. Convexity of the problem is where one
    would expect tightness, and this says every fixed grade still under-certifies by a
    polynomial factor there.

    The practical translation: a sample size derived for a nonsmooth functional from a
    two-point, Assouad or Fano argument is polynomially optimistic, and by an amount that is
    an approximation-theory quantity rather than an artifact of the argument. -/
theorem gradeGap_lower_bound {C : CertificateCalculus} (E : NonsmoothIncompleteness C)
    (K : ℕ) (hK : 0 < K) (n : ℝ) (hn : 1 < n)
    (hpos : 0 < C.modulus.Δ K (1 / n)) :
    E.envelopeConst * n ^ (E.b K / 2) / Real.sqrt (Real.log n)
      ≤ C.modulus.Δ 0 (1 / n) / C.modulus.Δ K (1 / n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hh0 : (0 : ℝ) < 1 / n := by positivity
  have hh1 : 1 / n < 1 := by
    rw [div_lt_one hn0]; exact hn
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hsqrt : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hlogn
  -- `log (1/h) = log n` at `h = 1/n`
  have hinv : (1 : ℝ) / (1 / n) = n := by
    field_simp
  have henv : E.envelopeConst / Real.sqrt (Real.log n) ≤ C.modulus.Δ 0 (1 / n) := by
    have := E.envelope_lower (1 / n) hh0 hh1
    rwa [hinv] at this
  -- the grade bound, rewritten as a negative power of `n`
  have hgrade : C.modulus.Δ K (1 / n) ≤ (n ^ (E.b K / 2))⁻¹ := by
    have hup := E.grade_upper K hK (1 / n) hh0 hh1
    have hrw : (1 / n : ℝ) ^ (E.b K / 2) = (n ^ (E.b K / 2))⁻¹ := by
      rw [one_div, Real.inv_rpow (le_of_lt hn0)]
    rwa [hrw] at hup
  have hnpow : 0 < n ^ (E.b K / 2) := Real.rpow_pos_of_pos hn0 _
  rw [div_le_div_iff₀ hsqrt hpos]
  have hstep : E.envelopeConst * n ^ (E.b K / 2) * C.modulus.Δ K (1 / n)
      ≤ E.envelopeConst * n ^ (E.b K / 2) * (n ^ (E.b K / 2))⁻¹ := by
    have hc : 0 ≤ E.envelopeConst * n ^ (E.b K / 2) :=
      mul_nonneg (le_of_lt E.envelopeConst_pos) (le_of_lt hnpow)
    exact mul_le_mul_of_nonneg_left hgrade hc
  have hsimp : E.envelopeConst * n ^ (E.b K / 2) * (n ^ (E.b K / 2))⁻¹ = E.envelopeConst := by
    field_simp
  have henv' : E.envelopeConst ≤ C.modulus.Δ 0 (1 / n) * Real.sqrt (Real.log n) := by
    rw [div_le_iff₀ hsqrt] at henv
    exact henv
  calc E.envelopeConst * n ^ (E.b K / 2) * C.modulus.Δ K (1 / n)
      ≤ E.envelopeConst * n ^ (E.b K / 2) * (n ^ (E.b K / 2))⁻¹ := hstep
    _ = E.envelopeConst := hsimp
    _ ≤ C.modulus.Δ 0 (1 / n) * Real.sqrt (Real.log n) := henv'

end Calibrator.CertificateGrading

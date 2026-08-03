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

## Monotonicity in the grade: I hedged, and the hedge was wrong

A first version of this header declined to make grade-ordering a structure field, on the
grounds that "moment constraints are not only a restriction on the pair, they are also what
*buys* the indistinguishability, and which effect wins is a property of the construction".

**That reasoning is wrong, and an LP measurement says so.** The grade-`(K+1)` feasible set is
a *subset* of the grade-`K` set at the same scale and support, so the supremum cannot rise:
monotonicity is forced by nesting and was never an empirical question. `gradeSound_of_nested_sup`
below is the one-line proof. Measurement agreed — 0 violations across 198 `(A,K,h)` cells,
largest step up `1.7e-12`.

The resolution of the tension I thought I saw: moment matching *does* buy small total
variation — at `A = 1` the grade-8 optimum has `TV = 4.8e-7` against the grade-0 optimum's
`2.1e-1` — but that cannot raise a supremum, because every grade-`K` construction is already
available to the grade-0 sup. **Indistinguishability is a constraint being satisfied, not a
budget being earned.** `GradeSound` is kept as an explicit hypothesis only because
`GradedModulus` is abstract and does not know it is a sup over nested sets; for any nested
reading it is a theorem, and the eventual quantifier in
Any downstream grade-soundness assumption for a nested feasible-set model is therefore
weaker than it needs to be.

## Part (III) FAILED its first measurement, and the mechanism is not an artifact

An LP over discretised priors — Gaussian location mixture, `F(π) = E_π|θ|`, grade `K` as the
number of matched moments, exact solves to `h = 1e-8` with grid refinement moving answers by
under 0.1% — reports:

* **The headline gap collapses.** The measured deficit `Δ₀/Δ₈` runs `3.284, 1.424, 1.007,
  1.012, 1.027` as `h` goes `1e-1 … 1e-6`, and on a growing support reaches `1.0007` at
  `h = 1e-9`. **A grade-8 certificate recovers 99.93% of the ungraded modulus.** There is no
  polynomial gap; by `isComplete_iff_gradeInsensitive` every fixed grade is very nearly
  *complete* here — the opposite of what part (III) asserts.
* **`b_order` is falsified in that instance.** The fitted exponent is grade-*independent* to
  within 0.7% (`0.1514 … 0.1524` across `K = 0…8`), so `b_K · K` grows linearly rather than
  staying constant.
* **The envelope shape is wrong at fixed support**: fitted `1/log(1/h)^{0.966}`, i.e.
  `1/log(1/h)`, not `1/√log(1/h)`. Growing the support at the scale this module names does
  bend the exponent toward `0.5`, reaching `0.74`, but over the accessible range the two
  shapes fit equally badly (~22%) and cannot be separated. Not refuted asymptotically; not
  confirmed either.

**The mechanism, and why it is the interesting part.** At small `h` the grade-0 optimiser
*already* matches moments to high order without being asked: its discrepancies at
`h = 1e-9` are `2.1e-11, 3.0e-9, 2.1e-9, 2.0e-7` in the first four. Statistical closeness
implies approximate moment matching, so the grading constraint becomes vacuous exactly in the
regime the theory is about — and a grading that is nearly free certifies nearly everything.

**A conceptual objection that outlives the numbers.** Grading these arguments by matched
moment count makes higher grades *weaker*, which is correct for the definition as written but
does **not** order the four named methods by power. Moment-matched fuzzy hypotheses are in
practice the *strongest* of the four, and they are strong because they admit rich many-atom
priors a two-point argument cannot use. The binding restriction that makes a two-point
argument weak is the **support size**, not the moment count. If part (III) is to be recovered,
the grading is probably the thing to change.

**What this does and does not do to the Lean.** `NonsmoothIncompleteness` carries the
envelope and the grade bound as *fields*, so `gradeGap_lower_bound` remains a true
conditional — nothing here makes a theorem false. What is now known is that the one instance
measured **does not satisfy those fields**, and that the mechanism above suggests they may be
unsatisfiable in the small-`h` regime rather than merely unverified. `sampleIncompleteness`
shows the fields are consistent; it does not show any statistical problem realises them, and
that gap is now measured rather than hypothetical.

Parts (I), (II) and (IV) are untouched. (IV) is pure algebra. (II)'s Donoho–Liu bound is
comfortably satisfied in the measurement: the grade-2 deficit runs `1.00`–`1.05`, far inside
`5/4`.

Empirical status: parts (I), (II), (IV) PROVED and unaffected; part (III) **conditional, with
its hypotheses FALSIFIED in the one instance measured**. See `proofs/validation/certgrading/`.
Nothing in this module is a numerical claim.
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

/-- **Grade-ordering is forced by nesting.**

    If the grade-`K` feasible set of prior pairs sits inside the grade-`0` set — which it
    does, since matching more moments is a further restriction — then the grade-`K` supremum
    cannot exceed the ungraded one. `GradeSound` is therefore automatic for any modulus
    presented as a sup over nested feasible sets, and is carried as a hypothesis elsewhere in
    this file only because `GradedModulus` is abstract enough not to know that. -/
theorem gradeSound_of_nested_sup (F : ℕ → ℝ → Set ℝ) (K : ℕ) (h : ℝ)
    (hsub : F K h ⊆ F 0 h) (hne : (F K h).Nonempty) (hbdd : BddAbove (F 0 h)) :
    sSup (F K h) ≤ sSup (F 0 h) :=
  csSup_le_csSup hbdd hne hsub

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
    most `√(5/4) < 1.12` in the modulus — under 12%, and in particular a constant.
    Part (III) would contrast with this only in an experiment satisfying its additional
    analytic assumptions. -/
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
    factor is polynomial in `n` for every fixed grade. This conclusion is conditional on
    `E`: neither convexity nor a statistical experiment is encoded by the theorem. The
    first audited Gaussian-mixture instance did not satisfy these fields, so no practical
    sample-size claim follows without a separate instantiation proof. -/
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

/-! ## The structures are inhabited, so the theorems are not vacuous

A theorem conditioned on a structure says nothing if the structure has no instances, and
this corpus tracks that failure mode explicitly. Both hypothesis-carrying structures above
are therefore given explicit instances here, so that `gradeGap_lower_bound` and
`donohoLiu_deficit_le` are known to be about something.

These instances are **witnesses of consistency, not models of any statistical problem**. They
are built to satisfy the fields and nothing more; exhibiting one does not establish that a
real minimax problem realizes the envelope or the grade bound, which remains the open
analytic content. -/

/-- A modulus realizing the incompleteness shape: envelope `A/√(log(1/h))` at grade `0` and
    `|h|^(c/2K)` at every positive grade. -/
noncomputable def sampleModulus (A c : ℝ) (hA : 0 ≤ A) : GradedModulus where
  Δ := fun K h =>
    if K = 0 then A / Real.sqrt (Real.log (1 / h)) else |h| ^ (c / (2 * (K : ℝ)))
  nonneg := by
    intro K h
    by_cases hK : K = 0
    · simp only [hK]
      exact div_nonneg hA (Real.sqrt_nonneg _)
    · simp only [if_neg hK]
      exact Real.rpow_nonneg (abs_nonneg h) _

theorem sampleModulus_zero (A c : ℝ) (hA : 0 ≤ A) (h : ℝ) :
    (sampleModulus A c hA).Δ 0 h = A / Real.sqrt (Real.log (1 / h)) := by
  rfl

theorem sampleModulus_pos (A c : ℝ) (hA : 0 ≤ A) {K : ℕ} (hK : K ≠ 0) (h : ℝ) :
    (sampleModulus A c hA).Δ K h = |h| ^ (c / (2 * (K : ℝ))) := by
  simp [sampleModulus, hK]

/-- The calculus built on `sampleModulus`, with unit value constant. -/
noncomputable def sampleCalculus (A c : ℝ) (hA : 0 ≤ A) : CertificateCalculus where
  modulus := sampleModulus A c hA
  scale := 1
  scale_pos := one_pos

/-- **`NonsmoothIncompleteness` is inhabited.** Its fields are jointly satisfiable, so the
    gap theorem is not conditioned on an empty hypothesis. -/
noncomputable def sampleIncompleteness (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    NonsmoothIncompleteness (sampleCalculus A c (le_of_lt hA)) where
  envelopeConst := A
  envelopeConst_pos := hA
  b := fun K => c / (K : ℝ)
  b_pos := by
    intro K hK
    have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    exact div_pos hc hK'
  b_order := by
    intro K hK
    have hK' : ((K : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
      exact ne_of_gt this
    push_cast
    field_simp
  envelope_lower := by
    intro h _ _
    exact le_of_eq (sampleModulus_zero A c (le_of_lt hA) h).symm
  grade_upper := by
    intro K hK h hh0 _
    have hEq : (sampleCalculus A c (le_of_lt hA)).modulus.Δ K h =
        |h| ^ (c / (2 * (K : ℝ))) := by
      change (sampleModulus A c (le_of_lt hA)).Δ K h = _
      exact sampleModulus_pos A c (le_of_lt hA) hK.ne' h
    rw [hEq, abs_of_pos hh0]
    have hexp : c / (K : ℝ) / 2 = c / (2 * (K : ℝ)) := by ring
    exact le_of_eq (by rw [hexp])

/-- **`DonohoLiuFragment` is inhabited.** A grade-insensitive calculus satisfies it with room
    to spare, which is the expected shape: the fragment is a statement about regimes where
    grading costs the modulus little. -/
def sampleDonohoLiu (C : CertificateCalculus)
    (hflat : ∀ h, C.modulus.Δ 2 h = C.modulus.Δ 0 h) : DonohoLiuFragment C where
  gradeTwoTight := by
    intro h
    unfold CertificateCalculus.ungradedRisk CertificateCalculus.certifiedRisk
    rw [hflat h]
    nlinarith [C.scale_pos, sq_nonneg (C.modulus.Δ 0 h)]

end Calibrator.CertificateGrading

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ChronologyReportLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.Decision Descent.Program

/-!
# The admixture chronology and its recombination-exposure representation

NOTE1 section 6.1 fixes a deterministic haploid recipient that starts monomorphic, receives
one-way migration from a donor fixed for the opposite haplotype at rate `m t ≥ 0`, and
recombines at rate `r t ≥ 0`, with no mutation, drift, selection or measurement noise. Both
marginal frequencies are then the single donor fraction `p t = 1 - e^{-M t}`, and the excess
of the doubly donor haplotype over the product of the marginals is `D`, obeying the coupled
system (27). This module builds `M`, `R`, `p` and the integrating-factor solution `D` of (28),
proves the derivative identities (27), proves that (28) is the unique solution vanishing at
time zero, and derives the recombination-exposure representation (29) and its scaling (30).

Rates are taken continuous on all of `ℝ` rather than merely on `[0, T]`, and merely integrable
rates are not formalised; continuity is what the fundamental theorem of calculus needs here
and it is the weakening NOTE1 anticipates. The pushforward of the immigration-increment
measure by the remaining recombination exposure, which NOTE1 (29) states measure-theoretically,
is formalised only in the equivalent integral form on `[0, T]`; the finitely supported
pushforward is carried by `ExposureLaplaceConstraints` and `FinitePulseExposure`.

The module also fixes the ordered-event recursion that NOTE1 Theorem 5 needs. An event is
either a block of pure recombination with a given exposure or a block of pure migration with a
given total, and each acts on the pair `(p, D)`. Both actions are proved to be the exact
solution of (27) over such a block: a recombination block multiplies `D` by the survival
factor of its exposure, and a constant-rate migration block sends `D` to
`D e^{-M} + (1 - p)² e^{-M} (1 - e^{-M})` while sending `p` to `1 - (1 - p) e^{-M}`. Those two
theorems are what makes the recursion the model rather than a definition.

Calendar time is not identified by the exposure transform. Speeding both rates up by a factor
`c`, `m ↦ c m(c ·)` and `r ↦ c r(c ·)`, gives a chronology whose cumulative totals, donor
fraction, linkage and normalised coupling at time `t` are those of the original at time `c t`
(`normalisedCoupling_timeRescaled`), under every recombination scale `λ`
(`scaled_normalisedCoupling_timeRescaled`). So knowing `C(λ)` for every `λ` does not determine
`m` and `r` in calendar time: `calendar_rates_not_identified` exhibits the constant rates `1`
observed at time `2` and `2` observed at time `1`, which are different histories with the same
donor fraction and the same `C(λ)` for every `λ`.

Not proved here: the attainable range of the coupling at fixed totals, which is
`AttainableChronologyCurve`, and the spectral constraints of NOTE1 (35) and (36), which are
`ExposureLaplaceConstraints`. Nothing here asserts that any measured population followed such a
chronology.

## Empirical status

None. The bodies here are calculus: the migration-recombination model is a stated mechanism,
not a measured population, and every theorem is an identity about the solutions of a stated
ordinary differential equation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AdmixtureChronologyLaw

noncomputable section

/-- The cumulative total of a rate, `∫₀ᵗ rate`. Taking `rate = m` gives the cumulative
migration `M` of NOTE1 section 6.1 and `rate = r` the cumulative recombination `R`. -/
def cumulativeRate (rate : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, rate s

/-- No time has passed, so no rate has accumulated. -/
@[simp] theorem cumulativeRate_zero (rate : ℝ → ℝ) : cumulativeRate rate 0 = 0 := by
  simp [cumulativeRate]

/-- The fundamental theorem of calculus for a continuous rate: the cumulative total
differentiates back to the rate. -/
theorem hasDerivAt_cumulativeRate (rate : ℝ → ℝ) (hrate : Continuous rate) (t : ℝ) :
    HasDerivAt (cumulativeRate rate) (rate t) t := by
  unfold cumulativeRate
  exact intervalIntegral.integral_hasDerivAt_right (hrate.intervalIntegrable _ _)
    hrate.aestronglyMeasurable.stronglyMeasurableAtFilter hrate.continuousAt

/-- A cumulative total of a continuous rate is continuous. -/
theorem continuous_cumulativeRate (rate : ℝ → ℝ) (hrate : Continuous rate) :
    Continuous (cumulativeRate rate) := by
  have hdiff : Differentiable ℝ (cumulativeRate rate) :=
    fun t ↦ (hasDerivAt_cumulativeRate rate hrate t).differentiableAt
  exact hdiff.continuous

/-- Scaling a whole rate history scales its cumulative total. -/
theorem cumulativeRate_const_mul (c : ℝ) (rate : ℝ → ℝ) (t : ℝ) :
    cumulativeRate (fun s ↦ c * rate s) t = c * cumulativeRate rate t :=
  intervalIntegral.integral_const_mul c rate

/-- A nonnegative rate accumulates a nonnegative total over forward time. -/
theorem cumulativeRate_nonneg (rate : ℝ → ℝ) (hnonneg : ∀ s, 0 ≤ rate s) (t : ℝ)
    (ht : 0 ≤ t) : 0 ≤ cumulativeRate rate t :=
  intervalIntegral.integral_nonneg ht (fun s _ ↦ hnonneg s)

/-- The donor ancestry fraction `p t = 1 - e^{-M t}`, which NOTE1 section 6.1 shows is the
common marginal frequency of both loci. -/
def donorFraction (m : ℝ → ℝ) (t : ℝ) : ℝ := 1 - Real.exp (-cumulativeRate m t)

/-- The recipient fraction is the migration survival factor. -/
theorem one_sub_donorFraction (m : ℝ → ℝ) (t : ℝ) :
    1 - donorFraction m t = Real.exp (-cumulativeRate m t) := by
  unfold donorFraction
  ring

/-- The recipient starts with no donor ancestry. -/
@[simp] theorem donorFraction_zero (m : ℝ → ℝ) : donorFraction m 0 = 0 := by
  simp [donorFraction]

/-- The donor fraction never reaches one: some recipient ancestry always survives a finite
migration total. -/
theorem donorFraction_lt_one (m : ℝ → ℝ) (t : ℝ) : donorFraction m t < 1 := by
  have hpos : 0 < Real.exp (-cumulativeRate m t) := Real.exp_pos _
  unfold donorFraction
  linarith

/-- A nonnegative migration rate gives a nonnegative donor fraction over forward time. -/
theorem donorFraction_nonneg (m : ℝ → ℝ) (hnonneg : ∀ s, 0 ≤ m s) (t : ℝ)
    (ht : 0 ≤ t) : 0 ≤ donorFraction m t := by
  have hM : 0 ≤ cumulativeRate m t := cumulativeRate_nonneg m hnonneg t ht
  have hle : Real.exp (-cumulativeRate m t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold donorFraction
  linarith

/-- Any strictly positive migration total gives a strictly positive donor fraction. -/
theorem donorFraction_pos (m : ℝ → ℝ) (t : ℝ) (hpos : 0 < cumulativeRate m t) :
    0 < donorFraction m t := by
  have hlt : Real.exp (-cumulativeRate m t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold donorFraction
  linarith

/-- NOTE1 (27), first equation: the donor fraction grows at the migration rate times the
surviving recipient fraction. -/
theorem hasDerivAt_donorFraction (m : ℝ → ℝ) (hm : Continuous m) (t : ℝ) :
    HasDerivAt (donorFraction m) (m t * (1 - donorFraction m t)) t := by
  have hsub := ((hasDerivAt_cumulativeRate m hm t).fun_neg).exp.const_sub 1
  refine hsub.congr_deriv ?_
  rw [one_sub_donorFraction]
  ring

/-- The integrating-factor solution (28) of the linkage equation: the excess of the doubly
donor haplotype over the product of the marginal frequencies. -/
def admixtureLinkage (m r : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-cumulativeRate m t - cumulativeRate r t) *
    ∫ s in (0 : ℝ)..t, m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)

/-- A monomorphic recipient carries no linkage. -/
@[simp] theorem admixtureLinkage_zero (m r : ℝ → ℝ) : admixtureLinkage m r 0 = 0 := by
  simp [admixtureLinkage]

/-- NOTE1 (27), second equation: the linkage decays at the combined migration and
recombination rate and is fed at the migration rate times the squared recipient fraction. -/
theorem hasDerivAt_admixtureLinkage (m r : ℝ → ℝ) (hm : Continuous m) (hr : Continuous r)
    (t : ℝ) :
    HasDerivAt (admixtureLinkage m r)
      (-(m t + r t) * admixtureLinkage m r t + m t * (1 - donorFraction m t) ^ 2) t := by
  have hMc := continuous_cumulativeRate m hm
  have hRc := continuous_cumulativeRate r hr
  have hcont : Continuous
      (fun s ↦ m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)) :=
    hm.mul ((hMc.neg.add hRc).rexp)
  have hG : HasDerivAt
      (fun v ↦ ∫ s in (0 : ℝ)..v, m s * Real.exp (-cumulativeRate m s + cumulativeRate r s))
      (m t * Real.exp (-cumulativeRate m t + cumulativeRate r t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hW := (((hasDerivAt_cumulativeRate m hm t).fun_neg).fun_sub
    (hasDerivAt_cumulativeRate r hr t)).exp
  refine (hW.fun_mul hG).congr_deriv ?_
  have h1 : Real.exp (cumulativeRate m t) ≠ 0 := Real.exp_ne_zero _
  have h2 : Real.exp (cumulativeRate r t) ≠ 0 := Real.exp_ne_zero _
  unfold admixtureLinkage
  rw [one_sub_donorFraction]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]
  field_simp
  ring

/-- Assumes: the candidate satisfies (27) at every time and starts uncoupled. Then it is
exactly the integrating-factor solution (28); the linear scalar equation has no other
solution. -/
theorem eq_admixtureLinkage_of_hasDerivAt (m r : ℝ → ℝ) (hm : Continuous m)
    (hr : Continuous r) (F : ℝ → ℝ) (hF0 : F 0 = 0)
    (hF : ∀ t, HasDerivAt F (-(m t + r t) * F t + m t * (1 - donorFraction m t) ^ 2) t)
    (t : ℝ) : F t = admixtureLinkage m r t := by
  have hMc := continuous_cumulativeRate m hm
  have hRc := continuous_cumulativeRate r hr
  have hcont : Continuous
      (fun s ↦ m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)) :=
    hm.mul ((hMc.neg.add hRc).rexp)
  have hderiv : ∀ u, HasDerivAt
      (fun v ↦ F v * Real.exp (cumulativeRate m v + cumulativeRate r v) -
        ∫ s in (0 : ℝ)..v, m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)) 0 u := by
    intro u
    have hG : HasDerivAt
        (fun v ↦ ∫ s in (0 : ℝ)..v, m s *
          Real.exp (-cumulativeRate m s + cumulativeRate r s))
        (m u * Real.exp (-cumulativeRate m u + cumulativeRate r u)) u :=
      intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
        hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
    have hexp := ((hasDerivAt_cumulativeRate m hm u).fun_add
      (hasDerivAt_cumulativeRate r hr u)).exp
    refine (((hF u).fun_mul hexp).fun_sub hG).congr_deriv ?_
    have h1 : Real.exp (cumulativeRate m u) ≠ 0 := Real.exp_ne_zero _
    have h2 : Real.exp (cumulativeRate r u) ≠ 0 := Real.exp_ne_zero _
    rw [one_sub_donorFraction]
    simp only [Real.exp_add, Real.exp_neg]
    field_simp
    ring
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) t 0
  simp only [cumulativeRate_zero, add_zero, Real.exp_zero, hF0, zero_mul,
    intervalIntegral.integral_same, sub_self] at hconst
  have hI : (∫ s in (0 : ℝ)..t, m s * Real.exp (-cumulativeRate m s + cumulativeRate r s)) =
      F t * Real.exp (cumulativeRate m t + cumulativeRate r t) := by linarith [hconst]
  have hprod : Real.exp (-cumulativeRate m t - cumulativeRate r t) *
      Real.exp (cumulativeRate m t + cumulativeRate r t) = 1 := by
    rw [← Real.exp_add, show -cumulativeRate m t - cumulativeRate r t +
      (cumulativeRate m t + cumulativeRate r t) = 0 from by ring, Real.exp_zero]
  unfold admixtureLinkage
  rw [hI]
  linear_combination (-F t) * hprod

/-- The normalised coupling `C = D / (p (1 - p))` of NOTE1 section 6.1: the linkage in units
of the common variance of the two loci. -/
def normalisedCoupling (m r : ℝ → ℝ) (t : ℝ) : ℝ :=
  admixtureLinkage m r t / (donorFraction m t * (1 - donorFraction m t))

/-- NOTE1 (29), the recombination-exposure representation: the normalised coupling is the
immigration-increment average of the survival factor `e^{-b}` of the recombination exposure
`b = R T - R s` still to be met by material that arrived at time `s`. -/
theorem normalisedCoupling_eq_exposure_integral (m r : ℝ → ℝ) (T : ℝ)
    (hpos : 0 < donorFraction m T) :
    normalisedCoupling m r T =
      1 / donorFraction m T *
        ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) *
          Real.exp (-(cumulativeRate r T - cumulativeRate r s)) := by
  have hkey : (∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) *
      Real.exp (-(cumulativeRate r T - cumulativeRate r s))) =
      Real.exp (-cumulativeRate r T) *
        ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s + cumulativeRate r s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro s _
    have h1 : Real.exp (cumulativeRate m s) ≠ 0 := Real.exp_ne_zero _
    have h2 : Real.exp (cumulativeRate r s) ≠ 0 := Real.exp_ne_zero _
    have h3 : Real.exp (cumulativeRate r T) ≠ 0 := Real.exp_ne_zero _
    simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]
    field_simp
  have h1 : Real.exp (cumulativeRate m T) ≠ 0 := Real.exp_ne_zero _
  have h2 : Real.exp (cumulativeRate r T) ≠ 0 := Real.exp_ne_zero _
  have h3 : donorFraction m T ≠ 0 := ne_of_gt hpos
  unfold normalisedCoupling admixtureLinkage
  rw [hkey, one_sub_donorFraction]
  simp only [Real.exp_sub, Real.exp_neg]
  field_simp

/-- NOTE1 (30): scaling the entire recombination history by `lam` replaces the survival factor
by `e^{-lam b}` against the same exposure weights. -/
theorem scaled_normalisedCoupling_eq_exposure_integral (m r : ℝ → ℝ) (lam T : ℝ)
    (hpos : 0 < donorFraction m T) :
    normalisedCoupling m (fun s ↦ lam * r s) T =
      1 / donorFraction m T *
        ∫ s in (0 : ℝ)..T, m s * Real.exp (-cumulativeRate m s) *
          Real.exp (-(lam * (cumulativeRate r T - cumulativeRate r s))) := by
  rw [normalisedCoupling_eq_exposure_integral m (fun s ↦ lam * r s) T hpos]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro s _
  simp only [cumulativeRate_const_mul]
  rw [show -(lam * cumulativeRate r T - lam * cumulativeRate r s) =
    -(lam * (cumulativeRate r T - cumulativeRate r s)) from by ring]

/-- Assumes: migration has stopped, so (27) reduces to pure recombination decay. Over such a
block the linkage is multiplied by exactly the survival factor of the recombination exposure
the block supplies. -/
theorem linkage_of_recombination_block (r : ℝ → ℝ) (hr : Continuous r) (F : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (-r t * F t) t) (t₀ t : ℝ) :
    F t = F t₀ * Real.exp (-(cumulativeRate r t - cumulativeRate r t₀)) := by
  have hderiv : ∀ u, HasDerivAt (fun v ↦ F v * Real.exp (cumulativeRate r v)) 0 u := by
    intro u
    refine ((hF u).fun_mul ((hasDerivAt_cumulativeRate r hr u).exp)).congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) t t₀
  have hne : Real.exp (cumulativeRate r t) ≠ 0 := Real.exp_ne_zero _
  rw [show -(cumulativeRate r t - cumulativeRate r t₀) =
      cumulativeRate r t₀ - cumulativeRate r t from by ring, Real.exp_sub, ← mul_div_assoc,
    eq_div_iff hne]
  exact hconst

/-- Assumes: recombination has stopped and migration proceeds at the constant rate `mrate`.
The recipient fraction then decays by exactly the block's migration total. -/
theorem donorFraction_of_migration_block (mrate : ℝ) (P : ℝ → ℝ)
    (hP : ∀ t, HasDerivAt P (mrate * (1 - P t)) t) (t₀ t : ℝ) :
    1 - P t = (1 - P t₀) * Real.exp (-(mrate * (t - t₀))) := by
  have hderiv : ∀ u, HasDerivAt
      (fun v ↦ (1 - P v) * Real.exp (mrate * (v - t₀))) 0 u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ ↦ mrate * (v - t₀)) mrate u := by
      have hstep := ((hasDerivAt_id u).sub_const t₀).const_mul mrate
      simpa using hstep
    refine (((hP u).const_sub 1).fun_mul hlin.exp).congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) t t₀
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hconst
  have hne : Real.exp (mrate * (t - t₀)) ≠ 0 := Real.exp_ne_zero _
  rw [← hconst, Real.exp_neg, mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- Assumes: recombination has stopped and migration proceeds at the constant rate `mrate`.
The linkage over such a block is damped by the block's migration total and gains exactly
`(1 - p₀)² e^{-M} (1 - e^{-M})`, which is the migration step of the ordered-event recursion. -/
theorem linkage_of_migration_block (mrate : ℝ) (P F : ℝ → ℝ)
    (hP : ∀ t, HasDerivAt P (mrate * (1 - P t)) t)
    (hF : ∀ t, HasDerivAt F (-mrate * F t + mrate * (1 - P t) ^ 2) t) (t₀ t : ℝ) :
    F t = F t₀ * Real.exp (-(mrate * (t - t₀))) +
      (1 - P t₀) ^ 2 * Real.exp (-(mrate * (t - t₀))) *
        (1 - Real.exp (-(mrate * (t - t₀)))) := by
  have hderiv : ∀ u, HasDerivAt
      (fun v ↦ F v * Real.exp (mrate * (v - t₀)) +
        (1 - P t₀) ^ 2 * Real.exp (-(mrate * (v - t₀)))) 0 u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ ↦ mrate * (v - t₀)) mrate u := by
      have hstep := ((hasDerivAt_id u).sub_const t₀).const_mul mrate
      simpa using hstep
    have hdecay : HasDerivAt
        (fun v ↦ (1 - P t₀) ^ 2 * Real.exp (-(mrate * (v - t₀))))
        ((1 - P t₀) ^ 2 * (Real.exp (-(mrate * (u - t₀))) * -mrate)) u :=
      (hlin.fun_neg).exp.const_mul _
    have hPu := donorFraction_of_migration_block mrate P hP t₀ u
    have hee : Real.exp (mrate * (u - t₀)) * Real.exp (-(mrate * (u - t₀))) = 1 := by
      rw [← Real.exp_add]
      simp
    refine (((hF u).fun_mul hlin.exp).fun_add hdecay).congr_deriv ?_
    rw [hPu]
    linear_combination
      (mrate * (1 - P t₀) ^ 2 * Real.exp (-(mrate * (u - t₀)))) * hee
  have hconst := is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
    (fun u ↦ (hderiv u).deriv) t t₀
  have hee : Real.exp (mrate * (t - t₀)) * Real.exp (-(mrate * (t - t₀))) = 1 := by
    rw [← Real.exp_add]
    simp
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at hconst
  linear_combination Real.exp (-(mrate * (t - t₀))) * hconst - F t * hee

/-- One ordered event of a piecewise chronology: a block of pure recombination supplying a
given exposure, or a block of pure migration supplying a given migration total. -/
inductive ChronologyEvent where
  /-- A block during which only recombination acts, of total exposure `exposure`. -/
  | recombination (exposure : ℝ)
  /-- A block during which only migration acts, of total `total`. -/
  | migration (total : ℝ)

/-- The action of one ordered event on the pair (donor fraction, linkage). -/
def stepEvent (event : ChronologyEvent) (state : ℝ × ℝ) : ℝ × ℝ :=
  match event with
  | ChronologyEvent.recombination exposure => (state.1, state.2 * Real.exp (-exposure))
  | ChronologyEvent.migration total =>
      (1 - (1 - state.1) * Real.exp (-total),
        state.2 * Real.exp (-total) +
          (1 - state.1) ^ 2 * Real.exp (-total) * (1 - Real.exp (-total)))

/-- A recombination block leaves the donor fraction alone and damps the linkage. -/
@[simp] theorem stepEvent_recombination (exposure : ℝ) (state : ℝ × ℝ) :
    stepEvent (ChronologyEvent.recombination exposure) state =
      (state.1, state.2 * Real.exp (-exposure)) := rfl

/-- A migration block replaces part of the recipient and feeds the linkage. -/
@[simp] theorem stepEvent_migration (total : ℝ) (state : ℝ × ℝ) :
    stepEvent (ChronologyEvent.migration total) state =
      (1 - (1 - state.1) * Real.exp (-total),
        state.2 * Real.exp (-total) +
          (1 - state.1) ^ 2 * Real.exp (-total) * (1 - Real.exp (-total))) := rfl

/-- The ordered chronology: apply the events to the initial state in order. -/
def runEvents (events : List ChronologyEvent) (state : ℝ × ℝ) : ℝ × ℝ :=
  events.foldl (fun current event ↦ stepEvent event current) state

/-- No events leave the state alone. -/
@[simp] theorem runEvents_nil (state : ℝ × ℝ) : runEvents [] state = state := rfl

/-- The recursion consumes its events from the front. -/
@[simp] theorem runEvents_cons (event : ChronologyEvent) (events : List ChronologyEvent)
    (state : ℝ × ℝ) :
    runEvents (event :: events) state = runEvents events (stepEvent event state) := rfl

/-- The migration total an event supplies. -/
def eventMigration (event : ChronologyEvent) : ℝ :=
  match event with
  | ChronologyEvent.recombination _ => 0
  | ChronologyEvent.migration total => total

/-- The recombination exposure an event supplies. -/
def eventRecombination (event : ChronologyEvent) : ℝ :=
  match event with
  | ChronologyEvent.recombination exposure => exposure
  | ChronologyEvent.migration _ => 0

/-- The recombination step of the recursion is the exact solution of (27) over a block with no
migration. -/
theorem stepEvent_recombination_eq_solution (r : ℝ → ℝ) (hr : Continuous r) (F : ℝ → ℝ)
    (hF : ∀ t, HasDerivAt F (-r t * F t) t) (t₀ t p₀ : ℝ) :
    stepEvent (ChronologyEvent.recombination (cumulativeRate r t - cumulativeRate r t₀))
      (p₀, F t₀) = (p₀, F t) := by
  simp only [stepEvent_recombination]
  rw [linkage_of_recombination_block r hr F hF t₀ t]

/-- The migration step of the recursion is the exact solution of (27) over a block with a
constant migration rate and no recombination. -/
theorem stepEvent_migration_eq_solution (mrate : ℝ) (P F : ℝ → ℝ)
    (hP : ∀ t, HasDerivAt P (mrate * (1 - P t)) t)
    (hF : ∀ t, HasDerivAt F (-mrate * F t + mrate * (1 - P t) ^ 2) t) (t₀ t : ℝ) :
    stepEvent (ChronologyEvent.migration (mrate * (t - t₀))) (P t₀, F t₀) = (P t, F t) := by
  have hp := donorFraction_of_migration_block mrate P hP t₀ t
  have hf := linkage_of_migration_block mrate P F hP hF t₀ t
  simp only [stepEvent_migration, Prod.mk.injEq]
  constructor
  · linarith [hp]
  · linarith [hf]

/-- The chronology and the report table of NOTE1 (31) meet here. Assumes: the donor fraction
and the normalised coupling of the chronology lie in the unit interval and the donor fraction
is strictly interior. The individual-level law at time `T` then has calibration slope equal to
the chronology's normalised coupling. -/
theorem chronology_report_slope (m r : ℝ → ℝ) (T : ℝ) (hp0 : 0 ≤ donorFraction m T)
    (hp1 : donorFraction m T ≤ 1) (hC0 : 0 ≤ normalisedCoupling m r T)
    (hC1 : normalisedCoupling m r T ≤ 1) (hlow : 0 < donorFraction m T)
    (hhigh : donorFraction m T < 1) :
    ChronologyReportLaw.linearSlope
        (ChronologyReportLaw.chronologyLaw (donorFraction m T) (normalisedCoupling m r T)
          hp0 hp1 hC0 hC1) = normalisedCoupling m r T :=
  ChronologyReportLaw.linearSlope_chronologyLaw _ _ hp0 hp1 hC0 hC1 hlow hhigh

/-- A change of calendar speed: the rate `s ↦ c · rate (c s)`, sped up by the factor `c`,
accumulates by time `t` exactly what the original rate accumulates by time `c t`. -/
theorem cumulativeRate_timeRescaled (rate : ℝ → ℝ) (speed t : ℝ) :
    cumulativeRate (fun s ↦ speed * rate (speed * s)) t = cumulativeRate rate (speed * t) := by
  have hchange : speed • ∫ s in (0 : ℝ)..t, rate (speed * s) =
      ∫ s in speed * 0..speed * t, rate s :=
    intervalIntegral.smul_integral_comp_mul_left rate speed
  unfold cumulativeRate
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul, hchange, mul_zero]

/-- The integrating-factor solution (28) under a change of calendar speed: the linkage of the
sped-up chronology at time `t` is the linkage of the original chronology at time `c t`. -/
theorem admixtureLinkage_timeRescaled (m r : ℝ → ℝ) (speed t : ℝ) :
    admixtureLinkage (fun s ↦ speed * m (speed * s)) (fun s ↦ speed * r (speed * s)) t =
      admixtureLinkage m r (speed * t) := by
  have hchange : speed • ∫ s in (0 : ℝ)..t,
      m (speed * s) * Real.exp (-cumulativeRate m (speed * s) + cumulativeRate r (speed * s)) =
        ∫ s in speed * 0..speed * t,
          m s * Real.exp (-cumulativeRate m s + cumulativeRate r s) :=
    intervalIntegral.smul_integral_comp_mul_left
      (fun u ↦ m u * Real.exp (-cumulativeRate m u + cumulativeRate r u)) speed
  rw [mul_zero] at hchange
  have hintegral : ∫ s in (0 : ℝ)..t, speed * m (speed * s) *
      Real.exp (-cumulativeRate m (speed * s) + cumulativeRate r (speed * s)) =
        ∫ s in (0 : ℝ)..speed * t,
          m s * Real.exp (-cumulativeRate m s + cumulativeRate r s) := by
    rw [← hchange, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ ↦ ?_)
    ring
  unfold admixtureLinkage
  simp only [cumulativeRate_timeRescaled]
  rw [hintegral]

/-- The donor fraction under a change of calendar speed: the sped-up chronology at time `t`
has the donor fraction of the original at time `c t`. -/
theorem donorFraction_timeRescaled (m : ℝ → ℝ) (speed t : ℝ) :
    donorFraction (fun s ↦ speed * m (speed * s)) t = donorFraction m (speed * t) := by
  unfold donorFraction
  rw [cumulativeRate_timeRescaled]

/-- The normalised coupling under a change of calendar speed: the sped-up chronology at time
`t` has the coupling of the original at time `c t`. -/
theorem normalisedCoupling_timeRescaled (m r : ℝ → ℝ) (speed t : ℝ) :
    normalisedCoupling (fun s ↦ speed * m (speed * s)) (fun s ↦ speed * r (speed * s)) t =
      normalisedCoupling m r (speed * t) := by
  unfold normalisedCoupling
  rw [admixtureLinkage_timeRescaled, donorFraction_timeRescaled]

/-- NOTE1 (30) under a change of calendar speed: scaling the recombination history of the
sped-up chronology by `λ` gives, at time `t`, the coupling of the original chronology with its
recombination scaled by `λ`, at time `c t`. So the whole transform `C(λ)` is unchanged. -/
theorem scaled_normalisedCoupling_timeRescaled (m r : ℝ → ℝ) (speed lam t : ℝ) :
    normalisedCoupling (fun s ↦ speed * m (speed * s)) (fun s ↦ lam * (speed * r (speed * s)))
        t =
      normalisedCoupling m (fun s ↦ lam * r s) (speed * t) := by
  have hrate : (fun s ↦ lam * (speed * r (speed * s))) =
      fun s ↦ speed * (lam * r (speed * s)) := by
    funext s
    ring
  rw [hrate]
  exact normalisedCoupling_timeRescaled m (fun u ↦ lam * r u) speed t

/-- NOTE1 section 6.3: the exposure transform does not identify the calendar-time rates. The
constant rates `m = r = 1` observed at time `2` and the doubled constant rates `m = r = 2`
observed at time `1` are different histories, yet they give the same donor fraction and the
same normalised coupling under every recombination scale `λ`. -/
theorem calendar_rates_not_identified (lam : ℝ) :
    (fun _ : ℝ ↦ (1 : ℝ)) ≠ (fun _ : ℝ ↦ (2 : ℝ)) ∧
      donorFraction (fun _ ↦ 2) 1 = donorFraction (fun _ ↦ 1) 2 ∧
        normalisedCoupling (fun _ ↦ 2) (fun _ ↦ lam * 2) 1 =
          normalisedCoupling (fun _ ↦ 1) (fun _ ↦ lam) 2 := by
  refine ⟨fun hsame ↦ by simpa using congrFun hsame 0, ?_, ?_⟩
  · have hfast := donorFraction_timeRescaled (fun _ ↦ 1) 2 1
    simpa using hfast
  · have hfast := scaled_normalisedCoupling_timeRescaled (fun _ ↦ 1) (fun _ ↦ 1) 2 lam 1
    simpa using hfast

end

end Descent.Portability.AdmixtureChronologyLaw

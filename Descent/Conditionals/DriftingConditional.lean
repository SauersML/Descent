/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib.Topology.Order.Monotone
import Descent.Layer

assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent.Conditionals

open scoped BigOperators

/-!
# A drifting response curve: what a moving threshold hides, and what the dynamics give back

Imports Mathlib and `Descent.Foundations.Probability`, for the standard normal `Foundations.Phi`.

A response curve is `c_t(s) = P(Y = 1 | S = s)` at time `t` — disease risk as a function of a
polygenic score, ancestry coordinate, or any covariate, in a population that is itself moving.
Three questions decide whether anything read off such a curve means anything: what is invisible
in principle, what survives the drift, and how much an interior estimate can be trusted.

## The threshold gauge, and why statics cannot break it

In a liability-threshold model `Y = 1[Z > θ]` — the standard reading of a polygenic score, with `Z`
liability and `θ` a diagnostic threshold — apply any strictly increasing `h` to the liability
axis. `indicator_lt_eq_of_strictMono` records that the indicator is unchanged. Every observable is
unchanged; the threshold path is changed into an arbitrary increasing relabelling, and can be
flattened to zero. **From response curves alone the threshold path is identifiable at most up to
monotone relabelling**, so a study reporting that diagnostic thresholds moved, on the strength of
fitted curves at several times, is reporting a gauge choice.

Fixing the noise shape narrows it to exactly one direction rather than all of them.
`linkedCurve_identified_modulo_constants` shows the observable determines `m_t - θ_t` and nothing
finer: the unidentified set is the constants-in-`s`, and it is exactly the constants. A
population shift that is uniform across the covariate and a threshold move of the same size are
the same observation, forever, at any density of sampling.

## The dynamics break it, because a generator kills constants

`sum_invariantWeight_mul_generator_eq_zero` is the mechanism: averaging against an invariant
distribution annihilates the population's own dynamics. So if the linked curve moves by a Markov
generator plus a spatially constant threshold velocity, the invariant average of its motion sees
only the threshold:

`invariantAverage_eq_neg_of_affine_evolution`: `Σ ϖ ∂ₜu = -θ̇`.

Everything on the right is observable. This is the whole content: **statics can never separate a
moving threshold from a moving population, and dynamics always can — provided the population
model carries no constant forcing.** `constantForcing_conflates_threshold` is the sharpness: add a
spatially uniform forcing `ζ` and the same average returns `ζ - θ̇`, so only the difference is
ever identified. A Markov generator is exactly a model whose forcing cone excludes constants,
which is why drift rescues an identification no amount of static data can reach.

For genetics the reading is direct. Secular change in diagnostic criteria, in ascertainment, or
in the definition of a case is a moving `θ`; environmental and demographic change is a moving
`m`. Cross-cohort recalibration studies routinely attribute drift in polygenic score performance
to one or the other. The separation is available, but only from the *motion*, and only if the
population's own dynamics are modelled as conservative — which is what a generator is.

## What survives a genuinely mixing drift

`continuousInvariant_eq_at_limit`: a continuous functional constant along the flow takes the same
value on the initial curve and on its limit. Under ergodic mixing the limit is the constant curve
at the base rate, so every continuous invariant of the response curve is a function of prevalence
alone. Discrimination, calibration slope, threshold location, curve shape: all transient. **Under
mixing the base rate is the only stable summary**, and the corpus's separate observation that
prevalence is the conserved charge of the drift is the same fact from the other side.

## How much an interior estimate can be trusted

`interiorError_sq_le_mul_endpoints` is the interpolation bound at the midpoint, in squared form so
that nothing is taken square roots of: the error energy at the midpoint is at most the product of
the endpoint energies. The constant is exactly one, and `singleMode_interiorError_eq` shows a
single spectral mode attains it, so the constant cannot be improved. An estimate of the response
curve between two observation times inherits the geometric mean of the errors at those times;
error does not blow up in the interior, and the hardest data are pure single modes.

## Scope

The finite-state and finite-mixture results are proved as stated. The Gaussian averaging identity,
affine-probit invariance, and the algebraic core of the drift-diffusion evolution law are also
proved. The full affine-probit necessity classification, `link_rigidity`, is proved: not through
the link's density, which would need smoothness the hypotheses do not give, but by reading the
link as the cdf of a liability measure and classifying the measures that are affinely
self-similar under Gaussian blurring. The reconstruction operator built from the observed
marginal likewise needs diffusion generators, Fréchet curve spaces, and time reversal.
`stationaryDrift_collapses_to_generator` proves the stationary algebraic core: the curve's
transport drift collapses back to the generator's own drift, which is why the stationary flow is
the semigroup itself.

Empirical status: DERIVED. The identification and stability results are proved at the stated
hypotheses; whether a given cohort series satisfies them — a conservative population model, a
known link, an invariant distribution — is an empirical question this asks to be answered rather
than assumed.
-/

/-! ## Two-point rigidity inside the probit family

The elementary rigidity below makes the later classification worth wanting: a probit response
curve is pinned by its values at two distinct covariate points, so the two-parameter
probit family admits no deformation at all once two observations are fixed.

The consequence for a drifting cohort is the one the scope note gestures at. If a
response curve is probit at each time and the drift moves it continuously, then the
whole trajectory is carried by two numbers, and any two time points that agree in the
curve at two covariate values agree in the curve everywhere. Rigidity is what makes
"the curve drifted" a two-parameter statement rather than an infinite-dimensional one.

Gaussian preservation is proved later by an explicit product-measure argument. Necessity — that
closure under every Gaussian averaging step forces affine-probit shape — is the classification
theorem `link_rigidity`, and it is proved too.
-/

section ProbitRigidity

/-- The probit response curve: `Φ (a x + b)` in the covariate `x`. -/
noncomputable def probitCurve (a b x : ℝ) : ℝ := Foundations.Phi (a * x + b)

/-- **Probit rigidity: two points determine the curve.**

`Φ` is strictly monotone hence injective, so agreement of two probit curves at a single
covariate value already forces their linear arguments to agree there. Two distinct
values then pin both parameters.

This is the identifiability statement behind reading a slope and a threshold off a
fitted curve: nothing else in the family passes through the same two points. -/
theorem probitCurve_params_eq_of_two_points {a b a' b' x y : ℝ} (hxy : x ≠ y)
    (hx : probitCurve a b x = probitCurve a' b' x)
    (hy : probitCurve a b y = probitCurve a' b' y) :
    a = a' ∧ b = b' := by
  have hlx : a * x + b = a' * x + b' := Foundations.strictMono_Phi.injective hx
  have hly : a * y + b = a' * y + b' := Foundations.strictMono_Phi.injective hy
  have hsub : (a - a') * (x - y) = 0 := by nlinarith [hlx, hly]
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have ha : a = a' := by
    rcases mul_eq_zero.mp hsub with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hxy'
  refine ⟨ha, ?_⟩
  rw [ha] at hlx
  linarith

/-- **Agreement at two points is agreement everywhere.**  The curve, not just its
parameters, is determined. -/
theorem probitCurve_eq_of_two_points {a b a' b' x y : ℝ} (hxy : x ≠ y)
    (hx : probitCurve a b x = probitCurve a' b' x)
    (hy : probitCurve a b y = probitCurve a' b' y) :
    ∀ z, probitCurve a b z = probitCurve a' b' z := by
  obtain ⟨ha, hb⟩ := probitCurve_params_eq_of_two_points hxy hx hy
  intro z
  rw [ha, hb]

/-- **The threshold gauge acts on the probit family by shifting the intercept.**

`indicator_lt_eq_of_strictMono` says a monotone relabelling of the liability axis is
invisible. Here is the same gauge freedom inside the probit family: moving the threshold
by `c` and the intercept by `-c` is the identity on the curve. Combined with rigidity,
this is exactly the statement that slope is identified and intercept is identified only
relative to a threshold convention. -/
theorem probitCurve_shift (a b c x : ℝ) :
    probitCurve a (b + c) x = probitCurve a b (x + c / a) ∨ a = 0 := by
  rcases eq_or_ne a 0 with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    unfold probitCurve
    congr 1
    field_simp
    ring

end ProbitRigidity

/-! ## The threshold gauge -/

/-- **A monotone relabelling of the liability axis is invisible.** Applying any strictly
increasing map to liability and threshold together leaves the case indicator unchanged, so no
observable distinguishes them. -/
theorem indicator_lt_eq_of_strictMono (h : ℝ → ℝ) (hmono : StrictMono h) (Z θ : ℝ) :
    (if θ < Z then (1 : ℝ) else 0) = (if h θ < h Z then (1 : ℝ) else 0) := by
  by_cases hlt : θ < Z
  · simp [hlt, hmono hlt]
  · have hle : h Z ≤ h θ := hmono.le_iff_le.mpr (not_lt.mp hlt)
    simp [hlt, not_lt.mpr hle]

/-- **With the noise shape fixed, the unidentified set is exactly the constants.**

    The observable is the linked curve `m - θ`, with `θ` constant in the covariate. Two
    population/threshold pairs are observationally identical exactly when they differ by one
    number added to both. A uniform population shift and a threshold move of the same size are
    the same observation. -/
theorem linkedCurve_identified_modulo_constants {ι : Type*}
    (m m' : ι → ℝ) (θ θ' : ℝ) :
    (∀ s, m s - θ = m' s - θ') ↔ (∀ s, m' s = m s + (θ' - θ)) := by
  constructor
  · intro h s
    have := h s
    linarith
  · intro h s
    have := h s
    linarith

/-! ## The dynamics separate them -/

/-- A distribution invariant for the generator: `ϖ` is annihilated by `L` acting on the left. -/
def IsInvariantWeight {n : ℕ} (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ j, ∑ i, ϖ i * L i j = 0

/-- A conservative generator kills constant functions. For the matrix action
    `(L u) i = ∑ j, L i j * u j`, this is exactly the zero-row-sum condition. -/
def KillsConstants {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, L i j = 0

/-- **The zero generator kills constants**, so the theorems assuming `KillsConstants` are
    about something. A predicate assumed by theorems and satisfied by nothing leaves them
    vacuously true -- kernel-checked, clean axiom report, no content. -/
theorem killsConstants_zero {n : ℕ} :
    KillsConstants (fun _ _ : Fin n ↦ (0 : ℝ)) := by
  intro i
  simp

/-- **A two-state symmetric switching generator kills constants**, which is the witness that
    matters biologically rather than the trivial one: rows `(-s, s)` and `(s, -s)` sum to
    zero, so ancestry switching at any rate is conservative. -/
theorem killsConstants_twoStateSwitch (s : ℝ) :
    KillsConstants (fun i j : Fin 2 ↦ if i = j then -s else s) := by
  intro i
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- The zero weight is invariant for every generator. This is a useful algebraic base case, but
it is not a probability weight because its total mass is zero. -/
theorem isInvariantWeight_zero {n : ℕ} (L : Fin n → Fin n → ℝ) :
    IsInvariantWeight (fun _ ↦ (0 : ℝ)) L := by
  intro j
  simp

/-- **The invariant-probability assumptions used below are jointly satisfiable.**

    On the nonempty state space `Fin (n + 1)`, put unit mass at state zero and take the zero
    generator. The weight has total mass one and is invariant. This explicit witness rules out
    vacuity without assuming that an arbitrary biological generator has a stationary law. -/
theorem exists_invariantProbabilityWeight (n : ℕ) :
    ∃ ϖ : Fin (n + 1) → ℝ, ∃ L : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ ϖ i) ∧ (∑ i, ϖ i = 1) ∧ IsInvariantWeight ϖ L := by
  refine ⟨fun i ↦ if i = 0 then 1 else 0, fun _ _ ↦ 0, ?_, ?_, ?_⟩
  · intro i
    positivity
  · simp
  · intro j
    simp

/-- A generator whose columns sum to zero admits the uniform weight as invariant, which is
    the witness that matters for a symmetric biological generator. -/
theorem isInvariantWeight_one_of_colSum_zero {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    IsInvariantWeight (fun _ ↦ (1 : ℝ)) L := by
  intro j
  simpa using hcol j

/-- **Averaging against an invariant distribution annihilates the population dynamics.** This is
the projection that exposes the exogenous constant. -/
theorem sum_invariantWeight_mul_generator_eq_zero {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hinv : IsInvariantWeight ϖ L) :
    ∑ i, ϖ i * (∑ j, L i j * u j) = 0 := by
  have hstep : ∀ i : Fin n, ϖ i * (∑ j, L i j * u j) = ∑ j, ϖ i * L i j * u j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← Finset.sum_mul, hinv j, zero_mul]

/-- **The threshold's velocity is minus the invariant average of the linked curve's motion.**

    `u` is the observed linked curve, moving by the population generator plus a spatially
    constant threshold velocity. Averaging against the invariant distribution kills the generator
    term and leaves `-θ̇`, with everything on the left observable.

    This is the exact separation that `linkedCurve_identified_modulo_constants` shows is
    impossible from statics: there the constant direction is unreachable at every fixed time, and
    here it is the only direction that survives. -/
theorem invariantAverage_eq_neg_of_affine_evolution {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u du : Fin n → ℝ) (thetaDot : ℝ)
    (hmass : ∑ i, ϖ i = 1) (hinv : IsInvariantWeight ϖ L)
    (hdyn : ∀ i, du i = (∑ j, L i j * u j) - thetaDot) :
    ∑ i, ϖ i * du i = -thetaDot := by
  have hsplit : ∀ i : Fin n,
      ϖ i * du i = ϖ i * (∑ j, L i j * u j) - thetaDot * ϖ i := by
    intro i
    rw [hdyn i]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_sub_distrib,
    sum_invariantWeight_mul_generator_eq_zero ϖ L u hinv, ← Finset.mul_sum, hmass]
  ring

/-- **Sharpness: a spatially uniform forcing is conflated with the threshold forever.**

    Add a constant forcing `ζ` to the population's motion and the same average returns
    `ζ - θ̇`. Only the difference is identified, at any sampling density, which is why the
    separation above needs the population model's forcing cone to exclude constants — and a
    Markov generator is exactly such a model. -/
theorem constantForcing_conflates_threshold {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u du : Fin n → ℝ) (thetaDot zeta : ℝ)
    (hmass : ∑ i, ϖ i = 1) (hinv : IsInvariantWeight ϖ L)
    (hdyn : ∀ i, du i = (∑ j, L i j * u j) + zeta - thetaDot) :
    ∑ i, ϖ i * du i = zeta - thetaDot := by
  have hsplit : ∀ i : Fin n,
      ϖ i * du i = ϖ i * (∑ j, L i j * u j) + (zeta - thetaDot) * ϖ i := by
    intro i
    rw [hdyn i]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib,
    sum_invariantWeight_mul_generator_eq_zero ϖ L u hinv, ← Finset.mul_sum, hmass]
  ring

/-- Subtracting a spatially constant threshold commutes with a conservative generator.

    This is the algebraic bridge between autonomous population motion and the linked response
    curve: it is derived here, rather than assumed as part of the curve dynamics. -/
theorem generator_linkedCurve_eq_generator {n : ℕ}
    (L : Fin n → Fin n → ℝ) (m : Fin n → ℝ) (theta : ℝ)
    (hconst : KillsConstants L) (i : Fin n) :
    ∑ j, L i j * (m j - theta) = ∑ j, L i j * m j := by
  calc
    ∑ j, L i j * (m j - theta) =
        (∑ j, L i j * m j) - theta * ∑ j, L i j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    _ = ∑ j, L i j * m j := by rw [hconst i, mul_zero, sub_zero]

/-- **Autonomous conservative population dynamics identify threshold velocity.**

    The population state `m` evolves by `dm = Lm`, while the observable linked curve is
    `m - theta` and therefore has velocity `dm - thetaDot`. The zero-row-sum condition derives
    the linked-curve equation; invariant averaging then removes `Lm` and returns `-thetaDot`.
    Unlike `invariantAverage_eq_neg_of_affine_evolution`, this theorem does not take the desired
    linked evolution as an input. -/
theorem invariantAverage_velocity_eq_neg_shift {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (m dm : Fin n → ℝ)
    (theta thetaDot : ℝ) (hmass : ∑ i, ϖ i = 1)
    (hinv : IsInvariantWeight ϖ L) (hconst : KillsConstants L)
    (hmotion : ∀ i, dm i = ∑ j, L i j * m j) :
    ∑ i, ϖ i * (dm i - thetaDot) = -thetaDot := by
  apply invariantAverage_eq_neg_of_affine_evolution ϖ L
    (fun j ↦ m j - theta) (fun i ↦ dm i - thetaDot) thetaDot hmass hinv
  intro i
  rw [hmotion i, generator_linkedCurve_eq_generator L m theta hconst i]

/-! ## Reconstruction: transporting a conditional through the observed marginal

Theorem 14. The marked subpopulation `q` and the population `p` are pushed forward by the SAME
one-step coupling, so a conditional observed at one time can be transported to the next by
pushing forward `κ p` and dividing by the pushed-forward marginal. That ratio is Bayes' rule
built from the observed marginals, and it is exact rather than approximate: nothing is estimated
in `reconstruct_eq_of_pushed_marked`, the two sides are the same number.

`reconstruct_between` is the half that makes it usable. The operator is a weighted average of the
conditional's own values, so it cannot leave their range: an error in the observed conditional is
never amplified by transporting it forward. That is the forward direction of the asymmetry the
analysis turns on, and the backward direction — where the same structure inverts and amplifies —
The backward direction is `pushForward_not_injective`, and it is worse than
amplification: under complete mixing the operator collapses distinct conditionals onto the same
image, so inverting it is not an ill-conditioned problem but an underdetermined one. No amount of
data about the pushed-forward conditional recovers which conditional produced it. -/

/-- One step of the coupling applied to a nonnegative density on a finite state space. -/
noncomputable def pushForward {n : ℕ} (M : Fin n → Fin n → ℝ) (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, M i j * f j

/-- **The backward direction is not merely amplifying, it is undetermined.**

`reconstruct_between` says transporting a conditional forward cannot leave the range of its own
values, so forward error never grows. The reverse fails for a stronger reason than instability:
a completely mixing step sends two different conditionals to the SAME image, so there is no
backward map to be ill-conditioned. Recovering the earlier conditional from the later one is not
a hard inverse problem; it is not an inverse problem.

The witness is the uniform two-state coupling with the two point conditionals. -/
theorem pushForward_not_injective :
    ∃ (M : Fin 2 → Fin 2 → ℝ) (f g : Fin 2 → ℝ),
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ f ≠ g ∧
      pushForward M f = pushForward M g := by
  refine ⟨fun _ _ ↦ (1 : ℝ) / 2, ![1, 0], ![0, 1], fun i j ↦ by norm_num,
    fun i ↦ by simp, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · funext i
    unfold pushForward
    simp [Fin.sum_univ_two]

/-- Transport a conditional through one step: push the marked subpopulation forward and divide
by the pushed-forward marginal. -/
noncomputable def reconstruct {n : ℕ} (M : Fin n → Fin n → ℝ) (p κ : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  pushForward M (fun j ↦ κ j * p j) i / pushForward M p i

/-- Where the pushed-forward law puts no mass the reconstruction divides by zero and Mathlib
returns `0`, reporting a conditional of zero rather than an undefined one. -/
theorem reconstruct_at_zero_mass_is_junk {n : ℕ} (M : Fin n → Fin n → ℝ) (p κ : Fin n → ℝ)
    (i : Fin n) (hzero : pushForward M p i = 0) :
    reconstruct M p κ i = 0 := by
  unfold reconstruct
  rw [hzero, div_zero]


/-- **Exactness.** If the marked subpopulation is `κ p`, the transported conditional is the ratio
of the two pushed-forward densities. Both are pushed by the same coupling, which is the whole
reason this is an identity and not an estimate. -/
theorem reconstruct_eq_of_pushed_marked {n : ℕ} (M : Fin n → Fin n → ℝ)
    (p κ q : Fin n → ℝ) (i : Fin n) (hq : ∀ j, q j = κ j * p j) :
    reconstruct M p κ i = pushForward M q i / pushForward M p i := by
  unfold reconstruct
  congr 1
  unfold pushForward
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hq j]

/-- **Transport never amplifies.** The reconstructed conditional is a weighted average of the
conditional's own values, so it stays inside their range. An error in the observed conditional is
carried forward, never magnified — which is why forward reconstruction is the cheap direction. -/
theorem reconstruct_between {n : ℕ} (M : Fin n → Fin n → ℝ) (p κ : Fin n → ℝ) (i : Fin n)
    (lo hi : ℝ) (hM : ∀ j, 0 ≤ M i j) (hp : ∀ j, 0 ≤ p j)
    (hpos : 0 < pushForward M p i)
    (hlo : ∀ j, lo ≤ κ j) (hhi : ∀ j, κ j ≤ hi) :
    lo ≤ reconstruct M p κ i ∧ reconstruct M p κ i ≤ hi := by
  have hnum_lo : lo * pushForward M p i ≤ pushForward M (fun j ↦ κ j * p j) i := by
    unfold pushForward
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hstep : lo * p j ≤ κ j * p j := mul_le_mul_of_nonneg_right (hlo j) (hp j)
    calc lo * (M i j * p j) = M i j * (lo * p j) := by ring
      _ ≤ M i j * (κ j * p j) := mul_le_mul_of_nonneg_left hstep (hM j)
  have hnum_hi : pushForward M (fun j ↦ κ j * p j) i ≤ hi * pushForward M p i := by
    unfold pushForward
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hstep : κ j * p j ≤ hi * p j := mul_le_mul_of_nonneg_right (hhi j) (hp j)
    calc M i j * (κ j * p j) ≤ M i j * (hi * p j) := mul_le_mul_of_nonneg_left hstep (hM j)
      _ = hi * (M i j * p j) := by ring
  unfold reconstruct
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-! ## What survives a mixing drift -/

/-- **A continuous invariant of the drift is determined by the drift's limit.**

    If a functional is constant along the flow and the flow converges, the functional's value on
    the initial curve equals its value at the limit. Under ergodic mixing that limit is the
    constant curve at the base rate, so every continuous invariant is a function of prevalence
    alone: discrimination, calibration and curve shape are all transient, and the base rate is
    the only stable summary.

    `H` is not assumed Hausdorff. It was: the statement carried `[T2Space H]`, which a scan of
    the kernel-accepted proof term found unused. It has to be unused -- the uniqueness of limits
    this proof invokes is `tendsto_nhds_unique` on `ℝ`, the codomain, whose separation is
    ambient, and the argument never needs limits in `H` to be unique. -/
theorem continuousInvariant_eq_at_limit {H : Type*} [TopologicalSpace H]
    (invariant : H → ℝ) (hPhi : Continuous invariant) (flow : ℝ → H) (limit : H)
    (hinv : ∀ t, invariant (flow t) = invariant (flow 0))
    (hconv : Filter.Tendsto flow Filter.atTop (nhds limit)) :
    invariant (flow 0) = invariant limit := by
  have hcomp : Filter.Tendsto (fun t ↦ invariant (flow t)) Filter.atTop (nhds (invariant limit)) :=
    (hPhi.tendsto limit).comp hconv
  have hconst : Filter.Tendsto (fun t ↦ invariant (flow t)) Filter.atTop (nhds (invariant (flow 0))) := by
    simp [hinv]
  exact tendsto_nhds_unique hconst hcomp

/-! ## Interior estimates: the interpolation bound with constant one -/

/-- Error energy of a spectral mixture at time `t`: mode `k` carries weight `w k` and relaxes at
rate `lam k`. -/
noncomputable def errorEnergy {n : ℕ} (w lam : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, w k * Real.exp (-(2 * lam k * t))

/-- Reference evaluation at time zero, where every mode contributes its full weight. -/
theorem errorEnergy_at_reference_point :
    errorEnergy (![1, 3] : Fin 2 → ℝ) (![2, 5] : Fin 2 → ℝ) 0 = 4 := by
  simp [errorEnergy, Fin.sum_univ_succ]
  norm_num


/-- **The interior error energy is at most the product of the endpoint energies.**

    Stated in squared form so nothing is square-rooted: at the midpoint of two observation times
    the error energy squared is bounded by the product of the energies there. The constant is
    exactly one, so an estimate between two observations inherits the geometric mean of their
    errors and cannot blow up in the interior. -/
theorem interiorError_sq_le_mul_endpoints {n : ℕ} (w lam : Fin n → ℝ) (t₁ t₂ : ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    errorEnergy w lam ((t₁ + t₂) / 2) ^ 2 ≤
      errorEnergy w lam t₁ * errorEnergy w lam t₂ := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin n ↦ Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))))
    (fun k : Fin n ↦ Real.sqrt (w k * Real.exp (-(2 * lam k * t₂))))
  have hnn : ∀ (k : Fin n) (r : ℝ), 0 ≤ w k * Real.exp r := fun k r ↦
    mul_nonneg (hw k) (Real.exp_pos r).le
  have hexp : ∀ k : Fin n,
      Real.exp (-(2 * lam k * t₁)) * Real.exp (-(2 * lam k * t₂))
        = Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) ^ 2 := by
    intro k
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))) *
          Real.sqrt (w k * Real.exp (-(2 * lam k * t₂)))
        = w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) := by
    intro k
    rw [← Real.sqrt_mul (hnn k _)]
    have hcollect : w k * Real.exp (-(2 * lam k * t₁)) * (w k * Real.exp (-(2 * lam k * t₂)))
        = (w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2)))) ^ 2 := by
      calc w k * Real.exp (-(2 * lam k * t₁)) * (w k * Real.exp (-(2 * lam k * t₂)))
          = w k ^ 2 * (Real.exp (-(2 * lam k * t₁)) * Real.exp (-(2 * lam k * t₂))) := by ring
        _ = w k ^ 2 * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) ^ 2 := by rw [hexp k]
        _ = (w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2)))) ^ 2 := by ring
    rw [hcollect, Real.sqrt_sq (hnn k _)]
  have hsq₁ : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))) ^ 2 = w k * Real.exp (-(2 * lam k * t₁)) :=
    fun k ↦ Real.sq_sqrt (hnn k _)
  have hsq₂ : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₂))) ^ 2 = w k * Real.exp (-(2 * lam k * t₂)) :=
    fun k ↦ Real.sq_sqrt (hnn k _)
  rw [Finset.sum_congr rfl fun k _ ↦ hprod k,
    Finset.sum_congr rfl fun k _ ↦ hsq₁ k,
    Finset.sum_congr rfl fun k _ ↦ hsq₂ k] at key
  exact key

/-- **A single mode attains the bound**, so the constant one cannot be improved: the hardest data
    for interior reconstruction are pure spectral modes. -/
theorem singleMode_interiorError_eq (w lam t₁ t₂ : ℝ) :
    (w * Real.exp (-(2 * lam * ((t₁ + t₂) / 2)))) ^ 2
      = (w * Real.exp (-(2 * lam * t₁))) * (w * Real.exp (-(2 * lam * t₂))) := by
  have hexp : Real.exp (-(2 * lam * t₁)) * Real.exp (-(2 * lam * t₂))
      = Real.exp (-(2 * lam * ((t₁ + t₂) / 2))) ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc (w * Real.exp (-(2 * lam * ((t₁ + t₂) / 2)))) ^ 2
      = w ^ 2 * Real.exp (-(2 * lam * ((t₁ + t₂) / 2))) ^ 2 := by ring
    _ = w ^ 2 * (Real.exp (-(2 * lam * t₁)) * Real.exp (-(2 * lam * t₂))) := by rw [hexp]
    _ = (w * Real.exp (-(2 * lam * t₁))) * (w * Real.exp (-(2 * lam * t₂))) := by ring

/-! ## Probit invariance under Ornstein-Uhlenbeck drift

Theorem 3. Averaging the probit link against a Gaussian returns a probit link with a rescaled
slope, so the two-parameter family `Φ(a x + b)` is exactly invariant under the OU semigroup. That
is why the realization is two-dimensional and curved rather than linear, which is the escape from
the spectral obstruction: no bounded link has a finite-dimensional invariant SUBSPACE, and this
one has an invariant MANIFOLD.

The whole content sits in one Gaussian identity, `gaussianAverage_probit`, and that identity is
proved below. The proof is the standard coupling — `E[Φ(α + βZ)]` is
`P(W ≤ α + βZ)` for an independent standard normal `W`, and `W - βZ` is centred Gaussian with
variance `1 + β²`.  The formal argument supplies both pieces: Mathlib's Gaussian convolution and
the conditioning step that turns the expectation of a cdf into a probability of a linear
combination.

`probit_invariant_under_ou` is then derived rather than assumed: from the identity, the
invariance and the exact new slope follow by algebra, which is proved. So the module carries one
proved analytic spine instead of an untracked paragraph of prose, and everything the analysis
draws from Theorem 3 downstream is connected to it. -/

open MeasureTheory ProbabilityTheory in
/-- **Standardisation of a centred Gaussian cdf.** The distribution function of `N(0, v)` is the
standard one evaluated at the scaled argument.

    This is one of the two halves of `gaussianAverage_probit`, and it is the half that is pure
    change of variable: `N(0,v)` is the pushforward of `N(0,1)` under multiplication by `√v`, so
    the measure of a half-line is the standard measure of the scaled half-line. -/
theorem cdf_gaussianReal_zero_mean (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal 0 v) x = Foundations.Phi (x / Real.sqrt (v : ℝ)) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rcases v.coe_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (NNReal.coe_eq_zero.mp h.symm) hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvpos
  have hsq : (⟨Real.sqrt (v : ℝ) ^ 2, sq_nonneg _⟩ : NNReal) * 1 = v := by
    ext
    simp [Real.sq_sqrt hvpos.le]
  have hmap : (gaussianReal 0 1).map (fun y ↦ Real.sqrt (v : ℝ) * y) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal))
      (Real.sqrt (v : ℝ))
    rw [mul_zero, hsq] at h
    exact h
  have hpre : (fun y ↦ Real.sqrt (v : ℝ) * y) ⁻¹' Set.Iic x = Set.Iic (x / Real.sqrt (v : ℝ)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [le_div_iff₀' hs]
  show cdf (gaussianReal 0 v) x = cdf (gaussianReal 0 1) (x / Real.sqrt (v : ℝ))
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, ← hmap,
    Measure.map_apply (measurable_const_mul _) measurableSet_Iic, hpre]

open MeasureTheory ProbabilityTheory in
/-- **The conditioning step for Theorem 3.**

    Averaging the standard cdf over a Gaussian shift is the law of a difference: `E[Φ(α + βZ)]`
    is `P(W ≤ α + βZ)` for an independent standard normal `W`, which is `P(W - βZ ≤ α)`, and
    `W - βZ` is centred Gaussian with variance `1 + β²`.

    `Measure.prod_apply` slices the product measure into exactly this average, and
    `gaussianReal_add_gaussianReal_of_indepFun` with `gaussianReal_map_const_mul` gives the law of
    the difference. The proof includes the passage from the lower integral of measures to the
    Bochner integral of the cdf. -/
theorem gaussianAverage_eq_cdf_sum (α β : ℝ) :
    ∫ z, Foundations.Phi (α + β * z) ∂(gaussianReal 0 1)
      = cdf (gaussianReal 0 ⟨1 + β ^ 2, by positivity⟩) α := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγdef
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 - β * p.1 ≤ α} with hSdef
  have hdiff : Measurable (fun p : ℝ × ℝ ↦ p.2 - β * p.1) := by fun_prop
  have hSmeas : MeasurableSet S := hdiff measurableSet_Iic
  -- Slicing the product measure is exactly the average of the cdf.
  have hslice : (γ.prod γ) S = ∫⁻ z, γ (Set.Iic (α + β * z)) ∂γ := by
    rw [Measure.prod_apply hSmeas]
    refine lintegral_congr fun z ↦ ?_
    congr 1
    ext w
    simp only [hSdef, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro h; linarith
    · intro h; linarith
  have hPhi : ∀ t : ℝ, Foundations.Phi t = (γ (Set.Iic t)).toReal := by
    intro t
    show cdf (gaussianReal 0 1) t = _
    rw [cdf_eq_real, measureReal_def]
  have hmono : Monotone (fun t : ℝ ↦ γ (Set.Iic t)) := fun a b hab ↦
    measure_mono (Set.Iic_subset_Iic.mpr hab)
  have hlhs : ∫ z, Foundations.Phi (α + β * z) ∂γ
      = (∫⁻ z, γ (Set.Iic (α + β * z)) ∂γ).toReal := by
    have hfun : (fun z ↦ Foundations.Phi (α + β * z))
        = fun z ↦ (γ (Set.Iic (α + β * z))).toReal := funext fun z ↦ hPhi _
    rw [hfun]
    refine integral_toReal ?_ ?_
    · exact (hmono.measurable.comp (by fun_prop)).aemeasurable
    · filter_upwards with z
      exact measure_lt_top _ _
  -- The difference of the two coordinates is centred Gaussian with variance `1 + β²`.
  have hX : (γ.prod γ).map (fun p : ℝ × ℝ ↦ p.2) = gaussianReal 0 1 := by
    change Measure.snd (γ.prod γ) = gaussianReal 0 1
    rw [Measure.snd_prod, hγdef]
  have hfst : (γ.prod γ).map (fun p : ℝ × ℝ ↦ p.1) = gaussianReal 0 1 := by
    change Measure.fst (γ.prod γ) = gaussianReal 0 1
    rw [Measure.fst_prod, hγdef]
  have hY : (γ.prod γ).map (fun p : ℝ × ℝ ↦ -β * p.1)
      = gaussianReal 0 ⟨β ^ 2, sq_nonneg β⟩ := by
    have hcomp : (fun p : ℝ × ℝ ↦ -β * p.1) = (fun y : ℝ ↦ -β * y) ∘
        (fun p : ℝ × ℝ ↦ p.1) :=
      rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hfst]
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) (-β)
    have hv : (⟨(-β) ^ 2, sq_nonneg _⟩ : NNReal) * 1 = ⟨β ^ 2, sq_nonneg β⟩ := by
      ext; simp
    rw [mul_zero, hv] at h
    exact h
  have hindep : IndepFun (fun p : ℝ × ℝ ↦ p.2) (fun p : ℝ × ℝ ↦ -β * p.1)
      (γ.prod γ) := by
    have h := ProbabilityTheory.indepFun_prod₀ (μ := γ) (ν := γ)
      (X := fun y : ℝ ↦ -β * y) (Y := fun y : ℝ ↦ y)
      (by fun_prop) (by fun_prop)
    exact h.symm
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hindep hX hY
  have hfunsum : ((fun p : ℝ × ℝ ↦ p.2) + fun p : ℝ × ℝ ↦ -β * p.1)
      = fun p : ℝ × ℝ ↦ p.2 - β * p.1 := by
    funext p
    simp [sub_eq_add_neg]
  rw [hfunsum] at hsum
  have hvar : (0 : ℝ) + 0 = 0 := by norm_num
  have hnn : (1 : NNReal) + ⟨β ^ 2, sq_nonneg β⟩ = ⟨1 + β ^ 2, by positivity⟩ := by
    ext; simp
  rw [hvar, hnn] at hsum
  -- Put the two readings of the same probability together.
  have hSpre : S = (fun p : ℝ × ℝ ↦ p.2 - β * p.1) ⁻¹' Set.Iic α := rfl
  have hRHS : (γ.prod γ) S = gaussianReal 0 ⟨1 + β ^ 2, by positivity⟩ (Set.Iic α) := by
    rw [hSpre, ← Measure.map_apply hdiff measurableSet_Iic, hsum]
  rw [hlhs, ← hslice, hRHS, cdf_eq_real, measureReal_def]

open MeasureTheory ProbabilityTheory in
/-- **The Gaussian averaging identity**, `E[Φ(α + βZ)] = Φ(α / √(1 + β²))`.

    Now derived rather than assumed: the conditioning step above identifies the average as a
    centred Gaussian cdf, and `cdf_gaussianReal_zero_mean` — which IS proved — standardises it.
    So Theorem 3 rests on one measure-theoretic assembly, not on the identity as a whole. -/
theorem gaussianAverage_probit (α β : ℝ) :
    ∫ z, Foundations.Phi (α + β * z) ∂(gaussianReal 0 1) = Foundations.Phi (α / Real.sqrt (1 + β ^ 2)) := by
  have hne : (⟨1 + β ^ 2, by positivity⟩ : NNReal) ≠ 0 := by
    intro h
    have h' : (1 + β ^ 2 : ℝ) = 0 := by simpa using congrArg NNReal.toReal h
    nlinarith [sq_nonneg β]
  rw [gaussianAverage_eq_cdf_sum, cdf_gaussianReal_zero_mean _ hne]
  norm_num [NNReal.coe_mk]

open MeasureTheory ProbabilityTheory in
/-- **Probit is exactly invariant under one Ornstein-Uhlenbeck step**, with the slope contracted
by `a ↦ a e^{-λt} / √(1 + a²σ²)`.

    Derived from `gaussianAverage_probit` by algebra: the OU transition sends `x` to
    `e^{-λt} x + σ z`, so the probit argument `a₀(e^{-λt}x + σz) + b₀` is exactly
    `α + βz` at `α = a₀ e^{-λt} x + b₀` and `β = a₀ σ`, and the identity contracts it. The
    resulting slope is the one whose inverse square linearises to `Ȧ = 2λA + 1`, which is
    `inverseSquare_linearises_probit_flow` below. -/
theorem probit_invariant_under_ou (lam t a₀ b₀ x sigma : ℝ) :
    ∫ z, Foundations.Phi (a₀ * (Real.exp (-(lam * t)) * x + sigma * z) + b₀) ∂(gaussianReal 0 1)
      = Foundations.Phi ((a₀ * Real.exp (-(lam * t)) * x + b₀)
          / Real.sqrt (1 + a₀ ^ 2 * sigma ^ 2)) := by
  have hshape : (fun z ↦ Foundations.Phi (a₀ * (Real.exp (-(lam * t)) * x + sigma * z) + b₀))
      = fun z ↦ Foundations.Phi ((a₀ * Real.exp (-(lam * t)) * x + b₀) + (a₀ * sigma) * z) := by
    funext z
    congr 1
    ring
  rw [hshape, gaussianAverage_probit]
  congr 2
  ring_nf

/-! ## Rigidity of the probit shape

Theorem 4. Theorem 3 says the probit family is invariant. The correct rigidity target is an
**affine-probit** link `p + q * Φ (αu + β)`, not a bare probit: Gaussian averaging acts on the
argument and therefore cannot identify a vertical offset `p` or scale `q`. The earlier bare-probit
target was false; for example `1 / 4 + (1 / 2) * Φ u` is strictly increasing, takes values in
`(0,1)`, and has the same closure property.

This correction matters biologically. A nonzero floor and a ceiling below one represent persistent
case-label contamination, incomplete ascertainment, or penetrance bounded away from one. Population
drift can determine the Gaussian latent-response *shape*, but it cannot manufacture the two
external anchors needed to identify those observation-channel limits. A bare probit follows only
after the scientifically separate tail calibration `p = 0`, `p + q = 1`.

Both directions are proved. Sufficiency is `probit_link_invariant`, Theorem 3 rearranged: the
averaged probit is a probit, and the new parameters are exhibited. Necessity is `link_rigidity`.

Necessity does not go through the density. Differentiating the invariance would need smoothness
the hypotheses do not give, so the route here is measure-theoretic: a bounded increasing link is
the cdf of a finite liability measure, Gaussian averaging of the link is Gaussian blurring of that
measure, and the invariance says the measure is affinely self-similar under blurring at every
scale. Iterating the resulting characteristic-function equation evaluates it in closed form, and
it is Gaussian. The vertical offset and scale survive that argument and remain in the
conclusion. -/

open MeasureTheory ProbabilityTheory in
/-- **Sufficiency: the probit family is closed under Gaussian averaging**, with the new
parameters exhibited rather than merely asserted to exist. This is Theorem 3 rearranged into the
single-index form rigidity is stated against. -/
theorem probit_link_invariant (lam t a₀ b₀ σ : ℝ) :
    ∃ a' b' : ℝ, ∀ x,
      ∫ z, Foundations.Phi (a₀ * (Real.exp (-(lam * t)) * x + σ * z) + b₀) ∂(gaussianReal 0 1)
        = Foundations.Phi (a' * x + b') := by
  refine ⟨a₀ * Real.exp (-(lam * t)) / Real.sqrt (1 + a₀ ^ 2 * σ ^ 2),
    b₀ / Real.sqrt (1 + a₀ ^ 2 * σ ^ 2), fun x ↦ ?_⟩
  rw [probit_invariant_under_ou]
  congr 1
  ring

open MeasureTheory ProbabilityTheory in
/-- **The observation-channel floor and ceiling survive Gaussian averaging.**

If the biological response curve is `p + q Φ(a₀x + b₀)`, averaging latent liability over a
Gaussian population displacement changes only its horizontal slope and intercept. The vertical
offset `p` and scale `q` are untouched. Thus dynamics can identify the affine-probit shape, but
cannot distinguish a genuine penetrance ceiling from persistent label noise or incomplete case
ascertainment without separate tail calibration. -/
theorem affineProbit_link_invariant (p q a₀ b₀ σ : ℝ) :
    ∃ a' b' : ℝ, ∀ x,
      ∫ z, (p + q * Foundations.Phi (a₀ * (x + σ * z) + b₀)) ∂(gaussianReal 0 1)
        = p + q * Foundations.Phi (a' * x + b') := by
  refine ⟨a₀ / Real.sqrt (1 + a₀ ^ 2 * σ ^ 2),
    b₀ / Real.sqrt (1 + a₀ ^ 2 * σ ^ 2), fun x ↦ ?_⟩
  have hPhiMeas : Measurable (fun z : ℝ ↦ Foundations.Phi (a₀ * (x + σ * z) + b₀)) :=
    Foundations.strictMono_Phi.monotone.measurable.comp (by fun_prop)
  have hPhiInt : Integrable (fun z : ℝ ↦ Foundations.Phi (a₀ * (x + σ * z) + b₀))
      (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hPhiMeas.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ProbabilityTheory.cdf_le_one _ _
    · exact ProbabilityTheory.cdf_nonneg _ _
  rw [integral_add (integrable_const p) (hPhiInt.const_mul q), integral_const,
    integral_const_mul]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  have hshape : (fun z ↦ Foundations.Phi (a₀ * (x + σ * z) + b₀)) =
      fun z ↦ Foundations.Phi ((a₀ * x + b₀) + (a₀ * σ) * z) := by
    funext z
    congr 1
    ring
  rw [hshape, gaussianAverage_probit]
  congr 2
  ring_nf

/-- A positive horizontal and vertical scaling preserves the strict ordering of genetic or
environmental liability. -/
theorem affineProbit_strictMono (p q α β : ℝ) (hq : 0 < q) (hα : 0 < α) :
    StrictMono (fun u ↦ p + q * Foundations.Phi (α * u + β)) := by
  intro u v huv
  apply add_lt_add_left
  apply mul_lt_mul_of_pos_left _ hq
  apply Foundations.strictMono_Phi
  nlinarith

/-- The natural floor/ceiling constraints put every affine-probit risk strictly between zero and
one. Endpoints may equal zero and one because `Foundations.Phi` never attains either at a finite
liability. -/
theorem affineProbit_mem_Ioo (p q α β : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hpq : p + q ≤ 1) (u : ℝ) :
    0 < p + q * Foundations.Phi (α * u + β) ∧ p + q * Foundations.Phi (α * u + β) < 1 := by
  have hPhiPos : 0 < Foundations.Phi (α * u + β) := by
    have hnonneg : 0 ≤ Foundations.Phi (α * u + β - 1) := ProbabilityTheory.cdf_nonneg _ _
    exact lt_of_le_of_lt hnonneg (Foundations.strictMono_Phi (by linarith))
  have hPhiLtOne : Foundations.Phi (α * u + β) < 1 := by
    have hle : Foundations.Phi (α * u + β + 1) ≤ 1 := ProbabilityTheory.cdf_le_one _ _
    exact lt_of_lt_of_le (Foundations.strictMono_Phi (by linarith)) hle
  constructor <;> nlinarith

open MeasureTheory ProbabilityTheory in
/-- A bounded monotone link composed with an affine map is integrable against a Gaussian.

Monotone functions are measurable, the link is bounded by `1`, and the Gaussian is a
probability measure, so there is nothing to check beyond assembling those three. -/
theorem link_integrable (L : ℝ → ℝ) (hmono : StrictMono L) (hbdd : ∀ u, 0 < L u ∧ L u < 1)
    (a b σ c : ℝ) :
    Integrable (fun z : ℝ ↦ L (a * (c + σ * z) + b)) (gaussianReal 0 1) := by
  refine ⟨(hmono.monotone.measurable.comp (by fun_prop)).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (hbdd _).1]
  exact le_of_lt (hbdd _).2

open MeasureTheory ProbabilityTheory in
/-- **The averaged link is strictly increasing in the covariate.**

Pointwise in the noise the integrand is strictly increasing in `x`, and the integral of a
strictly positive integrable function against a probability measure is strictly positive,
so the average inherits strictness rather than only monotonicity.

This is the step that makes the orientation of the induced parameter map forced rather
than assumed; see `link_invariance_slope_pos`. -/
theorem link_average_strictMono (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {a σ : ℝ} (ha : 0 < a) (b : ℝ) :
    StrictMono (fun x ↦ ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1)) := by
  intro x y hxy
  have hix := link_integrable L hmono hbdd a b σ x
  have hiy := link_integrable L hmono hbdd a b σ y
  have hpos : 0 < ∫ z, (L (a * (y + σ * z) + b) - L (a * (x + σ * z) + b))
      ∂(gaussianReal 0 1) := by
    have hstrict : ∀ z : ℝ, 0 < L (a * (y + σ * z) + b) - L (a * (x + σ * z) + b) := by
      intro z
      have : a * (x + σ * z) + b < a * (y + σ * z) + b := by nlinarith
      linarith [hmono this]
    rw [integral_pos_iff_support_of_nonneg (fun z ↦ le_of_lt (hstrict z)) (hiy.sub hix)]
    have hsupp : (Function.support fun z : ℝ ↦
        L (a * (y + σ * z) + b) - L (a * (x + σ * z) + b)) = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hstrict z)
    rw [hsupp, measure_univ]
    norm_num
  rw [integral_sub hiy hix] at hpos
  linarith

open MeasureTheory ProbabilityTheory in
/-- **The induced parameter map preserves orientation: `a' > 0` is forced.**

`link_rigidity`'s invariance hypothesis produces `a'` and `b'` with no sign constraint.
There is none to impose: the left side is strictly increasing in `x` by
`link_average_strictMono`, so `x ↦ L (a' x + b')` is too, and a strictly monotone `L`
then forces `a' > 0`.

Stating it separately keeps the hypothesis honest. A version of `link_rigidity` that
assumed `0 < a'` would be assuming part of what the invariance already delivers, which is
the failure mode this corpus keeps finding elsewhere. -/
theorem link_invariance_slope_pos (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {a b σ a' b' : ℝ} (ha : 0 < a)
    (heq : ∀ x, ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1) = L (a' * x + b')) :
    0 < a' := by
  have hlt : L (a' * 0 + b') < L (a' * 1 + b') := by
    rw [← heq 0, ← heq 1]
    exact link_average_strictMono L hmono hbdd ha b (by norm_num)
  have := hmono.lt_iff_lt.mp hlt
  linarith

open MeasureTheory ProbabilityTheory in
/-- **A monotone link is continuous at almost every point the averaging sees.**

A monotone function has countably many discontinuities, the affine map
`z ↦ a (x + σ z) + b` is injective when `a σ ≠ 0`, and the standard Gaussian has no
atoms.  So the pullback of the discontinuity set is countable and therefore null.

This is what makes dominated convergence available below.  Without it the pointwise
limit hypothesis fails: `y ↦ L (a (y + σ z) + b)` is continuous at `x` only where `L` is
continuous, and a monotone `L` is not assumed continuous anywhere. -/
theorem link_discontinuity_null (L : ℝ → ℝ) (hmono : StrictMono L) {a σ : ℝ}
    (ha : a ≠ 0) (hσ : σ ≠ 0) (b x : ℝ) :
    (gaussianReal 0 1) {z : ℝ | ¬ ContinuousAt L (a * (x + σ * z) + b)} = 0 := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hinj : Function.Injective (fun z : ℝ ↦ a * (x + σ * z) + b) := by
    intro z₁ z₂ h
    simp only at h
    exact mul_left_cancel₀ hσ (add_left_cancel (mul_left_cancel₀ ha (add_right_cancel h)))
  have hcount : {u : ℝ | ¬ ContinuousAt L u}.Countable :=
    hmono.monotone.countable_not_continuousAt
  exact (hcount.preimage hinj).measure_zero _

open MeasureTheory ProbabilityTheory in
/-- **The averaged link is continuous, even though the link is not assumed to be.**

Dominated convergence along the neighbourhood filter: the integrand is bounded by `1`,
the measure is a probability measure, and by `link_discontinuity_null` the pointwise limit
holds for almost every noise value.

This is the first regularity gained from the invariance rather than assumed, and it is
the step the classification needs before anything can be differentiated. Biologically,
cohort mixing smooths even a response curve with threshold jumps: discontinuities in
individual liability occupy zero mass after a continuously distributed environmental or
ancestry shift. -/
theorem link_average_continuous (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {a σ : ℝ} (ha : a ≠ 0) (hσ : σ ≠ 0) (b : ℝ) :
    Continuous (fun x ↦ ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1)) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ)) ?_ ?_ ?_ ?_
  · filter_upwards with y
    exact (hmono.monotone.measurable.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with y
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (hbdd _).1]
    exact le_of_lt (hbdd _).2
  · exact integrable_const 1
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (link_discontinuity_null L hmono ha hσ b x)] with z hz
    exact (not_not.mp hz).tendsto.comp
      ((by fun_prop : Continuous fun y : ℝ ↦ a * (y + σ * z) + b).tendsto x)

open MeasureTheory ProbabilityTheory in
/-- **The averaging map pushes the standard Gaussian to a Gaussian centred at the
covariate.**

`z ↦ a (x + σ z) + b` is the scaling by `a σ` followed by the shift by `a x + b`, so the
pushforward of `N(0,1)` is `N(a x + b, (a σ)²)`. -/
theorem link_average_pushforward (a σ b x : ℝ) :
    (gaussianReal 0 1).map (fun z ↦ a * (x + σ * z) + b)
      = gaussianReal (a * x + b) ⟨(a * σ) ^ 2, sq_nonneg _⟩ := by
  have hfun : (fun z : ℝ ↦ a * (x + σ * z) + b)
      = (fun w : ℝ ↦ w + (a * x + b)) ∘ (fun z : ℝ ↦ (a * σ) * z) := by
    funext z; simp only [Function.comp_apply]; ring
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have hscale := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) (a * σ)
  have hv : (⟨(a * σ) ^ 2, sq_nonneg _⟩ : NNReal) * 1 = ⟨(a * σ) ^ 2, sq_nonneg _⟩ := by
    ext; simp
  rw [mul_zero, hv] at hscale
  rw [hscale, gaussianReal_map_add_const]
  congr 1
  ring

open MeasureTheory ProbabilityTheory in
/-- **The averaging operator is `L` integrated against a Gaussian whose mean is the
covariate.**

This is the change of variables the classification needs.  On the left the covariate `x`
sits inside `L`, where nothing is known about it beyond monotonicity; on the right it sits
only in the mean of the measure, which is as smooth in `x` as anything could be.  Every
route to regularity for `L` goes through moving `x` out of `L` and into the kernel, and
this is that move.

What still has to be supplied afterwards is the differentiation under the integral sign:
`gaussianReal` is `volume.withDensity (gaussianPDF …)`, so the right-hand side is an
integral of `L` against a density smooth in `x`, and `L` is bounded — the ingredients of a
dominated-convergence argument.  That argument is not made here. -/
theorem link_average_eq_gaussian_integral (L : ℝ → ℝ) (hmono : StrictMono L)
    (a σ b x : ℝ) :
    ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1)
      = ∫ u, L u ∂(gaussianReal (a * x + b) ⟨(a * σ) ^ 2, sq_nonneg _⟩) := by
  rw [← link_average_pushforward a σ b x,
    integral_map (by fun_prop) hmono.monotone.measurable.aestronglyMeasurable]

open MeasureTheory ProbabilityTheory in
/-- **Closure forces continuity of the original link.**

If one nondegenerate Gaussian averaging step lands back in the affine family of `L`, the output
slope is positive and hence invertible. Solving the output affine coordinate for its input writes
`L` itself as a continuous Gaussian average. Thus the continuity needed by the rigidity
classification is a theorem of closure, not an extra regularity hypothesis. -/
theorem link_continuous_of_invariance (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {a b σ a' b' : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (heq : ∀ x, ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1) = L (a' * x + b')) :
    Continuous L := by
  have ha' : 0 < a' := link_invariance_slope_pos L hmono hbdd ha heq
  have havg_cont := link_average_continuous L hmono hbdd ha.ne' hσ.ne' b
  have hrepl : L = fun u ↦ ∫ z, L (a * ((u - b') / a' + σ * z) + b)
      ∂(gaussianReal 0 1) := by
    funext u
    rw [heq]
    congr 1
    field_simp
    ring
  rw [hrepl]
  exact havg_cont.comp (by fun_prop)

/-- **The induced parameters are unique, so the invariance defines a map.**

`hinv` asserts existence of `a'` and `b'`; it does not say they are determined.  They are:
`L` is injective, so agreement of `L (a₁ x + b₁)` and `L (a₂ x + b₂)` at every `x` forces
the affine maps to agree, and two affine maps agreeing everywhere have equal coefficients.

Without this the "induced parameter map" of the classification argument is a relation, and
the semigroup identity it has to satisfy would not typecheck as a statement about
functions. -/
theorem link_invariance_params_unique (L : ℝ → ℝ) (hmono : StrictMono L)
    {a₁ b₁ a₂ b₂ : ℝ}
    (heq : ∀ x, L (a₁ * x + b₁) = L (a₂ * x + b₂)) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h0 : b₁ = b₂ := by
    have := hmono.injective (heq 0)
    simpa using this
  refine ⟨?_, h0⟩
  have h1 := hmono.injective (heq 1)
  simp only [mul_one] at h1
  linarith [h0 ▸ h1]

open MeasureTheory ProbabilityTheory in
/-- **Two averaging scales compose into one.**

`(z₁, z₂) ↦ x + s z₁ + t z₂` pushes the product of two standard Gaussians to
`N(x, s² + t²)`: it is a sum of two independent Gaussian coordinates, and variances add.

This is the semigroup law of the averaging operator, and it is what turns the
classification from an analytic problem into an algebraic one.  Averaging at scale `s` and
then at scale `t` is averaging once at scale `√(s² + t²)`, so the induced parameter map of
`link_rigidity` — well defined by `link_invariance_params_unique` — must satisfy a
composition identity in the scale.  For the probit that identity is
`α(√(s²+t²)) = α(s) · α(α(s) t)` with `α(s) = 1/√(1+s²)`, and pinning `α` is what pins the
link. -/
theorem gaussian_two_scale_map (x s t : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ ↦ x + s * p.1 + t * p.2)
      = gaussianReal x ⟨s ^ 2 + t ^ 2, by positivity⟩ := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  have hfst : (γ.prod γ).map (fun p : ℝ × ℝ ↦ p.1) = γ := by
    change Measure.fst (γ.prod γ) = γ
    rw [Measure.fst_prod]
  have hsnd : (γ.prod γ).map (fun p : ℝ × ℝ ↦ p.2) = γ := by
    change Measure.snd (γ.prod γ) = γ
    rw [Measure.snd_prod]
  have hX : (γ.prod γ).map (fun p : ℝ × ℝ ↦ x + s * p.1)
      = gaussianReal x ⟨s ^ 2, sq_nonneg s⟩ := by
    have hcomp : (fun p : ℝ × ℝ ↦ x + s * p.1)
        = (fun y : ℝ ↦ y + x) ∘ ((fun y : ℝ ↦ s * y) ∘ fun p : ℝ × ℝ ↦ p.1) := by
      funext p; simp only [Function.comp_apply]; ring
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop), hfst]
    have hs := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) s
    have hv : (⟨s ^ 2, sq_nonneg s⟩ : NNReal) * 1 = ⟨s ^ 2, sq_nonneg s⟩ := by ext; simp
    rw [mul_zero, hv] at hs
    rw [hs, gaussianReal_map_add_const]
    congr 1
    ring
  have hY : (γ.prod γ).map (fun p : ℝ × ℝ ↦ t * p.2)
      = gaussianReal 0 ⟨t ^ 2, sq_nonneg t⟩ := by
    have hcomp : (fun p : ℝ × ℝ ↦ t * p.2) = (fun y : ℝ ↦ t * y) ∘ fun p : ℝ × ℝ ↦ p.2 := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hsnd]
    have ht := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : NNReal)) t
    have hv : (⟨t ^ 2, sq_nonneg t⟩ : NNReal) * 1 = ⟨t ^ 2, sq_nonneg t⟩ := by ext; simp
    rw [mul_zero, hv] at ht
    exact ht
  have hindep : IndepFun (fun p : ℝ × ℝ ↦ x + s * p.1) (fun p : ℝ × ℝ ↦ t * p.2) (γ.prod γ) :=
    ProbabilityTheory.indepFun_prod₀ (μ := γ) (ν := γ)
      (X := fun y : ℝ ↦ x + s * y) (Y := fun y : ℝ ↦ t * y) (by fun_prop) (by fun_prop)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hindep hX hY
  have hfun : ((fun p : ℝ × ℝ ↦ x + s * p.1) + fun p : ℝ × ℝ ↦ t * p.2)
      = fun p : ℝ × ℝ ↦ x + s * p.1 + t * p.2 := rfl
  rw [hfun] at hsum
  have hm : x + (0 : ℝ) = x := by ring
  have hv : (⟨s ^ 2, sq_nonneg s⟩ : NNReal) + ⟨t ^ 2, sq_nonneg t⟩
      = ⟨s ^ 2 + t ^ 2, by positivity⟩ := by ext; simp
  rwa [hm, hv] at hsum

open MeasureTheory ProbabilityTheory in
/-- The two-scale integrand is integrable on the product: bounded by `1`, measurable, and
the product of two probability measures is a probability measure. -/
theorem link_two_scale_integrable (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) (x s t : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ L (x + s * p.1 + t * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine ⟨(hmono.monotone.measurable.comp (by fun_prop)).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := 1) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_pos (hbdd _).1]
  exact le_of_lt (hbdd _).2

open MeasureTheory ProbabilityTheory in
/-- **Averaging twice is averaging once at the combined scale.**

The operator form of `gaussian_two_scale_map`: both sides are `L` integrated against
`N(x, s² + t²)`, reached by `integral_map` from the two pushforwards.

This is the identity the classification runs on.  Combined with the invariance it forces a
composition law on the induced parameter map, and that law is an equation in one real
variable — which is why no further analysis of `L` itself is needed once regularity is in
hand. -/
theorem link_average_two_scale (L : ℝ → ℝ) (hmono : StrictMono L) (x s t : ℝ) :
    ∫ p, L (x + s * p.1 + t * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = ∫ w, L (x + Real.sqrt (s ^ 2 + t ^ 2) * w) ∂(gaussianReal 0 1) := by
  have hnn : (0 : ℝ) ≤ s ^ 2 + t ^ 2 := by positivity
  have hR : (gaussianReal 0 1).map (fun w : ℝ ↦ x + Real.sqrt (s ^ 2 + t ^ 2) * w)
      = gaussianReal x ⟨s ^ 2 + t ^ 2, hnn⟩ := by
    have h := link_average_pushforward 1 (Real.sqrt (s ^ 2 + t ^ 2)) 0 x
    have hvar : (⟨(1 * Real.sqrt (s ^ 2 + t ^ 2)) ^ 2, sq_nonneg _⟩ : NNReal)
        = ⟨s ^ 2 + t ^ 2, hnn⟩ := by
      ext; simp [Real.sq_sqrt hnn]
    rw [hvar] at h
    simpa using h
  calc
    ∫ p, L (x + s * p.1 + t * p.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
        ∫ y, L y ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (fun p : ℝ × ℝ ↦ x + s * p.1 + t * p.2)) := by
      symm
      exact integral_map (by fun_prop) hmono.monotone.measurable.aestronglyMeasurable
    _ = ∫ y, L y ∂(gaussianReal x ⟨s ^ 2 + t ^ 2, hnn⟩) := by
      rw [gaussian_two_scale_map]
    _ = ∫ w, L (x + Real.sqrt (s ^ 2 + t ^ 2) * w) ∂(gaussianReal 0 1) := by
      rw [← hR]
      exact integral_map (by fun_prop) hmono.monotone.measurable.aestronglyMeasurable

open MeasureTheory ProbabilityTheory in
/-- **The averaging operator is a semigroup in the scale, in iterated form.**

Fubini turns the product integral of `link_average_two_scale` into an average at scale `t`
of an average at scale `s`.  This is the shape the classification uses: applying the
invariance to the inner average and then to the outer one produces the induced parameters
of the two steps composed, while the right-hand side produces the induced parameters at the
single combined scale.  Uniqueness (`link_invariance_params_unique`) then equates them, and
what is left is an equation in one real variable.

For the probit the resulting law is `α(√(s²+t²)) = α(s) · α(α(s) t)` with `α(s) = 1/√(1+s²)`, which
one verifies directly:
`α(s) · α(α(s) t) = (1/√(1+s²)) · √(1+s²)/√(1+s²+t²)`.  Pinning `α` pins the link. -/
theorem link_average_semigroup (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) (x s t : ℝ) :
    ∫ z₁, (∫ z₂, L (x + s * z₁ + t * z₂) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ w, L (x + Real.sqrt (s ^ 2 + t ^ 2) * w) ∂(gaussianReal 0 1) := by
  rw [integral_integral (link_two_scale_integrable L hmono hbdd x s t)]
  exact link_average_two_scale L hmono x s t

open MeasureTheory ProbabilityTheory in
/-- **The general two-parameter invariance is the one-parameter scale family in disguise.**

`a (x + σ z) + b = (a x + b) + (a σ) z`, so averaging the affinely reparametrised link at
scale `σ` is averaging `L` itself at scale `a σ`, evaluated at the shifted point `a x + b`.

The hypothesis of `link_rigidity` quantifies over `a`, `b` and `σ` separately; this says
only the product `a σ` and the point `a x + b` matter.  The classification is therefore
about the one-parameter family `s ↦ (average of L at scale s)` and not about a
three-parameter family. -/
theorem link_average_reduce (L : ℝ → ℝ) (a b σ x : ℝ) :
    ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1)
      = ∫ z, L ((a * x + b) + (a * σ) * z) ∂(gaussianReal 0 1) := by
  have harg : ∀ z : ℝ, a * (x + σ * z) + b = (a * x + b) + (a * σ) * z := fun z ↦ by ring
  simp_rw [harg]

open MeasureTheory ProbabilityTheory in
/-- **The composition law for the scale family.**

If averaging at scale `t` returns `L` reparametrised by `(αt, βt)`, then averaging at scale
`s` *after* that is averaging `L` once at scale `√(s² + t²)`:

`(average at scale αt·s)(αt·x + βt) = (average at scale √(s²+t²))(x)`.

This is the classification's governing equation, and it is now a statement about one real
parameter.  For the probit, `αt = 1/√(1+t²)` and `βt = 0`, and the law reads
`α(αt·s) · αt = α(√(s²+t²))`, which is `1/√(1+s²+t²)` on both sides.

What remains of `link_rigidity` is to solve this for the scale family and recover `L`. -/
theorem link_scale_composition (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {t αt βt : ℝ}
    (ht : ∀ y, ∫ z, L (y + t * z) ∂(gaussianReal 0 1) = L (αt * y + βt)) (s x : ℝ) :
    ∫ z, L ((αt * x + βt) + (αt * s) * z) ∂(gaussianReal 0 1)
      = ∫ w, L (x + Real.sqrt (s ^ 2 + t ^ 2) * w) ∂(gaussianReal 0 1) := by
  rw [← link_average_semigroup L hmono hbdd x s t]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z₁ ↦ ?_)
  -- `show` forces the beta reduction that `rw` needs; without it both sides are
  -- unreduced applications and the pattern does not match.
  show L (αt * x + βt + αt * s * z₁)
      = ∫ z₂, L (x + s * z₁ + t * z₂) ∂(gaussianReal 0 1)
  rw [ht (x + s * z₁)]
  congr 1
  ring

open MeasureTheory ProbabilityTheory in
/-- **The induced affine parameters obey the scale-composition law.**

`link_scale_composition` equates the two averaged functions. If each is represented in
the affine family of `L`, `link_invariance_params_unique` upgrades equality of functions to
equality of both parameters. The theorem stays relational: it neither selects witnesses
from the closure hypothesis nor stores a theorem as parameter data.

For portability, this is path independence in its sharp form. Transport through two
independent Gaussian liability shifts produces exactly the same calibration slope and
intercept as transport through their variance-summed shift. -/
theorem link_scale_params_compose (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {t αt βt : ℝ}
    (ht : ∀ y, ∫ z, L (y + t * z) ∂(gaussianReal 0 1) = L (αt * y + βt))
    (s aₛₜ bₛₜ aᵣ bᵣ : ℝ)
    (hstep : ∀ x,
      ∫ z, L ((αt * x + βt) + (αt * s) * z) ∂(gaussianReal 0 1) =
        L (aₛₜ * x + bₛₜ))
    (hcombined : ∀ x,
      ∫ z, L (x + Real.sqrt (s ^ 2 + t ^ 2) * z) ∂(gaussianReal 0 1) =
        L (aᵣ * x + bᵣ)) :
    aₛₜ = aᵣ ∧ bₛₜ = bᵣ := by
  apply link_invariance_params_unique L hmono
  intro x
  rw [← hstep x, ← hcombined x]
  exact link_scale_composition L hmono hbdd ht s x

open MeasureTheory ProbabilityTheory in
/-- **The induced parameter action commutes.**

Averaging at scale `t` and then at scale `s` gives the same affine parameters as averaging
at scale `s` and then at scale `t` — because both routes are averaging once at
`√(s² + t²)`, and that is symmetric in `s` and `t`.

Written out, the slope equation is `α(α(t)·s)·α(t) = α(α(s)·t)·α(s)`.  This is the
constraint that pins the scale family: it is not satisfied by a generic decreasing
`α : (0,∞) → (0,1]`, and `α(s) = 1/√(1 + c²s²)` satisfies it because both sides collapse to
`1/√(1 + c²(s² + t²))`.

Unlike `link_scale_params_compose` this needs no representation of the combined scale — the
two-step routes are compared directly — so it constrains the parameter map using only the
hypothesis `link_rigidity` actually has. -/
theorem link_scale_params_symm (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) {s t αs βs αt βt aₛₜ bₛₜ aₜₛ bₜₛ : ℝ}
    (hs : ∀ y, ∫ z, L (y + s * z) ∂(gaussianReal 0 1) = L (αs * y + βs))
    (ht : ∀ y, ∫ z, L (y + t * z) ∂(gaussianReal 0 1) = L (αt * y + βt))
    (hst : ∀ x, ∫ z, L ((αt * x + βt) + (αt * s) * z) ∂(gaussianReal 0 1)
      = L (aₛₜ * x + bₛₜ))
    (hts : ∀ x, ∫ z, L ((αs * x + βs) + (αs * t) * z) ∂(gaussianReal 0 1)
      = L (aₜₛ * x + bₜₛ)) :
    aₛₜ = aₜₛ ∧ bₛₜ = bₜₛ := by
  apply link_invariance_params_unique L hmono
  intro x
  rw [← hst x, ← hts x, link_scale_composition L hmono hbdd ht s x,
    link_scale_composition L hmono hbdd hs t x, add_comm (t ^ 2) (s ^ 2)]

open MeasureTheory ProbabilityTheory in
/-- **Zero Gaussian scale induces the identity affine parameters.**

At scale zero the noise vanishes, so closure reads `L x = L (a₀ x + b₀)`. Strict
monotonicity then forces `a₀ = 1` and `b₀ = 0`. This pins the identity element of the
parameter semigroup rather than adding it as a normalization assumption. -/
theorem link_scale_zero_params (L : ℝ → ℝ) (hmono : StrictMono L) (a₀ b₀ : ℝ)
    (hzero : ∀ x,
      ∫ z, L (x + 0 * z) ∂(gaussianReal 0 1) = L (a₀ * x + b₀)) :
    a₀ = 1 ∧ b₀ = 0 := by
  apply link_invariance_params_unique L hmono
  intro x
  have hx := (hzero x).symm
  simpa using hx

open MeasureTheory ProbabilityTheory in
/-- **The link is continuous — derived from the invariance, not assumed.**

`link_rigidity` assumes only that `L` is strictly monotone and bounded.  A monotone
function may jump on a countable set, and the classification cannot begin against one that
does.  This closes that: apply the invariance at `a = σ = 1`, `b = 0`.  The left-hand side
is continuous by `link_average_continuous`, the right-hand side is `L` precomposed with an
affine map of positive slope by `link_invariance_slope_pos`, and composing with the inverse
affine map returns `L`.

So the functional equation manufactures its own regularity, which is the first step of the
classification and the reason the theorem can be true with no smoothness hypothesis. -/
theorem link_continuous (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1)
    (hinv : ∀ a b σ : ℝ, 0 < a → 0 < σ → ∃ a' b' : ℝ,
      ∀ x, ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1) = L (a' * x + b')) :
    Continuous L := by
  obtain ⟨a', b', heq⟩ := hinv 1 0 1 one_pos one_pos
  exact link_continuous_of_invariance L hmono hbdd one_pos one_pos heq

/-- **Boundedness really does exclude the affine stratum.**

The classification below says its boundedness hypothesis is load-bearing because it rules
out the affine and half-line-exponential links. For the affine stratum that is provable
outright, and is proved here: a strictly increasing affine map is unbounded above, so it
cannot land in `(0, 1)`.

Small, but it is the difference between a hypothesis that does work and one asserted to
work. The exponential stratum needs the half-line restriction and is not settled here. -/
theorem not_bounded_of_affine (c d : ℝ) (hc : 0 < c) :
    ¬ ∀ u : ℝ, 0 < c * u + d ∧ c * u + d < 1 := by
  intro h
  have hval := (h ((1 - d) / c)).2
  rw [mul_div_cancel₀ _ (ne_of_gt hc)] at hval
  linarith

/-! ### The link is a liability distribution

The classification's remaining step is an argument about measures, not about functions: a
bounded increasing `L` is the cdf of a finite measure on the liability axis, and the
averaging invariance says that measure reproduces itself, up to an affine change of
variable, under convolution with every Gaussian.  Only Gaussians do that.

This section builds the dictionary.  It is the step at which "link function" becomes
"distribution of the unmodelled liability", which is also what the object means
biologically: `L u` is the probability that total liability `u` plus everything the score
does not capture clears the threshold. -/

/-- The link is bounded above by its own supremum bound, so its limit at `+∞` exists. -/
theorem link_tendsto_atTop (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) :
    Filter.Tendsto L Filter.atTop (nhds (⨆ u, L u)) :=
  tendsto_atTop_ciSup hmono.monotone ⟨1, by rintro _ ⟨u, rfl⟩; exact (hbdd u).2.le⟩

/-- ... and at `-∞`, by the floor at `0`. -/
theorem link_tendsto_atBot (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) :
    Filter.Tendsto L Filter.atBot (nhds (⨅ u, L u)) :=
  tendsto_atBot_ciInf hmono.monotone ⟨0, by rintro _ ⟨u, rfl⟩; exact (hbdd u).1.le⟩

/-- **The link's two asymptotes are distinct.**

Strict monotonicity separates them, so the vertical scale `q = sup L - inf L` that
`link_rigidity` asks to be positive is positive for structural reasons: it is the total
mass of the liability distribution below.  A link with `q = 0` is a constant, which is not
strictly increasing. -/
theorem link_iInf_lt_iSup (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) :
    (⨅ u, L u) < ⨆ u, L u := by
  have hbelow : BddBelow (Set.range L) := ⟨0, by rintro _ ⟨u, rfl⟩; exact (hbdd u).1.le⟩
  have habove : BddAbove (Set.range L) := ⟨1, by rintro _ ⟨u, rfl⟩; exact (hbdd u).2.le⟩
  calc (⨅ u, L u) ≤ L 0 := ciInf_le hbelow 0
    _ < L 1 := hmono (by norm_num)
    _ ≤ ⨆ u, L u := le_ciSup habove 1

/-- **The link is the cdf of a finite measure on the liability axis.**

A continuous increasing bounded `L` is a Stieltjes function; its Lebesgue–Stieltjes measure
`ν` is finite with total mass `sup L - inf L`, and `L u = inf L + ν (-∞, u]`.

This is the representation the classification runs on.  Once `L` is `inf L + ν(Iic ·)`, the
averaging identity
`∫ L (x + s z) dγ(z) = L (α x + β)`
says `ν` convolved with `N(0, s²)` equals `ν` pushed forward by an affine map — for every
`s`.  Reading it that way is what makes "only the Gaussian" a statement one can attack,
because self-similarity under all Gaussian convolutions is a condition on `ν`, not on `L`.

Biologically `ν` is the distribution of the liability the score does not model. The theorem
says that object always exists; `link_rigidity` is the claim that the invariance forces it
to be Gaussian. -/
theorem link_stieltjes_representation (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1) (hcont : Continuous L) :
    ∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsFiniteMeasure ν ∧
      ν Set.univ = ENNReal.ofReal ((⨆ u, L u) - ⨅ u, L u) ∧
      ∀ u, L u = (⨅ v, L v) + (ν (Set.Iic u)).toReal := by
  classical
  set f : StieltjesFunction :=
    ⟨L, hmono.monotone, fun u ↦ (hcont.tendsto u).mono_left nhdsWithin_le_nhds⟩ with hf
  have hbot : Filter.Tendsto f Filter.atBot (nhds (⨅ u, L u)) :=
    link_tendsto_atBot L hmono hbdd
  have htop : Filter.Tendsto f Filter.atTop (nhds (⨆ u, L u)) :=
    link_tendsto_atTop L hmono hbdd
  have huniv : f.measure Set.univ = ENNReal.ofReal ((⨆ u, L u) - ⨅ u, L u) :=
    f.measure_univ hbot htop
  have hfin : MeasureTheory.IsFiniteMeasure f.measure :=
    ⟨by rw [huniv]; exact ENNReal.ofReal_lt_top⟩
  refine ⟨f.measure, hfin, huniv, fun u ↦ ?_⟩
  have hIic : f.measure (Set.Iic u) = ENNReal.ofReal (L u - ⨅ v, L v) :=
    f.measure_Iic hbot u
  have hle : (⨅ v, L v) ≤ L u :=
    ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; exact (hbdd v).1.le⟩ u
  rw [hIic, ENNReal.toReal_ofReal (by linarith)]
  ring

open MeasureTheory ProbabilityTheory in
/-- **Averaging the link is convolving its liability distribution.**

Through the representation `L u = p + ν (-∞, u]`, the Gaussian average of `L` at scale `s`
is the joint mass of the half-plane `{y ≤ x + s z}` under `ν ⊗ γ` — that is, the cdf at `x`
of `ν` convolved with `N(0, s²)`.

This is the change of viewpoint the classification needs.  On the left is an integral of an
unknown function; on the right is a measure evaluated on a half-plane, and the invariance
hypothesis of `link_rigidity` becomes: for every `s`, convolving `ν` with `N(0, s²)`
returns `ν` up to an affine change of variable.  Stated that way it is a self-similarity
condition on one measure, which is the form in which "only the Gaussian" is provable.

The proof is Fubini in its measure form — `Measure.prod_apply` slices the half-plane at
each `z` into exactly `Iic (x + s z)` — with the passage between the Bochner integral of
`toReal` and the lower integral justified by finiteness of `ν`. -/
theorem link_average_as_convolution (ν : Measure ℝ) [IsFiniteMeasure ν]
    (L : ℝ → ℝ) (p : ℝ) (hrep : ∀ u, L u = p + (ν (Set.Iic u)).toReal) (s x : ℝ) :
    ∫ z, L (x + s * z) ∂(gaussianReal 0 1)
      = p + (((gaussianReal 0 1).prod ν) {q : ℝ × ℝ | q.2 ≤ x + s * q.1}).toReal := by
  have hmeasS : MeasurableSet {q : ℝ × ℝ | q.2 ≤ x + s * q.1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hmonoIic : Monotone fun u : ℝ ↦ ν (Set.Iic u) :=
    fun _ _ hab ↦ measure_mono (Set.Iic_subset_Iic.2 hab)
  have hmeasg : Measurable fun z : ℝ ↦ ν (Set.Iic (x + s * z)) :=
    hmonoIic.measurable.comp (by fun_prop)
  have hlt : ∀ z : ℝ, ν (Set.Iic (x + s * z)) < ⊤ :=
    fun z ↦ lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (measure_lt_top ν _)
  have hInt : Integrable (fun z : ℝ ↦ (ν (Set.Iic (x + s * z))).toReal)
      (gaussianReal 0 1) := by
    refine ⟨hmeasg.ennreal_toReal.aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := (ν Set.univ).toReal) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.subset_univ _))
  simp_rw [hrep]
  rw [integral_add (integrable_const p) hInt, integral_const,
    integral_toReal hmeasg.aemeasurable (Filter.Eventually.of_forall hlt),
    Measure.prod_apply hmeasS]
  simp only [measureReal_univ_eq_one, one_smul, add_right_inj]
  rfl

open MeasureTheory ProbabilityTheory in
/-- The liability distribution `ν` blurred by an independent Gaussian of scale `s`: the law
of `Y - s Z` for `Y ∼ ν` and `Z` standard normal.  Since the standard normal is symmetric
this is `ν` convolved with `N(0, s²)`.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is the pushforward measure that defines
Gaussian liability blurring in the formal model. -/
noncomputable def convolvedLiability (ν : Measure ℝ) (s : ℝ) : Measure ℝ :=
  ((gaussianReal 0 1).prod ν).map fun q ↦ q.2 - s * q.1

open MeasureTheory ProbabilityTheory in
instance convolvedLiability_isFiniteMeasure (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    IsFiniteMeasure (convolvedLiability ν s) :=
  ⟨by
    rw [convolvedLiability, Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ]
    exact measure_lt_top _ _⟩

open MeasureTheory ProbabilityTheory in
/-- **The Gaussian average of the link is the cdf of the blurred liability distribution.**

Combining the half-plane form with the pushforward along `(z, y) ↦ y - s z`: averaging `L`
at scale `s` is `p` plus the cdf of `convolvedLiability ν s`. -/
theorem link_average_eq_convolved_cdf (ν : Measure ℝ) [IsFiniteMeasure ν]
    (L : ℝ → ℝ) (p : ℝ) (hrep : ∀ u, L u = p + (ν (Set.Iic u)).toReal) (s x : ℝ) :
    ∫ z, L (x + s * z) ∂(gaussianReal 0 1)
      = p + ((convolvedLiability ν s) (Set.Iic x)).toReal := by
  rw [link_average_as_convolution ν L p hrep s x]
  congr 2
  rw [convolvedLiability, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  refine Set.ext fun q ↦ ?_
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory in
/-- **The invariance, stated as self-similarity of one measure.**

This is the reduction the section was built for.  If the link's averaging family is closed
at scale `s` with parameters `(α, β)`, `α > 0`, then the liability distribution satisfies

`ν ⋆ N(0, s²)  =  ν pushed forward by  y ↦ (y - β)/α`.

No integral and no unknown function survive in it: an equation between two finite measures
on the line, holding at every scale.  The two sides are compared through their cdfs and
`Measure.ext_of_Iic` finishes, which is legitimate precisely because both are finite.

What is left of `link_rigidity` is exactly the classical statement that a finite measure
reproducing itself, up to affine change of variable, under convolution with every Gaussian
is Gaussian — on characteristic functions, `φ(ξ) e^{-s²ξ²/2} = e^{iβξ} φ(αξ)`.  That gap is
now self-contained, and is about characteristic functions rather than about an arbitrary
monotone link. -/
theorem liability_selfSimilar_of_invariance (ν : Measure ℝ) [IsFiniteMeasure ν]
    (L : ℝ → ℝ) (p : ℝ) (hrep : ∀ u, L u = p + (ν (Set.Iic u)).toReal)
    {s α β : ℝ} (hα : 0 < α)
    (hinv : ∀ x, ∫ z, L (x + s * z) ∂(gaussianReal 0 1) = L (α * x + β)) :
    convolvedLiability ν s = ν.map fun y ↦ (y - β) / α := by
  haveI : IsFiniteMeasure (ν.map fun y : ℝ ↦ (y - β) / α) :=
    ⟨by
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
      exact measure_lt_top _ _⟩
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  have hcdf : ((convolvedLiability ν s) (Set.Iic x)).toReal
      = (ν (Set.Iic (α * x + β))).toReal := by
    have h := hinv x
    rw [link_average_eq_convolved_cdf ν L p hrep s x, hrep (α * x + β)] at h
    linarith
  have hmap : (ν.map fun y ↦ (y - β) / α) (Set.Iic x) = ν (Set.Iic (α * x + β)) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    refine Set.ext fun y ↦ ?_
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hα, sub_le_iff_le_add]
    constructor <;> intro h <;> linarith
  rw [hmap]
  exact (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 hcdf

open MeasureTheory ProbabilityTheory in
/-- Blurring multiplies the characteristic function by the Gaussian factor `e^{-s²t²/2}`.

Fubini in the form `integral_prod_mul`: the exponential of a sum factors, and the two
coordinates are independent under the product measure. -/
theorem charFun_convolvedLiability (ν : Measure ℝ) [IsFiniteMeasure ν] (s t : ℝ) :
    charFun (convolvedLiability ν s) t
      = Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t := by
  rw [convolvedLiability, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have key : ∀ q : ℝ × ℝ,
      Complex.exp ((t : ℂ) * ((q.2 - s * q.1 : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((-(s * t) : ℝ) : ℂ) * (q.1 : ℂ) * Complex.I)
          * Complex.exp ((t : ℂ) * (q.2 : ℂ) * Complex.I) := by
    intro q
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  simp_rw [key]
  rw [integral_prod_mul (fun z : ℝ ↦ Complex.exp (((-(s * t) : ℝ) : ℂ) * (z : ℂ) * Complex.I))
      (fun y : ℝ ↦ Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal]
  push_cast
  ring_nf

open MeasureTheory ProbabilityTheory in
/-- An affine change of variable rescales the argument of the characteristic function and
multiplies it by a unit-modulus phase. -/
theorem charFun_map_affine (ν : Measure ℝ) (α β t : ℝ) :
    charFun (ν.map fun y ↦ (y - β) / α) t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have key : ∀ y : ℝ,
      Complex.exp ((t : ℂ) * (((y - β) / α : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((t / α : ℝ) : ℂ) * (y : ℂ) * Complex.I)
          * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I) := by
    intro y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [key]
  rw [integral_mul_const, ← charFun_apply_real]

open MeasureTheory ProbabilityTheory in
/-- **The classification, reduced to one equation on one function.**

Everything above collapses into this.  Write `φ` for the characteristic function of the
liability distribution `ν`.  If the link's averaging family is closed at scale `s` with parameters
`(α, β)`, then

`e^{-s²t²/2} · φ(t) = φ(t/α) · e^{-iβt/α}`  for every `t`.

This holds for every scale `s`, with `α` and `β` depending on `s`, and it is the whole
content of the invariance hypothesis of `link_rigidity`: no measure, no monotone function
and no Gaussian integral is left in it.

`φ(t) = e^{iμt - σ²t²/2}` solves it with `α = 1/√(1 + s²/σ²)`, and the classical fact is
that nothing else does: taking moduli kills the phase and gives
`|φ(t)| e^{-s²t²/2} = |φ(t/α)|`, which forces `log |φ|` to be quadratic.

Formalising that last implication — a Cauchy-type functional equation with regularity — is
the remaining gap in `link_rigidity`, and it is now a statement about a single continuous
function `ℝ → ℂ` rather than about links, measures or Gaussian integrals. -/
theorem charFun_selfSimilar_of_invariance (ν : Measure ℝ) [IsFiniteMeasure ν]
    (L : ℝ → ℝ) (p : ℝ) (hrep : ∀ u, L u = p + (ν (Set.Iic u)).toReal)
    {s α β : ℝ} (hα : 0 < α)
    (hinv : ∀ x, ∫ z, L (x + s * z) ∂(gaussianReal 0 1) = L (α * x + β)) (t : ℝ) :
    Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I) := by
  rw [← charFun_convolvedLiability ν s t,
    liability_selfSimilar_of_invariance ν L p hrep hα hinv,
    charFun_map_affine ν α β t]

/-! ### Step one: the affine-probit parameters are identifiable

`link_rigidity` asserts an affine-probit representation exists. Before that is worth proving it
is worth knowing the representation is unique, because otherwise the conclusion names four
numbers that the data do not determine and the biological reading -- that `p` is a penetrance
floor and `p + q` a ceiling -- has nothing behind it.

Uniqueness is where the floor and the ceiling actually come from: they are the two tail limits
of the curve, which is why no amount of population drift can move them and why identifying them
needs tail calibration rather than dynamics. The horizontal parameters then follow from
injectivity.

Everything here is proved. -/

open Filter Topology in
/-- The probit tends to the floor at low liability. -/
theorem tendsto_affineProbit_atBot (p q α β : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun u ↦ p + q * Foundations.Phi (α * u + β)) Filter.atBot (𝓝 p) := by
  have harg : Filter.Tendsto (fun u : ℝ ↦ α * u + β) Filter.atBot Filter.atBot := by
    rw [Filter.tendsto_atBot]
    intro c
    filter_upwards [Filter.eventually_le_atBot ((c - β) / α)] with u hu
    have h1 : α * u ≤ α * ((c - β) / α) := mul_le_mul_of_nonneg_left hu (le_of_lt hα)
    have h2 : α * ((c - β) / α) = c - β := by field_simp
    linarith
  have hPhi : Filter.Tendsto (fun u : ℝ ↦ Foundations.Phi (α * u + β)) Filter.atBot (𝓝 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot _).comp harg
  have := (hPhi.const_mul q).const_add p
  simpa using this

open Filter Topology in
/-- The probit tends to the ceiling at high liability. -/
theorem tendsto_affineProbit_atTop (p q α β : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun u ↦ p + q * Foundations.Phi (α * u + β)) Filter.atTop (𝓝 (p + q)) := by
  have harg : Filter.Tendsto (fun u : ℝ ↦ α * u + β) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro c
    filter_upwards [Filter.eventually_ge_atTop ((c - β) / α)] with u hu
    have h1 : α * ((c - β) / α) ≤ α * u := mul_le_mul_of_nonneg_left hu (le_of_lt hα)
    have h2 : α * ((c - β) / α) = c - β := by field_simp
    linarith
  have hPhi : Filter.Tendsto (fun u : ℝ ↦ Foundations.Phi (α * u + β)) Filter.atTop (𝓝 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop _).comp harg
  have := (hPhi.const_mul q).const_add p
  simpa using this

/-- **The floor is identified**: it is the low-liability limit, so two affine-probit curves that
agree everywhere have the same penetrance floor. -/
theorem affineProbit_floor_unique (p q α β p' q' α' β' : ℝ) (hα : 0 < α) (hα' : 0 < α')
    (h : ∀ u, p + q * Foundations.Phi (α * u + β) = p' + q' * Foundations.Phi (α' * u + β')) :
    p = p' := by
  have h1 := tendsto_affineProbit_atBot p q α β hα
  have h2 := tendsto_affineProbit_atBot p' q' α' β' hα'
  have hfun : (fun u ↦ p + q * Foundations.Phi (α * u + β))
      = fun u ↦ p' + q' * Foundations.Phi (α' * u + β') := funext h
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The scale is identified**: it is the distance between the two tail limits. -/
theorem affineProbit_scale_unique (p q α β p' q' α' β' : ℝ) (hα : 0 < α) (hα' : 0 < α')
    (h : ∀ u, p + q * Foundations.Phi (α * u + β) = p' + q' * Foundations.Phi (α' * u + β')) :
    q = q' := by
  have hp : p = p' := affineProbit_floor_unique p q α β p' q' α' β' hα hα' h
  have h1 := tendsto_affineProbit_atTop p q α β hα
  have h2 := tendsto_affineProbit_atTop p' q' α' β' hα'
  have hfun : (fun u ↦ p + q * Foundations.Phi (α * u + β))
      = fun u ↦ p' + q' * Foundations.Phi (α' * u + β') := funext h
  rw [hfun] at h1
  have := tendsto_nhds_unique h1 h2
  rw [hp] at this
  linarith

/-- With floor and scale pinned, the two probit arguments agree pointwise. -/
theorem affineProbit_arg_eq (p q α β p' q' α' β' : ℝ) (hq : 0 < q) (hα : 0 < α) (hα' : 0 < α')
    (h : ∀ u, p + q * Foundations.Phi (α * u + β) = p' + q' * Foundations.Phi (α' * u + β')) (u : ℝ) :
    α * u + β = α' * u + β' := by
  have hp : p = p' := affineProbit_floor_unique p q α β p' q' α' β' hα hα' h
  have hqq : q = q' := affineProbit_scale_unique p q α β p' q' α' β' hα hα' h
  have hu := h u
  rw [← hp, ← hqq] at hu
  have : Foundations.Phi (α * u + β) = Foundations.Phi (α' * u + β') := by
    have hcancel : q * Foundations.Phi (α * u + β) = q * Foundations.Phi (α' * u + β') := by linarith
    exact mul_left_cancel₀ (ne_of_gt hq) hcancel
  exact Foundations.strictMono_Phi.injective this

/-- **The slope is identified.** -/
theorem affineProbit_slope_unique (p q α β p' q' α' β' : ℝ) (hq : 0 < q) (hα : 0 < α)
    (hα' : 0 < α')
    (h : ∀ u, p + q * Foundations.Phi (α * u + β) = p' + q' * Foundations.Phi (α' * u + β')) :
    α = α' := by
  have h0 := affineProbit_arg_eq p q α β p' q' α' β' hq hα hα' h 0
  have h1 := affineProbit_arg_eq p q α β p' q' α' β' hq hα hα' h 1
  simp only [mul_zero, zero_add, mul_one] at h0 h1
  linarith

/-- **The intercept is identified.** With all four pinned, the affine-probit representation the
rigidity theorem produces is the only one, so its floor and ceiling are properties of the curve
rather than of the parametrisation chosen for it. -/
theorem affineProbit_intercept_unique (p q α β p' q' α' β' : ℝ) (hq : 0 < q) (hα : 0 < α)
    (hα' : 0 < α')
    (h : ∀ u, p + q * Foundations.Phi (α * u + β) = p' + q' * Foundations.Phi (α' * u + β')) :
    β = β' := by
  have h0 := affineProbit_arg_eq p q α β p' q' α' β' hq hα hα' h 0
  simpa using h0

/-! ### Step two: what the invariance forces before any analysis

The two facts below are the ones that do not need the functional equation. They are proved from
monotonicity and boundedness alone, and they are what makes the normalisation in the necessity
argument legitimate: without them there is no floor to subtract and no scale to divide by. -/

open Filter Topology in
/-- **A bounded increasing response curve has a floor.** The infimum is approached at low
liability. This is where the `p` of the conclusion has to come from -- it is not a free
parameter the witness may choose. -/
theorem exists_floor_of_monotone_bddBelow (L : ℝ → ℝ) (hmono : Monotone L)
    (hbdd : ∀ u, 0 < L u) :
    Filter.Tendsto L Filter.atBot (𝓝 (⨅ u, L u)) :=
  tendsto_atBot_ciInf hmono ⟨0, fun _ ⟨u, hu⟩ ↦ hu ▸ le_of_lt (hbdd u)⟩

open Filter Topology in
/-- **And a ceiling.** -/
theorem exists_ceiling_of_monotone_bddAbove (L : ℝ → ℝ) (hmono : Monotone L)
    (hbdd : ∀ u, L u < 1) :
    Filter.Tendsto L Filter.atTop (𝓝 (⨆ u, L u)) :=
  tendsto_atTop_ciSup hmono ⟨1, fun _ ⟨u, hu⟩ ↦ hu ▸ le_of_lt (hbdd u)⟩

/-- **The floor is strictly below the ceiling** for a strictly increasing curve, so the scale `q`
the rigidity conclusion asserts positive is genuinely positive and the normalisation that turns
`L` into a distribution function does not divide by zero. -/
theorem floor_lt_ceiling_of_strictMono (L : ℝ → ℝ) (hmono : StrictMono L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) :
    (⨅ u, L u) < ⨆ u, L u := by
  have hbb : BddBelow (Set.range L) := ⟨0, fun _ ⟨u, hu⟩ ↦ hu ▸ le_of_lt (hlo u)⟩
  have hba : BddAbove (Set.range L) := ⟨1, fun _ ⟨u, hu⟩ ↦ hu ▸ le_of_lt (hhi u)⟩
  have h01 : L 0 < L 1 := hmono (by norm_num)
  calc (⨅ u, L u) ≤ L 0 := ciInf_le hbb 0
    _ < L 1 := h01
    _ ≤ ⨆ u, L u := le_ciSup hba 1

/-! ### Step three: the invariance cannot reverse or collapse the curve

The necessity argument normalises `L` by subtracting its floor and dividing by its scale, which
turns the invariance into a statement about a probability law. That normalisation is only
legitimate if the reparametrised slope the invariance produces is positive: a zero slope would
make the averaged curve constant, and a negative one would exchange the floor for the ceiling.

Neither is ruled out by the statement of the invariance, so both are ruled out here. The
argument is dominated convergence and nothing else -- the averaging weight is a probability
measure and the curve is bounded, so the tail limits pass through the integral. -/

open MeasureTheory ProbabilityTheory Filter Topology in
/-- **Gaussian averaging inherits whatever limit the liability curve has.**

Every displaced value is near the limit once `x` is far enough along the filter, and the
displacement has finite weight, so the average goes there too.  The floor and the ceiling
below are this theorem at `atBot` and at `atTop`; they were written out twice, and the two
copies differed only in the direction of three names. -/
theorem tendsto_gaussianAverage_of_tendsto (L : ℝ → ℝ) (hmono : Monotone L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) (σ : ℝ)
    {l : Filter ℝ} [l.IsCountablyGenerated] {limit : ℝ}
    (hL : Tendsto L l (𝓝 limit))
    (hshift : ∀ z : ℝ, Tendsto (fun x : ℝ ↦ x + σ * z) l l) :
    Tendsto (fun x ↦ ∫ z, L (x + σ * z) ∂(gaussianReal 0 1)) l (𝓝 limit) := by
  have hmeas : Measurable L := hmono.measurable
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  have hconst : ∫ _z : ℝ, limit ∂(gaussianReal 0 1) = limit := by
    simp
  rw [← hconst]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    (fun n ↦ (hmeas.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_const 1) (fun n ↦ ?_) ?_
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (hlo _)]
    exact le_of_lt (hhi _)
  · filter_upwards with z
    exact hL.comp ((hshift z).comp hx)

open MeasureTheory ProbabilityTheory Filter Topology in
/-- **Gaussian averaging inherits the floor.** -/
theorem tendsto_gaussianAverage_atBot (L : ℝ → ℝ) (hmono : Monotone L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) (σ : ℝ) :
    Tendsto (fun x ↦ ∫ z, L (x + σ * z) ∂(gaussianReal 0 1)) atBot (𝓝 (⨅ u, L u)) :=
  tendsto_gaussianAverage_of_tendsto L hmono hlo hhi σ
    (exists_floor_of_monotone_bddBelow L hmono hlo)
    (fun z ↦ tendsto_atBot_add_const_right _ (σ * z) tendsto_id)

open MeasureTheory ProbabilityTheory Filter Topology in
/-- **And the ceiling.** -/
theorem tendsto_gaussianAverage_atTop (L : ℝ → ℝ) (hmono : Monotone L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) (σ : ℝ) :
    Tendsto (fun x ↦ ∫ z, L (x + σ * z) ∂(gaussianReal 0 1)) atTop (𝓝 (⨆ u, L u)) :=
  tendsto_gaussianAverage_of_tendsto L hmono hlo hhi σ
    (exists_ceiling_of_monotone_bddAbove L hmono hhi)
    (fun z ↦ tendsto_atTop_add_const_right _ (σ * z) tendsto_id)

open MeasureTheory ProbabilityTheory Filter Topology in
/-- **The reparametrised slope is positive.**

The averaged curve has the same floor and the same ceiling as the original, and those differ.
A zero slope would make it constant and a negative one would swap the two, so neither survives.

This is the step that lets the necessity argument normalise: `(L - floor) / (ceiling - floor)`
is then a genuine distribution function and the invariance becomes a statement about adding an
independent Gaussian to a random liability. -/
theorem invariance_slope_pos (L : ℝ → ℝ) (hmono : StrictMono L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) (σ a' b' : ℝ)
    (hinv : ∀ x, ∫ z, L (x + σ * z) ∂(gaussianReal 0 1) = L (a' * x + b')) :
    0 < a' := by
  have hsep : (⨅ u, L u) < ⨆ u, L u := floor_lt_ceiling_of_strictMono L hmono hlo hhi
  have hfun : (fun x ↦ ∫ z, L (x + σ * z) ∂(gaussianReal 0 1))
      = fun x ↦ L (a' * x + b') := funext hinv
  have hbot := tendsto_gaussianAverage_atBot L hmono.monotone hlo hhi σ
  have htop := tendsto_gaussianAverage_atTop L hmono.monotone hlo hhi σ
  rw [hfun] at hbot htop
  rcases lt_trichotomy a' 0 with hneg | hzero | hpos
  · exfalso
    -- a negative slope sends low liability to high, so the two limits are exchanged
    have harg : Tendsto (fun x : ℝ ↦ a' * x + b') atBot atTop := by
      rw [Filter.tendsto_atTop]
      intro c
      filter_upwards [Filter.eventually_le_atBot ((c - b') / a')] with u hu
      have ha0 : a' ≠ 0 := ne_of_lt hneg
      have h1 : a' * ((c - b') / a') ≤ a' * u :=
        mul_le_mul_of_nonpos_left hu (le_of_lt hneg)
      have h2 : a' * ((c - b') / a') = c - b' := by field_simp
      linarith
    have hswap : Tendsto (fun x ↦ L (a' * x + b')) atBot (𝓝 (⨆ u, L u)) :=
      (exists_ceiling_of_monotone_bddAbove L hmono.monotone hhi).comp harg
    exact absurd (tendsto_nhds_unique hbot hswap) (ne_of_lt hsep)
  · exfalso
    -- a zero slope makes the averaged curve constant, so it has no room for two limits
    subst hzero
    simp only [zero_mul, zero_add] at hbot htop
    have h1 : (⨅ u, L u) = L b' := tendsto_nhds_unique hbot tendsto_const_nhds
    have h2 : (⨆ u, L u) = L b' := tendsto_nhds_unique htop tendsto_const_nhds
    rw [h1, h2] at hsep
    exact absurd hsep (lt_irrefl _)
  · exact hpos

/-! ### Step four: averaging cannot see a jump

`link_average_as_convolution` needs a liability measure `ν` with `L u = p + ν (Iic u)`, and a
monotone bounded curve carries one only if it is right-continuous. The hypotheses of
`link_rigidity` do not say that: `StrictMono` permits countably many jumps.

They do not have to say it. A monotone curve is discontinuous at only countably many points, an
affine change of variable with nonzero scale keeps that set countable, and the standard normal
assigns it no mass. So the Gaussian average of the curve is the Gaussian average of its
right-continuous version, and the jumps are invisible to the averaging that the invariance is
about. -/

open MeasureTheory ProbabilityTheory Filter Topology Function in
/-- **The displaced discontinuity set is null.** -/
theorem gaussianAverage_ae_continuousAt (L : ℝ → ℝ) (hmono : Monotone L) (σ : ℝ) (hσ : σ ≠ 0)
    (x : ℝ) :
    ∀ᵐ z ∂(gaussianReal 0 1), ContinuousAt L (x + σ * z) := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  have hinj : Function.Injective (fun z : ℝ ↦ x + σ * z) := by
    intro a b hab
    simp only at hab
    exact mul_left_cancel₀ hσ (by linarith)
  have hcount : {z : ℝ | ¬ ContinuousAt L (x + σ * z)}.Countable :=
    Set.Countable.preimage hmono.countable_not_continuousAt hinj
  rw [MeasureTheory.ae_iff]
  exact hcount.measure_zero _

open MeasureTheory ProbabilityTheory Filter Topology Function in
/-- **Averaging a curve is averaging its right-continuous version.**

This is what lets the necessity argument replace `L` by a genuine distribution function without
changing anything the invariance says. Without it the representation `L u = p + ν (Iic u)` is an
extra hypothesis, and a hypothesis that strong would be doing the work the theorem claims to do. -/
theorem gaussianAverage_eq_rightLim (L : ℝ → ℝ) (hmono : Monotone L) (σ : ℝ) (hσ : σ ≠ 0)
    (x : ℝ) :
    ∫ z, L (x + σ * z) ∂(gaussianReal 0 1)
      = ∫ z, rightLim L (x + σ * z) ∂(gaussianReal 0 1) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [gaussianAverage_ae_continuousAt L hmono σ hσ x] with z hz
  exact (hmono.continuousWithinAt_Ioi_iff_rightLim_eq.mp hz.continuousWithinAt).symm

open MeasureTheory ProbabilityTheory Filter Topology Function in
/-- **The right-continuous version has the same floor and ceiling**, so replacing `L` by it does
not move the two numbers the conclusion identifies. -/
theorem rightLim_mem_Icc_of_bounded (L : ℝ → ℝ) (hmono : Monotone L)
    (hlo : ∀ u, 0 < L u) (hhi : ∀ u, L u < 1) (u : ℝ) :
    (⨅ v, L v) ≤ rightLim L u ∧ rightLim L u ≤ ⨆ v, L v := by
  have hbb : BddBelow (Set.range L) := ⟨0, fun _ ⟨v, hv⟩ ↦ hv ▸ le_of_lt (hlo v)⟩
  have hba : BddAbove (Set.range L) := ⟨1, fun _ ⟨v, hv⟩ ↦ hv ▸ le_of_lt (hhi v)⟩
  constructor
  · exact le_trans (ciInf_le hbb u) (hmono.le_rightLim le_rfl)
  · exact le_trans (hmono.rightLim_le (lt_add_one u)) (le_ciSup hba (u + 1))

/-! ### Step six: the self-similar law contracts, so its scale factor is below one

`charFun_selfSimilar_of_invariance` leaves one equation on one function. Solving it is an
iteration: substituting the equation into itself replaces `α` by `αⁿ`, and with `0 < α < 1` the
point `αⁿ u` runs to zero, where a characteristic function is its total mass. The limit then
evaluates the characteristic function in closed form and it is Gaussian.

That argument needs `α < 1`, which the invariance does not state. It is forced. Taking moduli in
the functional equation gives `‖ψ(u)‖ = ‖ψ(α u)‖ · exp(-(sαu)²/2)`, and iterating that bound with `α
≥ 1` drives `‖ψ(u)‖` below `M · exp(-n (su)²/2)` for every `n`. So `ψ` would vanish off the
origin while equalling the total mass at it, and a characteristic function of a finite measure is
continuous. Mathlib does not carry that continuity, so it is proved here by dominated convergence
against the constant bound one. -/

open MeasureTheory ProbabilityTheory Complex in
/-- **A characteristic function is continuous.** The integrand is bounded by one and continuous
in the argument, and the measure is finite, so dominated convergence applies directly. -/
theorem continuous_charFun_real (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Continuous (fun t : ℝ ↦ charFun ν t) := by
  simp only [charFun_apply_real]
  refine MeasureTheory.continuous_of_dominated (bound := fun _ : ℝ ↦ (1 : ℝ))
    (fun t ↦ by fun_prop) (fun t ↦ ?_) (integrable_const 1) ?_
  · filter_upwards with x
    rw [show ((t : ℂ) * (x : ℂ) * Complex.I) = (((t * x : ℝ)) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  · filter_upwards with x
    fun_prop

open MeasureTheory ProbabilityTheory Complex in
/-- The modulus form of the functional equation, at the substitution that makes it an iteration. -/
theorem norm_charFun_selfSimilar (ν : Measure ℝ)
    {s α β : ℝ} (hα : 0 < α)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I)) (u : ℝ) :
    Real.exp (-((s * (α * u)) ^ 2) / 2) * ‖charFun ν (α * u)‖ = ‖charFun ν u‖ := by
  have hcancel : α * u / α = u := by field_simp
  have h := heq (α * u)
  rw [hcancel] at h
  have hnorm := congrArg (fun z : ℂ ↦ ‖z‖) h
  simp only [norm_mul] at hnorm
  rw [Complex.norm_exp_ofReal_mul_I] at hnorm
  have hcoe : (-(((s * (α * u)) ^ 2 : ℝ) : ℂ) / 2)
      = (((-((s * (α * u)) ^ 2) / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [show ‖Complex.exp (-(((s * (α * u)) ^ 2 : ℝ) : ℂ) / 2)‖
      = Real.exp (-((s * (α * u)) ^ 2) / 2) by
    rw [hcoe, Complex.norm_exp, Complex.ofReal_re]] at hnorm
  simpa using hnorm

open MeasureTheory ProbabilityTheory Complex in
/-- **With a scale factor at least one, the characteristic function is squeezed to nothing.**
Each substitution of the equation into itself contributes another factor `exp(-(su)²/2)`, and
`α ≥ 1` keeps every contribution at least that large. -/
theorem norm_charFun_le_geometric (ν : Measure ℝ)
    {s α β : ℝ} (hα1 : 1 ≤ α)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I))
    (u : ℝ) (n : ℕ) :
    ‖charFun ν u‖ ≤ ν.real Set.univ * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2) := by
  have hα : 0 < α := lt_of_lt_of_le zero_lt_one hα1
  induction n generalizing u with
  | zero => simpa using norm_charFun_le (μ := ν) u
  | succ n ih =>
    have hrel := norm_charFun_selfSimilar ν hα heq u
    have hIH := ih (α * u)
    have hmass : (0 : ℝ) ≤ ν.real Set.univ := by positivity
    have hα2 : (1 : ℝ) ≤ α ^ 2 := by nlinarith
    have hsq : (s * u) ^ 2 ≤ (s * (α * u)) ^ 2 := by
      have hexp : (s * (α * u)) ^ 2 = α ^ 2 * (s * u) ^ 2 := by ring
      rw [hexp]
      nlinarith [sq_nonneg (s * u)]
    have hfac : Real.exp (-((s * (α * u)) ^ 2) / 2) ≤ Real.exp (-((s * u) ^ 2) / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmono : Real.exp (-(n : ℝ) * (s * (α * u)) ^ 2 / 2)
        ≤ Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2) := by
      refine Real.exp_le_exp.mpr ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have hbound : ‖charFun ν (α * u)‖ ≤ ν.real Set.univ * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2) :=
      hIH.trans (mul_le_mul_of_nonneg_left hmono hmass)
    calc ‖charFun ν u‖
        = Real.exp (-((s * (α * u)) ^ 2) / 2) * ‖charFun ν (α * u)‖ := hrel.symm
      _ ≤ Real.exp (-((s * u) ^ 2) / 2)
            * (ν.real Set.univ * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2)) :=
          mul_le_mul hfac hbound (norm_nonneg _) (Real.exp_pos _).le
      _ = ν.real Set.univ
            * (Real.exp (-((s * u) ^ 2) / 2) * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2)) := by ring
      _ = ν.real Set.univ * Real.exp (-((n + 1 : ℕ) : ℝ) * (s * u) ^ 2 / 2) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-! ### Step seven: iterating the equation evaluates the characteristic function

One substitution of the functional equation into itself turns `α` into `α²` and leaves behind a
Gaussian factor and a phase. Doing it `n` times leaves behind the two partial sums of a geometric
series, and `α < 1` makes both converge while `αⁿ u` runs to zero. The value at zero is the total
mass, so the limit is a closed form -- and the closed form is a Gaussian characteristic function
with variance `s²α²/(1-α²)` and mean `β/(1-α)`. -/

open MeasureTheory ProbabilityTheory Complex in
/-- **One substitution.** The equation, rearranged into the direction the iteration runs. -/
theorem charFun_selfSimilar_step (ν : Measure ℝ)
    {s α β : ℝ} (hα : 0 < α)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I)) (u : ℝ) :
    charFun ν u
      = charFun ν (α * u) * Complex.exp ((-((s * (α * u)) ^ 2) / 2 : ℝ))
        * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) := by
  have hcancel : α * u / α = u := by field_simp
  have h := heq (α * u)
  rw [hcancel] at h
  have hphase : β * (α * u) / α = β * u := by field_simp
  rw [hphase] at h
  have hcoe : (-(((s * (α * u)) ^ 2 : ℝ) : ℂ) / 2)
      = (((-((s * (α * u)) ^ 2) / 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcoe] at h
  have hunit : Complex.exp (((-(β * u) : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    rw [show (((-(β * u) : ℝ) : ℂ) * Complex.I + ((β * u : ℝ) : ℂ) * Complex.I) = 0 by
      push_cast; ring]
    exact Complex.exp_zero
  calc charFun ν u
      = charFun ν u * (Complex.exp (((-(β * u) : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I)) := by rw [hunit, mul_one]
    _ = (charFun ν u * Complex.exp (((-(β * u) : ℝ) : ℂ) * Complex.I))
          * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) := by ring
    _ = (Complex.exp ((((-((s * (α * u)) ^ 2) / 2 : ℝ)) : ℂ)) * charFun ν (α * u))
          * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) := by rw [← h]
    _ = charFun ν (α * u) * Complex.exp ((-((s * (α * u)) ^ 2) / 2 : ℝ))
          * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) := by ring

open MeasureTheory ProbabilityTheory Complex in
/-- **`n` substitutions.** The Gaussian exponents and the phases each accumulate as a partial sum
of a geometric series; this is the identity the limit is taken in. -/
theorem charFun_selfSimilar_iterate (ν : Measure ℝ)
    {s α β : ℝ} (hα : 0 < α)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I))
    (u : ℝ) (n : ℕ) :
    charFun ν u
      = charFun ν (α ^ n * u)
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2)
            * ∑ k ∈ Finset.range n, α ^ (2 * (k + 1)) : ℝ))
        * Complex.exp (((β * u * ∑ k ∈ Finset.range n, α ^ k : ℝ) : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : α ^ (n + 1) * u = α * (α ^ n * u) := by ring
    have hA : Complex.exp ((-((s * (α * (α ^ n * u))) ^ 2) / 2 : ℝ))
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2)
            * ∑ k ∈ Finset.range n, α ^ (2 * (k + 1)) : ℝ))
        = Complex.exp ((-(s ^ 2 * u ^ 2 / 2)
            * ∑ k ∈ Finset.range (n + 1), α ^ (2 * (k + 1)) : ℝ)) := by
      rw [← Complex.exp_add, Finset.sum_range_succ]
      congr 1
      push_cast
      ring
    have hB : Complex.exp (((β * (α ^ n * u) : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((β * u * ∑ k ∈ Finset.range n, α ^ k : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((β * u * ∑ k ∈ Finset.range (n + 1), α ^ k : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, Finset.sum_range_succ]
      congr 1
      push_cast
      ring
    rw [ih, charFun_selfSimilar_step ν hα heq (α ^ n * u), hpow, ← hA, ← hB]
    ring

/-! ### Step eight: the limit, and the closed form it produces

The iterate identity holds at every `n` with no convergence hypothesis. Letting `n` grow uses
`α < 1` three times: `αⁿ u` runs to zero, where a characteristic function is its total mass, and
the two partial sums run to `α²/(1-α²)` and `1/(1-α)`. The result is a closed form for the
characteristic function of the liability law, and it is a Gaussian one. -/

open MeasureTheory ProbabilityTheory Complex Filter Topology in
/-- **The characteristic function of a self-similar liability law, in closed form.**

Only a Gaussian is affinely self-similar under adding an independent Gaussian, and this is that
statement with the Gaussian exhibited rather than asserted to exist: variance `s²α²/(1-α²)` and
mean `β/(1-α)`, both read off the two geometric series. -/
theorem charFun_selfSimilar_closed_form (ν : Measure ℝ) [IsFiniteMeasure ν]
    {s α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I)) (u : ℝ) :
    charFun ν u
      = (ν.real Set.univ : ℂ)
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2) * (α ^ 2 / (1 - α ^ 2)) : ℝ))
        * Complex.exp (((β * u * (1 / (1 - α)) : ℝ) : ℂ) * Complex.I) := by
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hcont1 : Continuous (fun x : ℝ ↦ Complex.exp ((x : ℂ))) :=
    Complex.continuous_exp.comp Complex.continuous_ofReal
  have hcont2 : Continuous (fun x : ℝ ↦ Complex.exp ((x : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hz : Tendsto (fun n : ℕ ↦ α ^ n * u) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1).mul_const u
    simpa using h
  have hchar : Tendsto (fun n : ℕ ↦ charFun ν (α ^ n * u)) atTop
      (𝓝 ((ν.real Set.univ : ℂ))) := by
    have hc := ((continuous_charFun_real ν).tendsto 0).comp hz
    rwa [charFun_zero] at hc
  have hs1 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, α ^ (2 * (k + 1))) atTop
      (𝓝 (α ^ 2 / (1 - α ^ 2))) := by
    have hg : HasSum (fun k : ℕ ↦ α ^ 2 * (α ^ 2) ^ k) (α ^ 2 * (1 - α ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (sq_nonneg α) hα2).mul_left _
    have ht := hg.tendsto_sum_nat
    have hrw : ∀ n : ℕ, ∑ k ∈ Finset.range n, α ^ 2 * (α ^ 2) ^ k
        = ∑ k ∈ Finset.range n, α ^ (2 * (k + 1)) := by
      intro n
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← pow_mul, ← pow_add]
      ring_nf
    simp only [hrw] at ht
    rwa [div_eq_mul_inv]
  have hs2 : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, α ^ k) atTop
      (𝓝 (1 / (1 - α))) := by
    have ht := (hasSum_geometric_of_lt_one hα.le hα1).tendsto_sum_nat
    rwa [one_div]
  have hlim : Tendsto (fun n : ℕ ↦
      charFun ν (α ^ n * u)
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2)
            * ∑ k ∈ Finset.range n, α ^ (2 * (k + 1)) : ℝ))
        * Complex.exp (((β * u * ∑ k ∈ Finset.range n, α ^ k : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 ((ν.real Set.univ : ℂ)
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2) * (α ^ 2 / (1 - α ^ 2)) : ℝ))
        * Complex.exp (((β * u * (1 / (1 - α)) : ℝ) : ℂ) * Complex.I))) :=
    (hchar.mul ((hcont1.tendsto _).comp (tendsto_const_nhds.mul hs1))).mul
      ((hcont2.tendsto _).comp (tendsto_const_nhds.mul hs2))
  have hconst : (fun n : ℕ ↦
      charFun ν (α ^ n * u)
        * Complex.exp ((-(s ^ 2 * u ^ 2 / 2)
            * ∑ k ∈ Finset.range n, α ^ (2 * (k + 1)) : ℝ))
        * Complex.exp (((β * u * ∑ k ∈ Finset.range n, α ^ k : ℝ) : ℂ) * Complex.I))
      = fun _ : ℕ ↦ charFun ν u :=
    funext fun n ↦ (charFun_selfSimilar_iterate ν hα heq u n).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

open MeasureTheory ProbabilityTheory Complex Filter Topology in
/-- **The scale factor is strictly below one.**

`norm_charFun_le_geometric` says that with `α ≥ 1` the modulus of the characteristic function is
below `M · exp(-n (su)²/2)` for every `n`, which for `u ≠ 0` forces it to vanish. A
characteristic function that vanishes off the origin and equals the total mass at it is not
continuous, and `continuous_charFun_real` says it is. So `α < 1`, and the iteration converges. -/
theorem selfSimilar_alpha_lt_one (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hmass : 0 < ν.real Set.univ) {s α β : ℝ} (hs : s ≠ 0)
    (heq : ∀ t : ℝ, Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
      = charFun ν (t / α) * Complex.exp (((-(β * t / α) : ℝ) : ℂ) * Complex.I)) :
    α < 1 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ u : ℝ, u ≠ 0 → charFun ν u = 0 := by
    intro u hu
    have hc : 0 < (s * u) ^ 2 := by positivity
    have hbound : ∀ n : ℕ,
        ‖charFun ν u‖ ≤ ν.real Set.univ * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2) :=
      fun n ↦ norm_charFun_le_geometric ν hcon heq u n
    have hinner : Tendsto (fun n : ℕ ↦ -(n : ℝ) * (s * u) ^ 2 / 2) atTop atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_gt (-b * 2 / (s * u) ^ 2)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hnr : -b * 2 / (s * u) ^ 2 < (n : ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hn)
      rw [div_lt_iff₀ hc] at hnr
      linarith
    have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hinner
    have hlim : Tendsto (fun n : ℕ ↦ ν.real Set.univ
        * Real.exp (-(n : ℝ) * (s * u) ^ 2 / 2)) atTop (𝓝 0) := by
      simpa using hexp.const_mul (ν.real Set.univ)
    have hconstseq : Tendsto (fun _ : ℕ ↦ ‖charFun ν u‖) atTop (𝓝 ‖charFun ν u‖) :=
      tendsto_const_nhds
    have hle : ‖charFun ν u‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' hconstseq hlim hbound
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  have hseq : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim2 := ((continuous_charFun_real ν).tendsto 0).comp hseq
  have hallzero : (fun k : ℕ ↦ charFun ν (1 / ((k : ℝ) + 1))) = fun _ : ℕ ↦ (0 : ℂ) :=
    funext fun k ↦ hzero _ (by positivity)
  rw [Function.comp_def, hallzero] at hlim2
  have hzeroseq : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 (0 : ℂ)) := tendsto_const_nhds
  have hz0 : charFun ν 0 = 0 := (tendsto_nhds_unique hzeroseq hlim2).symm
  rw [charFun_zero] at hz0
  exact absurd (Complex.ofReal_eq_zero.mp hz0) (ne_of_gt hmass)

open MeasureTheory ProbabilityTheory Complex in
/-- Scaling a measure scales its characteristic function. -/
theorem charFun_smul_measure (μ : Measure ℝ) (c : ENNReal) (t : ℝ) :
    charFun (c • μ) t = ((c.toReal : ℝ) : ℂ) * charFun μ t := by
  simp only [charFun_apply_real]
  rw [MeasureTheory.integral_smul_measure, Complex.real_smul]

open MeasureTheory ProbabilityTheory Complex in
/-- **The cdf of a Gaussian is the standard one at the standardised argument.**

`cdf_gaussianReal_zero_mean` does the centred case, which is pure change of variable. The mean is
a translation, and translating the half-line is the whole of the general case. -/
theorem cdf_gaussianReal_eq_Phi (m : ℝ) (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    ((gaussianReal m v) (Set.Iic x)).toReal = Foundations.Phi ((x - m) / Real.sqrt (v : ℝ)) := by
  have hmap : (gaussianReal 0 v).map (fun y ↦ y + m) = gaussianReal m v := by
    have h := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := v) m
    rwa [zero_add] at h
  have hpre : (fun y : ℝ ↦ y + m) ⁻¹' Set.Iic x = Set.Iic (x - m) := by
    ext y
    simp [Set.mem_Iic, le_sub_iff_add_le]
  have hshift : (gaussianReal m v) (Set.Iic x) = (gaussianReal 0 v) (Set.Iic (x - m)) := by
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
  rw [hshift]
  have hcdf := cdf_gaussianReal_zero_mean v hv (x - m)
  rw [ProbabilityTheory.cdf_eq_real] at hcdf
  simpa [MeasureTheory.Measure.real] using hcdf

open MeasureTheory ProbabilityTheory in
/-- **The irreducible analytic classification.**

Let `ν` be a nonzero finite liability measure.  Suppose that, after adding Gaussian noise of
every positive scale, its characteristic function is unchanged up to an orientation-preserving
affine change of liability coordinates.  Then the cdf of `ν` is a positive multiple of an
affine probit cdf.

This is the analytic core of the link classification, and it carries no external theorem
parameter and no arbitrary response curve: the input is one finite measure and the explicit
characteristic-function equation

`exp (-(s t)^2 / 2) · φ(t) = φ(t / a) · exp (-i b t / a)`.

It is proved.  `selfSimilar_alpha_lt_one` forces the
affine multiplier below one, and `charFun_selfSimilar_closed_form` evaluates the characteristic
function outright by iterating the equation: the Gaussian factors and the phases accumulate as
geometric series, and the limit is a Gaussian characteristic function with the variance and mean
exhibited.  No classification theorem is invoked. -/
theorem liability_cdf_eq_affineProbit_of_charFun_selfSimilar
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hmass : 0 < (ν Set.univ).toReal)
    (hself : ∀ s : ℝ, 0 < s → ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ,
      Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
        = charFun ν (t / a) *
          Complex.exp (((-(b * t / a) : ℝ) : ℂ) * Complex.I)) :
    ∃ q α β : ℝ, 0 < q ∧ 0 < α ∧
      ∀ u : ℝ, (ν (Set.Iic u)).toReal = q * Foundations.Phi (α * u + β) := by
  obtain ⟨a, b, ha, heq⟩ := hself 1 one_pos
  have hmassR : 0 < ν.real Set.univ := hmass
  have ha1 : a < 1 := selfSimilar_alpha_lt_one ν hmassR one_ne_zero heq
  have hV : 0 < a ^ 2 / (1 - a ^ 2) := div_pos (by positivity) (by nlinarith)
  set V : ℝ := a ^ 2 / (1 - a ^ 2) with hVdef
  set w : NNReal := ⟨V, hV.le⟩ with hwdef
  have hwcoe : (w : ℝ) = V := rfl
  have hwne : w ≠ 0 := fun h ↦ absurd (congrArg NNReal.toReal h) (ne_of_gt hV)
  set m : ℝ := b * (1 / (1 - a)) with hmdef
  set M : ℝ := ν.real Set.univ with hMdef
  have hsqrt : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  haveI : IsFiniteMeasure ((ENNReal.ofReal M) • gaussianReal m w) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hchar : charFun ν = charFun ((ENNReal.ofReal M) • gaussianReal m w) := by
    funext u
    rw [charFun_smul_measure, ENNReal.toReal_ofReal hmassR.le, charFun_gaussianReal,
      charFun_selfSimilar_closed_form ν ha ha1 heq u, mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hwcoe, hmdef, hVdef]
    push_cast
    ring
  have hmeas : ν = (ENNReal.ofReal M) • gaussianReal m w := Measure.ext_of_charFun hchar
  refine ⟨M, 1 / Real.sqrt V, -(m / Real.sqrt V), hmassR, by positivity, fun u ↦ ?_⟩
  rw [hmeas, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hmassR.le, cdf_gaussianReal_eq_Phi m w hwne u]
  congr 2
  rw [hwcoe]
  field_simp
  ring


open MeasureTheory ProbabilityTheory in
/-- **Necessity: no other bounded link shape survives.** A strictly increasing bounded link whose
two-parameter family is closed under Gaussian averaging is a positive vertical affine transform
of the normal cdf composed with a positive affine map.

Proved, end to end, and not through the link's density: differentiating the invariance would
need smoothness these hypotheses do not supply. The link is the cdf of a liability measure
(`link_stieltjes_representation`), Gaussian averaging of the link is Gaussian blurring of that
measure (`link_average_as_convolution`), so the invariance says the measure is affinely
self-similar under blurring at every scale (`charFun_selfSimilar_of_invariance`), and only a
Gaussian is (`liability_cdf_eq_affineProbit_of_charFun_selfSimilar`). Boundedness is
load-bearing and does its work through the finiteness of that measure; it does not fix the
observation-channel floor and ceiling, which is why `p` and `q` remain in the conclusion. -/
theorem link_rigidity (L : ℝ → ℝ) (hmono : StrictMono L)
    (hbdd : ∀ u, 0 < L u ∧ L u < 1)
    (hinv : ∀ a b σ : ℝ, 0 < a → 0 < σ → ∃ a' b' : ℝ,
      ∀ x, ∫ z, L (a * (x + σ * z) + b) ∂(gaussianReal 0 1) = L (a' * x + b')) :
    ∃ p q α β : ℝ, 0 < q ∧ 0 < α ∧ ∀ u, L u = p + q * Foundations.Phi (α * u + β) := by
  have hcont : Continuous L := link_continuous L hmono hbdd hinv
  obtain ⟨ν, hνfin, huniv, hrep⟩ := link_stieltjes_representation L hmono hbdd hcont
  letI : IsFiniteMeasure ν := hνfin
  have hspan : 0 < (⨆ u, L u) - ⨅ u, L u := sub_pos.mpr (link_iInf_lt_iSup L hmono hbdd)
  have hmass : 0 < (ν Set.univ).toReal := by
    rw [huniv, ENNReal.toReal_ofReal hspan.le]
    exact hspan
  have hself : ∀ s : ℝ, 0 < s → ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ,
      Complex.exp (-(((s * t) ^ 2 : ℝ) : ℂ) / 2) * charFun ν t
        = charFun ν (t / a) *
          Complex.exp (((-(b * t / a) : ℝ) : ℂ) * Complex.I) := by
    intro s hs
    obtain ⟨a, b, hab⟩ := hinv 1 0 s one_pos hs
    have hab' : ∀ x, ∫ z, L (x + s * z) ∂(gaussianReal 0 1) = L (a * x + b) := by
      intro x
      simpa using hab x
    have ha : 0 < a := link_invariance_slope_pos L hmono hbdd one_pos hab
    refine ⟨a, b, ha, ?_⟩
    intro t
    exact charFun_selfSimilar_of_invariance ν L (⨅ v, L v) hrep ha hab' t
  obtain ⟨q, α, β, hq, hα, hcdf⟩ :=
    liability_cdf_eq_affineProbit_of_charFun_selfSimilar ν hmass hself
  refine ⟨⨅ v, L v, q, α, β, hq, hα, ?_⟩
  intro u
  rw [hrep u, hcdf u]

/-! ## The evolution law of the response curve

Theorem 1 of the source analysis: in the frozen-mark coupling the marked and unmarked
subpopulations solve the SAME forward equation, so the response curve `c = q/p` obeys a
drift-diffusion equation whose drift is built from the OBSERVED marginal `p`. The marginal is not
a companion to the conditional; it is a coefficient in the conditional's own equation.

The computation is the product rule applied to `L*(cp) - c L*p` with `L*ρ = ½(aρ)'' - (bρ)'`, and
what survives is `(ap)'c' + ½ap c'' - bp c'`. Dividing by `p` gives the drift
`a' + a (log p)' - b`. Both steps are below: the first as an algebraic identity in the derivative
values, in the style this file already uses for the stationary collapse, and the second as the
division, which is where `p > 0` is needed.

Analytic hypotheses -- that the densities are twice differentiable and that the equation holds in
a genuine sense -- are not formalized here, and no semigroup is constructed. What is proved is the
identity those hypotheses would be used to obtain. -/

/-- **The response curve's transport identity.**

    With `a, a', a''`, `b, b'`, `c, c', c''` and `p, p', p''` standing for the values of the
    coefficients and their derivatives at a point, the second-order operator applied to the
    product `c p`, minus `c` times the same operator applied to `p`, collapses to a
    first-and-second-order expression in `c` alone. Every term carrying `c` undifferentiated
    cancels, which is why the result is an evolution equation FOR the curve rather than an
    identity constraining it. -/
theorem responseCurve_transport_identity
    (a a' a'' b b' c c' c'' p p' p'' : ℝ) :
    (a'' * (c * p) + 2 * a' * (c' * p + c * p') + a * (c'' * p + 2 * c' * p' + c * p'')) / 2
        - (b' * (c * p) + b * (c' * p + c * p'))
        - c * ((a'' * p + 2 * a' * p' + a * p'') / 2 - (b' * p + b * p'))
      = (a' * p + a * p') * c' + a * p * c'' / 2 - b * p * c' := by
  ring

/-- **The marginal appears in the conditional's drift.**

    Dividing the transport identity by the population density turns `(a'p + a p')/p` into
    `a' + a (log p)'`, written here as `a' + a * (p'/p)` since the logarithmic derivative is
    exactly that quotient. The drift the curve feels is therefore assembled from the observed
    marginal and the generator's own coefficients, and at `p ≡ π` stationary it collapses back to
    `b` by `stationaryDrift_collapses_to_generator`. -/
theorem responseCurve_drift_from_marginal
    (a a' b c' c'' p p' : ℝ) (hp : p ≠ 0) :
    ((a' * p + a * p') * c' + a * p * c'' / 2 - b * p * c') / p
      = a * c'' / 2 + (a' + a * (p' / p) - b) * c' := by
  field_simp
  ring

/-! ## The probit realization dynamics

The one piece of the continuum realization theory that is calculus rather than analysis. Under
Ornstein-Uhlenbeck drift the probit family `Φ(a x + b)` is exactly invariant, and its parameters
obey `ȧ = -λ a - a³/2`. That planar system looks nonlinear and is not: the substitution
`A = a⁻²` linearises it to `Ȧ = 2λA + 1`, which is why the realization is integrable in closed
form rather than merely finite-dimensional.

What is proved here is exactly that substitution. The invariance of the family itself is also
proved, and this paragraph used to say it was not: `gaussianAverage_probit` IS the Gaussian
identity `E[Φ(α + βZ)] = Φ(α/√(1+β²))`, and `probit_invariant_under_ou` is the OU step. Both are
above, in this file. -/

/-- **The inverse-square substitution linearises the probit realization flow.**

    If the slope parameter obeys `ȧ = -λ a - a³/2`, then `A = a⁻²` obeys `Ȧ = 2λ A + 1`. The
    nonlinearity is a coordinate artifact: the realization dynamics are affine, hence solvable in
    closed form, which is what makes the two-dimensional invariant family explicit rather than
    merely existent. -/
theorem inverseSquare_linearises_probit_flow
    (a : ℝ → ℝ) (lam t : ℝ) (hne : a t ≠ 0)
    (hderiv : HasDerivAt a (-(lam * a t) - a t ^ 3 / 2) t) :
    HasDerivAt (fun s ↦ ((a s) ^ 2)⁻¹) (2 * lam * ((a t) ^ 2)⁻¹ + 1) t := by
  have hsqne : (a t) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hsq : HasDerivAt (fun s ↦ (a s) ^ 2)
      (2 * a t ^ 1 * (-(lam * a t) - a t ^ 3 / 2)) t := hderiv.pow 2
  have hinv := hsq.inv hsqne
  have hval : -(2 * a t ^ 1 * (-(lam * a t) - a t ^ 3 / 2)) / ((a t) ^ 2) ^ 2
      = 2 * lam * ((a t) ^ 2)⁻¹ + 1 := by
    field_simp
    ring
  rwa [hval] at hinv

/-! ## The stationary collapse -/

/-- **At stationarity the curve's transport drift is the generator's own drift.**

    The response curve moves with drift `a' + a (log p)' - b`, built from the observed population
    density `p`. Under reversibility the stationary density satisfies `b = a'/2 + a (log π)'/2`,
    and substituting it returns `b`: the drifting equation collapses to the generator. This is
    the algebraic step behind "at stationarity the curve flows by the semigroup itself", and it
    is the only continuum computation in this file that is pure algebra. -/
theorem stationaryDrift_collapses_to_generator (aPrime aTimesScore b : ℝ)
    (hrev : b = aPrime / 2 + aTimesScore / 2) :
    aPrime + aTimesScore - b = b := by
  rw [hrev]; ring

end Descent.Conditionals

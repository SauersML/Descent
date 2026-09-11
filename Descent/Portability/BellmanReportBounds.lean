/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw

assert_below Descent.Decision Descent.Program

/-!
# Attained sharp dynamic report bounds by finite-horizon dynamic programming

At each state of a finite space a finite family of admissible one-step laws is available, one
for every allowed local coupling of the prescribed coordinate rates. The backward Bellman
recursion computes the exact extreme expected terminal report over all admissible policies at
every horizon, the extremes are attained by an explicit policy chosen from the finitely many
admissible controls at each state and time, and the resulting values stay inside the range of
the terminal report. The Bellman operator is nonexpansive in the uniform norm, so an
iteration whose every step is within a fixed defect of the exact one stays within the number
of steps times that defect, which is the certified enclosure of DC (6.7) and PL (10.8).

This is the discrete-horizon form of DC Theorem 6.1, DC Corollary 6.2, DC Theorem 6.3 and
PL Theorem 10.3. Since the state space is an arbitrary finite type, the statements already
cover the augmented states of DC Corollary 6.2: recording snapshots at observation times
enlarges the finite state space and nothing else, and a history-dependent competitor on a
smaller space is a Markov competitor on the space of its histories. The continuous-time
optimality claims DC (6.5) and PL (10.7) are not formalized here; they quantify over
continuous-time jump processes with predictable rates, which this pin of Mathlib does not
provide.

It builds on `FiniteReportLaw` and its `expectation` from `UniversalMetricIdentification`,
imported through `ExactFiniteHistoryLaw`. The hypotheses are the manuscript's domain
conditions: a finite state space, a finite nonempty set of admissible local couplings, and a
bounded terminal report.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BellmanReportBounds

noncomputable section

variable {S Ctrl : Type*} [Fintype S] [Fintype Ctrl] [Nonempty Ctrl]

/-- The expectation of a constant report is that constant. -/
theorem expectation_const (p : FiniteReportLaw S) (c : ℝ) :
    p.expectation (fun _ ↦ c) = c := by
  simp only [FiniteReportLaw.expectation, ← Finset.sum_mul, p.mass_sum, one_mul]

/-- Expectation is monotone in the report statistic. -/
theorem expectation_mono (p : FiniteReportLaw S) (f g : S → ℝ) (h : ∀ s, f s ≤ g s) :
    p.expectation f ≤ p.expectation g :=
  Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (h s) (p.mass_nonneg s)

/-- Two expectations differ by at most the uniform distance of their statistics. -/
theorem abs_expectation_sub_le (p : FiniteReportLaw S) (f g : S → ℝ) (d : ℝ)
    (h : ∀ s, |f s - g s| ≤ d) : |p.expectation f - p.expectation g| ≤ d := by
  have hsplit : p.expectation f - p.expectation g = ∑ s, p.mass s * (f s - g s) := by
    simp only [FiniteReportLaw.expectation, mul_sub, Finset.sum_sub_distrib]
  rw [hsplit]
  calc |∑ s, p.mass s * (f s - g s)| ≤ ∑ s, |p.mass s * (f s - g s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, p.mass s * d := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (p.mass_nonneg s)]
        exact mul_le_mul_of_nonneg_left (h s) (p.mass_nonneg s)
    _ = d := by rw [← Finset.sum_mul, p.mass_sum, one_mul]

/-- Two finite minima differ by at most the uniform distance of the minimised families. -/
theorem abs_inf'_sub_le (f g : Ctrl → ℝ) (d : ℝ) (h : ∀ c, |f c - g c| ≤ d) :
    |Finset.univ.inf' Finset.univ_nonempty f -
      Finset.univ.inf' Finset.univ_nonempty g| ≤ d := by
  obtain ⟨cf, -, hcf⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Ctrl)) f
  obtain ⟨cg, -, hcg⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Ctrl)) g
  have h1 : Finset.univ.inf' Finset.univ_nonempty f ≤ f cg :=
    Finset.inf'_le _ (Finset.mem_univ cg)
  have h2 : Finset.univ.inf' Finset.univ_nonempty g ≤ g cf :=
    Finset.inf'_le _ (Finset.mem_univ cf)
  have hf := abs_le.1 (h cf)
  have hg := abs_le.1 (h cg)
  rw [abs_le]
  constructor <;> linarith [hf.1, hf.2, hg.1, hg.2]

/-- Two finite maxima differ by at most the uniform distance of the maximised families. -/
theorem abs_sup'_sub_le (f g : Ctrl → ℝ) (d : ℝ) (h : ∀ c, |f c - g c| ≤ d) :
    |Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g| ≤ d := by
  obtain ⟨cf, -, hcf⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Ctrl)) f
  obtain ⟨cg, -, hcg⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Ctrl)) g
  have h1 : f cg ≤ Finset.univ.sup' Finset.univ_nonempty f :=
    Finset.le_sup' _ (Finset.mem_univ cg)
  have h2 : g cf ≤ Finset.univ.sup' Finset.univ_nonempty g :=
    Finset.le_sup' _ (Finset.mem_univ cf)
  have hf := abs_le.1 (h cf)
  have hg := abs_le.1 (h cg)
  rw [abs_le]
  constructor <;> linarith [hf.1, hf.2, hg.1, hg.2]

/-- The lower Bellman operator of DC (6.3): the minimum expected continuation over the
admissible local couplings available at each state. -/
def lowerStep (step : S → Ctrl → FiniteReportLaw S) (value : S → ℝ) : S → ℝ :=
  fun s ↦ Finset.univ.inf' Finset.univ_nonempty fun c ↦ (step s c).expectation value

/-- The upper Bellman operator of DC (6.3). -/
def upperStep (step : S → Ctrl → FiniteReportLaw S) (value : S → ℝ) : S → ℝ :=
  fun s ↦ Finset.univ.sup' Finset.univ_nonempty fun c ↦ (step s c).expectation value

/-- The finite-horizon lower value: the exact minimal expected terminal report. -/
def lowerValue (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ) : ℕ → S → ℝ
  | 0 => terminal
  | k + 1 => lowerStep step (lowerValue step terminal k)

/-- The finite-horizon upper value: the exact maximal expected terminal report. -/
def upperValue (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ) : ℕ → S → ℝ
  | 0 => terminal
  | k + 1 => upperStep step (upperValue step terminal k)

/-- The expected terminal report generated by a specified admissible policy. -/
def policyValue (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (policy : ℕ → S → Ctrl) : ℕ → S → ℝ
  | 0 => terminal
  | k + 1 => fun s ↦
      (step s (policy k s)).expectation (policyValue step terminal policy k)

/-- The Bellman recursion holds exactly at every horizon and state. -/
theorem lowerValue_succ (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (k : ℕ) (s : S) :
    lowerValue step terminal (k + 1) s =
      Finset.univ.inf' Finset.univ_nonempty fun c ↦
        (step s c).expectation (lowerValue step terminal k) := rfl

/-- The upper Bellman recursion holds exactly at every horizon and state. -/
theorem upperValue_succ (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (k : ℕ) (s : S) :
    upperValue step terminal (k + 1) s =
      Finset.univ.sup' Finset.univ_nonempty fun c ↦
        (step s c).expectation (upperValue step terminal k) := rfl

/-- One admissible step from a state is the point mass at that state bound with the chosen
transition law, so the dynamic program runs on the same composition of laws the corpus
already uses rather than on a private one. -/
theorem policyValue_succ_eq_bind (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (policy : ℕ → S → Ctrl) (k : ℕ) (s : S) :
    policyValue step terminal policy (k + 1) s =
      ((FiniteReportLaw.pointMass s).bind fun t ↦ step t (policy k t)).expectation
        (policyValue step terminal policy k) := by
  rw [FiniteReportLaw.expectation_bind, FiniteReportLaw.expectation_pointMass]
  rfl

/-- No admissible policy reports less than the lower value. -/
theorem lowerValue_le_policyValue (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (policy : ℕ → S → Ctrl) :
    ∀ (k : ℕ) (s : S),
      lowerValue step terminal k s ≤ policyValue step terminal policy k s := by
  intro k
  induction k with
  | zero => exact fun s ↦ le_refl _
  | succ k ih =>
    intro s
    calc lowerValue step terminal (k + 1) s
        ≤ (step s (policy k s)).expectation (lowerValue step terminal k) :=
          Finset.inf'_le _ (Finset.mem_univ (policy k s))
      _ ≤ (step s (policy k s)).expectation (policyValue step terminal policy k) :=
          expectation_mono _ _ _ ih
      _ = policyValue step terminal policy (k + 1) s := rfl

/-- No admissible policy reports more than the upper value. -/
theorem policyValue_le_upperValue (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (policy : ℕ → S → Ctrl) :
    ∀ (k : ℕ) (s : S),
      policyValue step terminal policy k s ≤ upperValue step terminal k s := by
  intro k
  induction k with
  | zero => exact fun s ↦ le_refl _
  | succ k ih =>
    intro s
    calc policyValue step terminal policy (k + 1) s
        = (step s (policy k s)).expectation (policyValue step terminal policy k) := rfl
      _ ≤ (step s (policy k s)).expectation (upperValue step terminal k) :=
          expectation_mono _ _ _ ih
      _ ≤ upperValue step terminal (k + 1) s := by
          rw [upperValue_succ]
          exact Finset.le_sup'
            (fun c ↦ (step s c).expectation (upperValue step terminal k))
            (Finset.mem_univ (policy k s))

/-- DC Theorem 6.1: the lower bound is attained by an explicit admissible policy, so it is a
minimum over admissible policies and not merely an infimum. -/
theorem exists_lower_optimal_policy (step : S → Ctrl → FiniteReportLaw S)
    (terminal : S → ℝ) :
    ∃ policy : ℕ → S → Ctrl, ∀ (k : ℕ) (s : S),
      policyValue step terminal policy k s = lowerValue step terminal k s := by
  classical
  choose policy hmem hvalue using fun (k : ℕ) (s : S) ↦
    Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Ctrl))
      fun c ↦ (step s c).expectation (lowerValue step terminal k)
  refine ⟨policy, ?_⟩
  intro k
  induction k with
  | zero => exact fun s ↦ rfl
  | succ k ih =>
    intro s
    show (step s (policy k s)).expectation (policyValue step terminal policy k) = _
    rw [funext ih]
    exact (hvalue k s).symm

/-- DC Theorem 6.1: the upper bound is attained by an explicit admissible policy. -/
theorem exists_upper_optimal_policy (step : S → Ctrl → FiniteReportLaw S)
    (terminal : S → ℝ) :
    ∃ policy : ℕ → S → Ctrl, ∀ (k : ℕ) (s : S),
      policyValue step terminal policy k s = upperValue step terminal k s := by
  classical
  choose policy hmem hvalue using fun (k : ℕ) (s : S) ↦
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Ctrl))
      fun c ↦ (step s c).expectation (upperValue step terminal k)
  refine ⟨policy, ?_⟩
  intro k
  induction k with
  | zero => exact fun s ↦ rfl
  | succ k ih =>
    intro s
    show (step s (policy k s)).expectation (policyValue step terminal policy k) = _
    rw [funext ih]
    exact (hvalue k s).symm

/-- The values stay inside the range of the terminal report at every horizon. -/
theorem lowerValue_mem_range (step : S → Ctrl → FiniteReportLaw S) (terminal : S → ℝ)
    (lo hi : ℝ) (hlo : ∀ s, lo ≤ terminal s) (hhi : ∀ s, terminal s ≤ hi) :
    ∀ (k : ℕ) (s : S), lo ≤ lowerValue step terminal k s ∧
      lowerValue step terminal k s ≤ hi := by
  intro k
  induction k with
  | zero => exact fun s ↦ ⟨hlo s, hhi s⟩
  | succ k ih =>
    intro s
    obtain ⟨cs, -, hcs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Ctrl))
      fun c ↦ (step s c).expectation (lowerValue step terminal k)
    constructor
    · rw [lowerValue_succ]
      refine (Finset.le_inf'_iff _ _).2 fun c _ ↦ ?_
      calc lo = (step s c).expectation (fun _ ↦ lo) := (expectation_const _ lo).symm
        _ ≤ (step s c).expectation (lowerValue step terminal k) :=
            expectation_mono _ _ _ fun t ↦ (ih t).1
    · rw [lowerValue_succ, hcs]
      calc (step s cs).expectation (lowerValue step terminal k)
          ≤ (step s cs).expectation (fun _ ↦ hi) :=
            expectation_mono _ _ _ fun t ↦ (ih t).2
        _ = hi := expectation_const _ hi

/-- The lower Bellman operator is nonexpansive in the uniform norm. -/
theorem abs_lowerStep_sub_le (step : S → Ctrl → FiniteReportLaw S) (v w : S → ℝ) (d : ℝ)
    (h : ∀ s, |v s - w s| ≤ d) :
    ∀ s, |lowerStep step v s - lowerStep step w s| ≤ d := by
  intro s
  exact abs_inf'_sub_le _ _ d fun c ↦ abs_expectation_sub_le (step s c) v w d h

/-- The upper Bellman operator is nonexpansive in the uniform norm. -/
theorem abs_upperStep_sub_le (step : S → Ctrl → FiniteReportLaw S) (v w : S → ℝ) (d : ℝ)
    (h : ∀ s, |v s - w s| ≤ d) :
    ∀ s, |upperStep step v s - upperStep step w s| ≤ d := by
  intro s
  exact abs_sup'_sub_le _ _ d fun c ↦ abs_expectation_sub_le (step s c) v w d h

/-- DC Theorem 6.3 and PL (10.8), the accumulation mechanism: nonexpansiveness prevents
amplification, so an iteration whose every step is within `defect` of the exact Bellman step
stays within the number of steps times that defect of the exact value. -/
theorem abs_approx_sub_lowerValue_le (step : S → Ctrl → FiniteReportLaw S)
    (terminal : S → ℝ) (approx : ℕ → S → ℝ) (defect : ℝ)
    (hzero : ∀ s, approx 0 s = terminal s)
    (hstep : ∀ (k : ℕ) (s : S), |approx (k + 1) s - lowerStep step (approx k) s| ≤ defect) :
    ∀ (k : ℕ) (s : S), |approx k s - lowerValue step terminal k s| ≤ k * defect := by
  intro k
  induction k with
  | zero =>
    intro s
    simp [hzero s, lowerValue]
  | succ k ih =>
    intro s
    have hnon := abs_lowerStep_sub_le step (approx k) (lowerValue step terminal k)
      ((k : ℝ) * defect) ih s
    have hstepk := hstep k s
    have hval : lowerValue step terminal (k + 1) s = lowerStep step
        (lowerValue step terminal k) s := rfl
    rw [hval]
    push_cast
    calc |approx (k + 1) s - lowerStep step (lowerValue step terminal k) s|
        ≤ |approx (k + 1) s - lowerStep step (approx k) s| +
            |lowerStep step (approx k) s - lowerStep step (lowerValue step terminal k) s| :=
          abs_sub_le _ _ _
      _ ≤ defect + (k : ℝ) * defect := add_le_add hstepk hnon
      _ = ((k : ℝ) + 1) * defect := by ring

/-- DC (6.7) and PL (10.8) in exact arithmetic: `N` steps of size `T / N`, each with local
defect `rate ^ 2 * (hi - lo) * (T / N) ^ 2`, accumulate to exactly
`rate ^ 2 * (hi - lo) * T ^ 2 / N`. -/
theorem accumulated_defect_eq (rate lo hi horizon : ℝ) (steps : ℕ) (hsteps : 0 < steps) :
    (steps : ℝ) * (rate ^ 2 * (hi - lo) * (horizon / steps) ^ 2) =
      rate ^ 2 * (hi - lo) * horizon ^ 2 / steps := by
  have hne : (steps : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hsteps.ne'
  field_simp

end

end Descent.Portability.BellmanReportBounds

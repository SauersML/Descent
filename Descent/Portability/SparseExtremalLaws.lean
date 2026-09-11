/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportRegionCertificates
import Mathlib.LinearAlgebra.Dimension.Finite

assert_below Descent.Decision Descent.Program

/-!
# Extremal compatible laws charge few states

An expected report statistic attains its extremes over the compatible laws, and this module
shows an extremizer can be taken to charge only as many states as the specified information
can distinguish. Concretely, some maximizing compatible law admits no nonzero direction that
is invisible to every specified summary, carries zero total mass, and vanishes off the states
it charges; the columns of the constraint system at the charged states are therefore linearly
independent, and the number of charged states is at most the number of specified summaries
plus one for total mass.

This is the support half of TQ Theorem 7.3 (7.7), whose interval half is already
`FiniteMetricIdentification.sharp_metric_interval`. The reduction is the manuscript's: at an
extremum with a dependent active set, the objective is flat along the dependence, so one can
move along it until a charged state drops out without changing the extremal value. That step
is carried out here, not assumed, by minimising the number of charged states over maximizers.

The hypotheses are the manuscript's domain conditions: the specified information is
consistent, so a compatible law exists. Nothing assumes the extremizer is a vertex; that is
what is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SparseExtremalLaws

open FiniteMetricIdentification

noncomputable section

variable {S O : Type*} [Fintype S] [Fintype O]

/-- The states a law actually charges. -/
def chargedStates (p : S → ℝ) : Finset S := by
  classical
  exact Finset.univ.filter fun s ↦ p s ≠ 0

/-- A state is charged exactly when it carries nonzero mass. -/
theorem mem_chargedStates {p : S → ℝ} {s : S} : s ∈ chargedStates p ↔ p s ≠ 0 := by
  classical
  simp [chargedStates]

/-- Moving a compatible law along a summary-invisible zero-mass direction keeps it
compatible as long as it stays nonnegative. -/
theorem shift_mem_feasible (observe : O → S → ℝ) (observed : O → ℝ) (p dir : S → ℝ)
    (hp : p ∈ feasible observe observed) (hmass : ∑ s, dir s = 0)
    (hobs : ∀ o, pairing (observe o) dir = 0) (t : ℝ)
    (hnonneg : ∀ s, 0 ≤ p s + t * dir s) : p + t • dir ∈ feasible observe observed := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro s
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hnonneg s
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, hp.1.2, ← Finset.mul_sum, hmass, mul_zero, add_zero]
  · intro o
    rw [pairing_add, pairing_smul, hp.2 o, hobs o, mul_zero, add_zero]

/-- The report vector of a compatible law is a point of the attainable report region, so the
sparse extremizers below are extremizers of that region's linear contrasts. -/
theorem reportVector_mem_reportRegion {J : Type*} (observe : O → S → ℝ) (observed : O → ℝ)
    (reportTable : J → S → ℝ) (p : S → ℝ) (hp : p ∈ feasible observe observed) :
    (fun j ↦ pairing (reportTable j) p) ∈
      ReportRegionCertificates.reportRegion observe observed reportTable :=
  ⟨p, hp, rfl⟩

/-- TQ Theorem 7.3: a maximizing compatible law can be chosen whose charged states admit no
nonzero summary-invisible zero-mass direction, so its active constraint columns are linearly
independent. -/
theorem exists_independent_maximizer (observe : O → S → ℝ) (observed : O → ℝ)
    (metric : S → ℝ) (hne : (feasible observe observed).Nonempty) :
    ∃ p ∈ feasible observe observed,
      (∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p) ∧
        ∀ dir : S → ℝ, (∀ s, s ∉ chargedStates p → dir s = 0) → ∑ s, dir s = 0 →
          (∀ o, pairing (observe o) dir = 0) → dir = 0 := by
  classical
  have hexists : ∃ n : ℕ, ∃ p ∈ feasible observe observed,
      (∀ q ∈ feasible observe observed, pairing metric q ≤ pairing metric p) ∧
        (chargedStates p).card = n := by
    obtain ⟨top, htop, hmaxtop⟩ := (feasible_compact observe observed).exists_isMaxOn hne
      (continuous_pairing metric).continuousOn
    exact ⟨_, top, htop, fun q hq ↦ hmaxtop hq, rfl⟩
  obtain ⟨p, hp, hmax, hcard⟩ := Nat.find_spec hexists
  refine ⟨p, hp, hmax, ?_⟩
  intro dir hsupp hmass hobs
  by_contra hnonzero
  have hS : Nonempty S := by
    rcases isEmpty_or_nonempty S with hempty | hnonempty
    · exact absurd hp.1.2 (by simp)
    · exact hnonempty
  have hpos : ∀ s, dir s ≠ 0 → 0 < p s := by
    intro s hs
    have hmem : s ∈ chargedStates p := by
      by_contra hno
      exact hs (hsupp s hno)
    exact lt_of_le_of_ne (hp.1.1 s) (Ne.symm (mem_chargedStates.1 hmem))
  have hstep_pos : ∀ s, (0 : ℝ) < (if dir s = 0 then (1 : ℝ) else p s / |dir s|) := by
    intro s
    by_cases hzero : dir s = 0
    · simp [hzero]
    · rw [if_neg hzero]
      exact div_pos (hpos s hzero) (abs_pos.mpr hzero)
  set eps := Finset.univ.inf' Finset.univ_nonempty
    (fun s ↦ if dir s = 0 then (1 : ℝ) else p s / |dir s|) with hepsdef
  have heps_pos : 0 < eps := (Finset.lt_inf'_iff _).2 fun s _ ↦ hstep_pos s
  have heps_bound : ∀ s, eps * |dir s| ≤ p s := by
    intro s
    by_cases hzero : dir s = 0
    · simpa [hzero] using hp.1.1 s
    · have hmem := Finset.inf'_le
        (f := fun t ↦ if dir t = 0 then (1 : ℝ) else p t / |dir t|) (Finset.mem_univ s)
      have hle : eps ≤ p s / |dir s| := by
        rw [hepsdef]
        simpa [hzero] using hmem
      have habs : (0 : ℝ) < |dir s| := abs_pos.mpr hzero
      have := mul_le_mul_of_nonneg_right hle habs.le
      rwa [div_mul_cancel₀ _ (ne_of_gt habs)] at this
  have hflat : pairing metric dir = 0 := by
    have hplus : p + eps • dir ∈ feasible observe observed := by
      refine shift_mem_feasible observe observed p dir hp hmass hobs eps fun s ↦ ?_
      have hb := heps_bound s
      have hneg := neg_abs_le (dir s)
      nlinarith [heps_pos.le]
    have hminus : p + (-eps) • dir ∈ feasible observe observed := by
      refine shift_mem_feasible observe observed p dir hp hmass hobs (-eps) fun s ↦ ?_
      have hb := heps_bound s
      have hle := le_abs_self (dir s)
      nlinarith [heps_pos.le]
    have h1 := hmax _ hplus
    have h2 := hmax _ hminus
    rw [pairing_add, pairing_smul] at h1 h2
    nlinarith [heps_pos]
  have hnegexists : ∃ s, dir s < 0 := by
    by_contra hno
    push_neg at hno
    refine hnonzero (funext fun s ↦ ?_)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hno i).1 hmass s (Finset.mem_univ s)
    simpa using hzero
  obtain ⟨start, hstart⟩ := hnegexists
  set falling := Finset.univ.filter (fun s ↦ dir s < 0) with hfalling
  have hfne : falling.Nonempty := ⟨start, by simp [hfalling, hstart]⟩
  set step := falling.inf' hfne (fun s ↦ p s / (-dir s)) with hstepdef
  obtain ⟨drop, hdropmem, hdropval⟩ :=
    Finset.exists_mem_eq_inf' hfne (fun s ↦ p s / (-dir s))
  have hdropneg : dir drop < 0 := by simpa [hfalling] using hdropmem
  have hstep_nonneg : 0 ≤ step := by
    refine le_of_lt ((Finset.lt_inf'_iff _).2 fun s hs ↦ ?_)
    have hsneg : dir s < 0 := by simpa [hfalling] using hs
    exact div_pos (hpos s (ne_of_lt hsneg)) (by linarith)
  have hshift_nonneg : ∀ s, 0 ≤ p s + step * dir s := by
    intro s
    rcases lt_or_ge (dir s) 0 with hs | hs
    · have hle : step ≤ p s / (-dir s) := by
        rw [hstepdef]
        exact Finset.inf'_le _ (by simp [hfalling, hs])
      have hposd : (0 : ℝ) < -dir s := by linarith
      have := mul_le_mul_of_nonneg_right hle hposd.le
      rw [div_mul_cancel₀ _ (ne_of_gt hposd)] at this
      nlinarith
    · nlinarith [hp.1.1 s]
  have hdropzero : p drop + step * dir drop = 0 := by
    have hquot : dir drop / (-dir drop) = -1 := by
      rw [div_neg, div_self (ne_of_lt hdropneg)]
    have hcalc : p drop / (-dir drop) * dir drop = -p drop := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hquot]
      ring
    rw [hstepdef, hdropval, hcalc]
    ring
  have hnewfeas : p + step • dir ∈ feasible observe observed :=
    shift_mem_feasible observe observed p dir hp hmass hobs step hshift_nonneg
  have hnewmax : ∀ q ∈ feasible observe observed,
      pairing metric q ≤ pairing metric (p + step • dir) := by
    intro q hq
    have hval : pairing metric (p + step • dir) = pairing metric p := by
      rw [pairing_add, pairing_smul, hflat, mul_zero, add_zero]
    rw [hval]
    exact hmax q hq
  have hsubset : chargedStates (p + step • dir) ⊆ chargedStates p := by
    intro s hs
    by_contra hno
    have hdirzero : dir s = 0 := hsupp s hno
    have hpzero : p s = 0 := by
      by_contra hpne
      exact hno (mem_chargedStates.2 hpne)
    refine (mem_chargedStates.1 hs) ?_
    simp [hpzero, hdirzero]
  have hstrict : chargedStates (p + step • dir) ⊂ chargedStates p := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ⟨drop, ?_, ?_⟩
    · exact mem_chargedStates.2 (ne_of_gt (hpos drop (ne_of_lt hdropneg)))
    · intro hmem
      refine (mem_chargedStates.1 hmem) ?_
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hdropzero
  have hlt : (chargedStates (p + step • dir)).card < Nat.find hexists := by
    rw [← hcard]
    exact Finset.card_lt_card hstrict
  exact Nat.find_min hexists hlt ⟨p + step • dir, hnewfeas, hnewmax, rfl⟩

/-- The constraint column at a state: total mass together with every specified summary. -/
def constraintColumn (observe : O → S → ℝ) (s : S) : Option O → ℝ
  | none => 1
  | some o => observe o s

/-- TQ Theorem 7.3: a law whose charged states admit no nonzero summary-invisible zero-mass
direction charges at most as many states as the rank of the constraint system, which is at
most the number of specified summaries plus one for total mass. -/
theorem card_chargedStates_le (observe : O → S → ℝ) (p : S → ℝ)
    (hindep : ∀ dir : S → ℝ, (∀ s, s ∉ chargedStates p → dir s = 0) → ∑ s, dir s = 0 →
      (∀ o, pairing (observe o) dir = 0) → dir = 0) :
    (chargedStates p).card ≤ Fintype.card O + 1 := by
  classical
  have hli : LinearIndependent ℝ fun s : (chargedStates p : Finset S) ↦
      constraintColumn observe (s : S) := by
    rw [linearIndependent_iff']
    intro t coeff hsum index hindex
    obtain ⟨dir, hdir⟩ : ∃ d : S → ℝ,
        ∀ s, d s = ∑ j ∈ t, if (j : S) = s then coeff j else 0 := ⟨_, fun _ ↦ rfl⟩
    have hdirsupp : ∀ s, s ∉ chargedStates p → dir s = 0 := by
      intro s hs
      rw [hdir s]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      refine if_neg fun heq ↦ hs ?_
      exact heq ▸ j.2
    have hsingle : ∀ j : (chargedStates p : Finset S), j ∈ t → dir (j : S) = coeff j := by
      intro j hj
      rw [hdir (j : S), Finset.sum_eq_single j]
      · exact if_pos rfl
      · intro k _ hk
        exact if_neg fun heq ↦ hk (Subtype.ext heq)
      · intro hno
        exact absurd hj hno
    have hnone : ∑ s, dir s = 0 := by
      have hval := congrFun hsum none
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        constraintColumn, mul_one] at hval
      have hrw : ∑ s, dir s = ∑ j ∈ t, coeff j := by
        rw [Finset.sum_congr rfl fun s _ ↦ hdir s, Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ by simp
      rw [hrw]
      exact hval
    have hobs : ∀ o, pairing (observe o) dir = 0 := by
      intro o
      have hval := congrFun hsum (some o)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        constraintColumn] at hval
      have hpoint : ∀ s : S, observe o s * dir s =
          ∑ j ∈ t, (if (j : S) = s then coeff j * observe o (j : S) else 0) := by
        intro s
        rw [hdir s, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : (j : S) = s
        · rw [if_pos hj, if_pos hj, hj]
          ring
        · rw [if_neg hj, if_neg hj, mul_zero]
      have hrw : pairing (observe o) dir = ∑ j ∈ t, coeff j * observe o (j : S) := by
        rw [pairing, Finset.sum_congr rfl fun s _ ↦ hpoint s, Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ by simp
      rw [hrw]
      exact hval
    have hzero := hindep dir hdirsupp hnone hobs
    have hval := hsingle index hindex
    rw [hzero] at hval
    simpa using hval.symm
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe] at hcard
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_option] at hcard

end

end Descent.Portability.SparseExtremalLaws

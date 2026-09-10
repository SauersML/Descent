/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationAccuracy
import Descent.Portability.SamplingDesignLaw

assert_below Descent.Decision Descent.Program

/-!
The finite threshold-selection and score-cleanup stage of `real_pt`. Candidate
files and the usable clumped GWAS table are explicit inputs. Nonfinite score
cells are represented by `none`; a missing score file is represented separately.
The GWAS/Firth solver, LD clumping, PCA and NumPy/PLINK numerical equivalence
are not supplied by this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PThresholdTrainingLaw

open FiniteReportLaw SamplingDesignLaw SimulationAccuracy TrainingNoiseAccuracy

/-- The source loop's order, including its tie-breaking priority. -/
noncomputable def thresholds : List ℝ :=
  [1 / 20000000, 1 / 1000000, 1 / 10000, 1 / 1000, 1 / 100,
    1 / 20, 1 / 10, 1 / 2, 1]

structure Ranked (A : Type*) where
  payload : A
  quality : ℝ

/-- Replace the incumbent only on a strict improvement. -/
noncomputable def advance {A : Type*} (incumbent : Option (Ranked A)) (next : Ranked A) :
    Option (Ranked A) :=
  match incumbent with
  | none => some next
  | some best => if best.quality < next.quality then some next else some best

noncomputable def scan {A : Type*} : Option (Ranked A) → List (Ranked A) → Option (Ranked A)
  | incumbent, [] => incumbent
  | incumbent, next :: rest => scan (advance incumbent next) rest

noncomputable def select {A : Type*} (candidates : List (Ranked A)) : Option (Ranked A) :=
  scan none candidates

theorem scan_append {A : Type*} (incumbent : Option (Ranked A))
    (first second : List (Ranked A)) :
    scan incumbent (first ++ second) = scan (scan incumbent first) second := by
  induction first generalizing incumbent with
  | nil => rfl
  | cons head tail ih => exact ih (advance incumbent head)

theorem advance_tie_keeps_first {A : Type*} (first second : Ranked A)
    (h : second.quality = first.quality) : advance (some first) second = some first := by
  simp [advance, h]

theorem scan_mem {A : Type*} (incumbent : Option (Ranked A))
    (candidates : List (Ranked A)) (winner : Ranked A)
    (h : scan incumbent candidates = some winner) :
    incumbent = some winner ∨ winner ∈ candidates := by
  induction candidates generalizing incumbent with
  | nil => exact Or.inl h
  | cons next rest ih =>
    rcases ih (advance incumbent next) h with heq | hm
    · cases incumbent with
      | none => exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj heq).symm))
      | some best =>
        simp only [advance] at heq
        split_ifs at heq with hbetter
        · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj heq).symm))
        · exact Or.inl heq
    · exact Or.inr (List.mem_cons.mpr (Or.inr hm))

theorem select_mem {A : Type*} (candidates : List (Ranked A)) (winner : Ranked A)
    (h : select candidates = some winner) : winner ∈ candidates := by
  rcases scan_mem none candidates winner h with hn | hm
  · cases hn
  · exact hm

theorem scan_some {A : Type*} (best : Ranked A) (candidates : List (Ranked A)) :
    ∃ winner, scan (some best) candidates = some winner := by
  induction candidates generalizing best with
  | nil => exact ⟨best, rfl⟩
  | cons next rest ih =>
    simp only [scan, advance]
    split_ifs <;> exact ih _

theorem select_none_iff {A : Type*} (candidates : List (Ranked A)) :
    select candidates = none ↔ candidates = [] := by
  cases candidates with
  | nil => simp [select, scan]
  | cons next rest =>
    obtain ⟨winner, h⟩ := scan_some next rest
    simp [select, scan, advance, h]

theorem scan_keeps_maximum {A : Type*} (best : Ranked A) (candidates : List (Ranked A))
    (h : ∀ next ∈ candidates, next.quality ≤ best.quality) :
    scan (some best) candidates = some best := by
  induction candidates with
  | nil => rfl
  | cons next rest ih =>
    have hnext := h next (by simp)
    simp only [scan, advance, if_neg (not_lt.mpr hnext)]
    exact ih (fun item hm ↦ h item (by simp [hm]))

/-- A candidate dominates every earlier candidate strictly and every later
candidate weakly exactly as the first occurrence of a maximum should. -/
theorem select_first_maximum {A : Type*} (before after : List (Ranked A)) (winner : Ranked A)
    (hearlier : ∀ item ∈ before, item.quality < winner.quality)
    (hlater : ∀ item ∈ after, item.quality ≤ winner.quality) :
    select (before ++ winner :: after) = some winner := by
  rw [select, scan_append]
  have hstep : advance (scan none before) winner = some winner := by
    cases h : scan none before with
    | none => rfl
    | some best =>
      have hm : best ∈ before := by
        rcases scan_mem none before best h with hn | hm
        · cases hn
        · exact hm
      simp [advance, hearlier best hm]
  simp only [scan, hstep]
  exact scan_keeps_maximum winner after hlater

theorem scan_quality_ge_incumbent {A : Type*} (best winner : Ranked A)
    (candidates : List (Ranked A)) (h : scan (some best) candidates = some winner) :
    best.quality ≤ winner.quality := by
  induction candidates generalizing best with
  | nil => exact le_of_eq (congrArg Ranked.quality (Option.some.inj h))
  | cons next rest ih =>
    simp only [scan, advance] at h
    split_ifs at h with hn
    · exact hn.le.trans (ih next h)
    · exact ih best h

theorem scan_quality_ge_member {A : Type*} (incumbent : Option (Ranked A))
    (candidates : List (Ranked A)) (winner item : Ranked A)
    (h : scan incumbent candidates = some winner) (hm : item ∈ candidates) :
    item.quality ≤ winner.quality := by
  induction candidates generalizing incumbent with
  | nil => simp at hm
  | cons next rest ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · cases incumbent with
      | none => exact scan_quality_ge_incumbent item winner rest h
      | some best =>
        simp only [scan, advance] at h
        split_ifs at h with hb
        · exact scan_quality_ge_incumbent item winner rest h
        · exact (le_of_not_gt hb).trans (scan_quality_ge_incumbent best winner rest h)
    · exact ih (advance incumbent next) h hm

theorem select_quality_maximal {A : Type*} (candidates : List (Ranked A))
    (winner item : Ranked A) (h : select candidates = some winner) (hm : item ∈ candidates) :
    item.quality ≤ winner.quality := scan_quality_ge_member none candidates winner item h hm

theorem comparison_bounds (caseScore controlScore : ℝ) :
    0 ≤ empiricalAUCComparison caseScore controlScore ∧
      empiricalAUCComparison caseScore controlScore ≤ 1 := by
  unfold empiricalAUCComparison
  split_ifs <;> norm_num

theorem comparison_affine_positive (scale shift caseScore controlScore : ℝ)
    (hs : 0 < scale) :
    empiricalAUCComparison (scale * caseScore + shift) (scale * controlScore + shift) =
      empiricalAUCComparison caseScore controlScore := by
  have hlt : scale * controlScore + shift < scale * caseScore + shift ↔
      controlScore < caseScore := by
    constructor <;> intro h <;> nlinarith
  have heq : scale * caseScore + shift = scale * controlScore + shift ↔
      caseScore = controlScore := by
    constructor <;> intro h <;> nlinarith
  simp only [empiricalAUCComparison, hlt, heq]

/-- A positive common AVG/SUM factor preserves AUC. Candidate validity has
an absolute variance cutoff and therefore needs a separate scale check. -/
theorem binaryAUC_affine_positive {R : Type*} [Fintype R] (law : FiniteReportLaw R)
    (scale shift : ℝ) (hs : 0 < scale) (score : R → ℝ) (labels : R → Bool) :
    law.binaryAUC (fun row ↦ scale * score row + shift) labels = law.binaryAUC score labels := by
  unfold binaryAUC binaryAUCNumerator
  simp only [comparison_affine_positive scale shift _ _ hs]

theorem oriented_auc_lower_bound (auc : ℝ) : 1 / 2 ≤ max auc (1 - auc) := by
  have hl := le_max_left auc (1 - auc)
  have hr := le_max_right auc (1 - auc)
  linarith

/-- `none` marks a missing/nonfinite score cell. These cells are not silently
made zero until after threshold selection and the fit-label sign decision. -/
structure Candidate (U : Type*) where
  threshold : ℝ
  snps : ℕ
  file : Option (U → Option ℝ)

structure Cohorts (U I Fit Sel : Type*) where
  fitRow : Fit → U
  selectionRow : Sel → U
  fitLabel : Fit → I
  selectionLabel : Sel → I

noncomputable def decoded {U : Type*} (scores : U → Option ℝ) : U → ℝ :=
  fun row ↦ (scores row).getD 0

def AllFinite {U R : Type*} (scores : U → Option ℝ) (row : R → U) : Prop :=
  ∀ r, (scores (row r)).isSome

variable {U I Fit Sel : Type*} [Fintype Fit] [Nonempty Fit] [Fintype Sel] [Nonempty Sel]

noncomputable def selectionScore (cohorts : Cohorts U I Fit Sel)
    (scores : U → Option ℝ) : Sel → ℝ := decoded scores ∘ cohorts.selectionRow

noncomputable def selectionLabels (cohorts : Cohorts U I Fit Sel)
    (labels : I → Bool) : Sel → Bool :=
  labels ∘ cohorts.selectionLabel

noncomputable def selectionAUC (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) : Option ℝ :=
  (uniform Sel).binaryAUC (selectionScore cohorts scores) (selectionLabels cohorts labels)

/-- Equality at the standard-deviation cutoff passes the source code's `<` test.
Finite scores, two outcome classes and at least one SNP are required as well. -/
noncomputable def evaluate (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (candidate : Candidate U) : Option (Ranked (Candidate U)) := by
  classical
  exact match candidate.file with
  | none => none
  | some scores =>
    if AllFinite scores cohorts.selectionRow ∧
        1 / 1000000000 ≤ Real.sqrt ((uniform Sel).variance (selectionScore cohorts scores)) ∧
        1 ≤ candidate.snps then
      match selectionAUC cohorts labels scores with
      | none => none
      | some auc => some ⟨candidate, max auc (1 - auc)⟩
    else none

omit [Fintype Fit] [Nonempty Fit] in
theorem evaluate_spec (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (candidate : Candidate U) (winner : Ranked (Candidate U))
    (he : evaluate cohorts labels candidate = some winner) :
    ∃ scores auc, candidate.file = some scores ∧
      AllFinite scores cohorts.selectionRow ∧
      1 / 1000000000 ≤ Real.sqrt ((uniform Sel).variance (selectionScore cohorts scores)) ∧
      1 ≤ candidate.snps ∧ selectionAUC cohorts labels scores = some auc ∧
      winner = ⟨candidate, max auc (1 - auc)⟩ := by
  classical
  unfold evaluate at he
  cases hf : candidate.file with
  | none => simp [hf] at he
  | some scores =>
    simp only [hf] at he
    split_ifs at he with hv
    · cases ha : selectionAUC cohorts labels scores with
      | none => simp [ha] at he
      | some auc =>
        simp only [ha, Option.some.injEq] at he
        exact ⟨scores, auc, rfl, hv.1, hv.2.1, hv.2.2, ha, he.symm⟩

/-- Invalid or absent candidates are skipped, preserving the source loop order. -/
noncomputable def chooseThreshold (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (candidates : List (Candidate U)) : Option (Ranked (Candidate U)) :=
  select (candidates.filterMap (evaluate cohorts labels))

omit [Fintype Fit] [Nonempty Fit] in
theorem chooseThreshold_valid (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (candidates : List (Candidate U)) (winner : Ranked (Candidate U))
    (h : chooseThreshold cohorts labels candidates = some winner) :
    ∃ candidate ∈ candidates, evaluate cohorts labels candidate = some winner := by
  exact List.mem_filterMap.mp (select_mem _ winner h)

omit [Fintype Fit] [Nonempty Fit] in
theorem chooseThreshold_maximal (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (candidates : List (Candidate U)) (winner other : Ranked (Candidate U))
    (h : chooseThreshold cohorts labels candidates = some winner)
    (candidate : Candidate U) (hm : candidate ∈ candidates)
    (he : evaluate cohorts labels candidate = some other) : other.quality ≤ winner.quality := by
  exact select_quality_maximal _ winner other h (List.mem_filterMap.mpr ⟨candidate, hm, he⟩)

noncomputable def fitScore (cohorts : Cohorts U I Fit Sel) (scores : U → Option ℝ) : Fit → ℝ :=
  decoded scores ∘ cohorts.fitRow

noncomputable def fitOutcomes (cohorts : Cohorts U I Fit Sel) (labels : I → Bool) : Fit → ℝ :=
  fun row ↦ if labels (cohorts.fitLabel row) then 1 else 0

/-- A nonfinite or constant fit vector gives an undefined Pearson coefficient,
whose comparison with zero does not trigger the source wrapper's sign flip. -/
noncomputable def flipSign (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) : Prop :=
  AllFinite scores cohorts.fitRow ∧
    0 < (uniform Fit).variance (fitScore cohorts scores) ∧
    0 < (uniform Fit).variance (fitOutcomes cohorts labels) ∧
    (uniform Fit).covariance (fitScore cohorts scores) (fitOutcomes cohorts labels) < 0

noncomputable def sign (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) : ℝ := by
  classical
  exact if flipSign cohorts labels scores then -1 else 1

noncomputable def cleanedScore (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) : U → ℝ := fun row ↦
  (scores row).map (fun value ↦ sign cohorts labels scores * value) |>.getD 0

omit [Fintype Sel] [Nonempty Sel] in
theorem sign_ne_zero (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) : sign cohorts labels scores ≠ 0 := by
  unfold sign
  split_ifs <;> norm_num

omit [Fintype Sel] [Nonempty Sel] in
theorem cleanedScore_eq_affine (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) :
    cleanedScore cohorts labels scores =
      affine (sign cohorts labels scores) 0 (decoded scores) := by
  funext row
  unfold cleanedScore affine decoded
  cases scores row <;> simp

omit [Fintype Sel] [Nonempty Sel] in
theorem cleanedScore_nonfinite_zero (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) (row : U) (h : scores row = none) :
    cleanedScore cohorts labels scores row = 0 := by simp [cleanedScore, h]

/-- The selected file is oriented using fit labels and only then sanitized.
The minimum clumped-SNP guard is a run-level failure before any candidate scan. -/
noncomputable def learnScore (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (clumpedCount : ℕ) (candidates : List (Candidate U)) : Option (U → ℝ) := do
  if 20 ≤ clumpedCount then
    let winner ← chooseThreshold cohorts labels candidates
    let scores ← winner.payload.file
    some (cleanedScore cohorts labels scores)
  else none

theorem learnScore_of_selected (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (clumpedCount : ℕ) (candidates : List (Candidate U)) (winner : Ranked (Candidate U))
    (scores : U → Option ℝ) (hc : 20 ≤ clumpedCount)
    (hw : chooseThreshold cohorts labels candidates = some winner)
    (hf : winner.payload.file = some scores) :
    learnScore cohorts labels clumpedCount candidates =
      some (cleanedScore cohorts labels scores) := by
  simp [learnScore, hc, hw, hf]

theorem learnScore_insufficient_clumps (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (clumpedCount : ℕ) (candidates : List (Candidate U)) (hc : clumpedCount < 20) :
    learnScore cohorts labels clumpedCount candidates = none := by
  simp [learnScore, not_le.mpr hc]

omit [Fintype Sel] [Nonempty Sel] in
theorem sign_nonfinite_fit (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) (row : Fit) (h : scores (cohorts.fitRow row) = none) :
    sign cohorts labels scores = 1 := by
  have hn : ¬ AllFinite scores cohorts.fitRow := by
    intro hf
    have hr := hf row
    simp [h] at hr
  simp [sign, flipSign, hn]

omit [Fintype Sel] [Nonempty Sel] in
theorem flipSign_iff_negative_correlation (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) (hf : AllFinite scores cohorts.fitRow)
    (hs : 0 < (uniform Fit).variance (fitScore cohorts scores))
    (hy : 0 < (uniform Fit).variance (fitOutcomes cohorts labels)) :
    flipSign cohorts labels scores ↔
      (uniform Fit).covariance (fitScore cohorts scores) (fitOutcomes cohorts labels) /
        Real.sqrt ((uniform Fit).variance (fitScore cohorts scores) *
          (uniform Fit).variance (fitOutcomes cohorts labels)) < 0 := by
  have hd : 0 < Real.sqrt ((uniform Fit).variance (fitScore cohorts scores) *
      (uniform Fit).variance (fitOutcomes cohorts labels)) := Real.sqrt_pos.mpr (mul_pos hs hy)
  simp [flipSign, hf, hs, hy, div_lt_iff₀ hd]

omit [Fintype Sel] [Nonempty Sel] in
/-- Sign orientation preserves the entire partial squared correlation of the
sanitized score, including undefined constant-vector cases. -/
theorem cleanedScore_squaredCorrelation {R : Type*} [Fintype R]
    (cohorts : Cohorts U I Fit Sel) (labels : I → Bool) (scores : U → Option ℝ)
    (law : FiniteReportLaw R) (row : R → U) (liability : R → ℝ) :
    law.squaredCorrelation (cleanedScore cohorts labels scores ∘ row) liability =
      law.squaredCorrelation (decoded scores ∘ row) liability := by
  rw [cleanedScore_eq_affine]
  have h := squaredCorrelation_affine law (sign cohorts labels scores) 0 1 0
    (sign_ne_zero cohorts labels scores) one_ne_zero (decoded scores ∘ row) liability
  change law.squaredCorrelation
    (fun r ↦ sign cohorts labels scores * decoded scores (row r) + 0) liability = _
  change law.squaredCorrelation
    (fun r ↦ sign cohorts labels scores * decoded scores (row r) + 0)
      (fun r ↦ 1 * liability r + 0) = _ at h
  simpa only [one_mul, add_zero] using h

/-- The finite table after GWAS parsing: usability and clumped index-SNP
membership are retained separately, as in the source's filtering operations. -/
structure ClumpedTable (J : Type*) where
  usable : Finset J
  clumped : Finset J
  pValue : J → ℝ
  effect : J → ℝ

noncomputable def thresholdRows {J : Type*} (table : ClumpedTable J) (threshold : ℝ) :
    Finset J := by
  classical
  exact (table.usable ∩ table.clumped).filter (fun variant ↦ table.pValue variant ≤ threshold)

/-- Mechanistic weights are available as a separate specialization when
score files are certified as SNP sums with the relevant allele coding. -/
noncomputable def thresholdWeights {J : Type*} (table : ClumpedTable J)
    (threshold : ℝ) : J → ℝ := by
  classical
  exact fun variant ↦ if variant ∈ thresholdRows table threshold then table.effect variant else 0

noncomputable def linearScoreFiles {J : Type*} [Fintype J] (table : ClumpedTable J)
    (genotype : U → J → ℝ) (factor : ℝ → ℝ) : ℝ → Option (U → Option ℝ) :=
  fun threshold ↦ some (fun row ↦
    some (factor threshold * linearScore genotype (thresholdWeights table threshold) row))

noncomputable def candidatesFromTable {J : Type*} (table : ClumpedTable J)
    (files : ℝ → Option (U → Option ℝ)) : List (Candidate U) :=
  thresholds.map (fun threshold ↦
    ⟨threshold, (thresholdRows table threshold).card, files threshold⟩)

noncomputable def learnerFromTables {J : Type*} (cohorts : Cohorts U I Fit Sel)
    (tables : (I → Bool) → ClumpedTable J)
    (files : (I → Bool) → ℝ → Option (U → Option ℝ)) : (I → Bool) → Option (U → ℝ) :=
  fun labels ↦ learnScore cohorts labels (tables labels).clumped.card
    (candidatesFromTable (tables labels) (files labels))

omit [Fintype Fit] [Nonempty Fit] [Fintype Sel] [Nonempty Sel] in
theorem candidatesFromTable_mem {J : Type*} (table : ClumpedTable J)
    (files : ℝ → Option (U → Option ℝ)) (candidate : Candidate U)
    (h : candidate ∈ candidatesFromTable table files) :
    candidate.threshold ∈ thresholds ∧
      candidate.snps = (thresholdRows table candidate.threshold).card ∧
      candidate.file = files candidate.threshold := by
  obtain ⟨threshold, hm, rfl⟩ := List.mem_map.mp h
  exact ⟨hm, rfl, rfl⟩

omit [Fintype Fit] [Nonempty Fit] in
theorem chosen_from_table (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    {J : Type*} (table : ClumpedTable J) (files : ℝ → Option (U → Option ℝ))
    (winner : Ranked (Candidate U))
    (h : chooseThreshold cohorts labels (candidatesFromTable table files) = some winner) :
    winner.payload.threshold ∈ thresholds ∧
      winner.payload.snps = (thresholdRows table winner.payload.threshold).card ∧
      winner.payload.file = files winner.payload.threshold ∧ 1 / 2 ≤ winner.quality := by
  obtain ⟨candidate, hm, he⟩ := chooseThreshold_valid cohorts labels _ winner h
  obtain ⟨scores, auc, _, _, _, _, _, hw⟩ := evaluate_spec cohorts labels candidate winner he
  subst winner
  exact ⟨(candidatesFromTable_mem table files candidate hm).1,
    (candidatesFromTable_mem table files candidate hm).2.1,
    (candidatesFromTable_mem table files candidate hm).2.2, oriented_auc_lower_bound auc⟩

/-- Finite full-cohort scores are represented exactly as coefficients of row
selectors. This adapter also covers the sanitizer without asserting SNP linearity. -/
noncomputable def rowSelectors {R : Type*} (row : R → U) : R → U → ℝ := by
  classical
  exact fun r u ↦ if row r = u then 1 else 0

omit [Fintype Fit] [Nonempty Fit] [Fintype Sel] [Nonempty Sel] in
theorem linearScore_rowSelectors [Fintype U] {R : Type*} (row : R → U)
    (score : U → ℝ) (r : R) : linearScore (rowSelectors row) score r = score (row r) := by
  classical
  simp [linearScore, rowSelectors, eq_comm]

omit [Fintype Sel] [Nonempty Sel] in
theorem selected_score_behavior (cohorts : Cohorts U I Fit Sel) (labels : I → Bool)
    (scores : U → Option ℝ) (row : U) (value : ℝ) (h : scores row = some value) :
    cleanedScore cohorts labels scores row = sign cohorts labels scores * value := by
  simp [cleanedScore, h]

omit [Fintype Fit] [Nonempty Fit] [Fintype Sel] [Nonempty Sel] in
theorem linearScoreFiles_values {J : Type*} [Fintype J] (table : ClumpedTable J)
    (genotype : U → J → ℝ) (factor : ℝ → ℝ) (threshold : ℝ) :
    linearScoreFiles table genotype factor threshold =
      some (fun row ↦ some (factor threshold *
        ∑ variant ∈ thresholdRows table threshold,
          table.effect variant * genotype row variant)) := by
  classical
  unfold linearScoreFiles linearScore thresholdWeights
  congr 1
  funext row
  congr 1
  congr 1
  calc
    _ = ∑ variant ∈ thresholdRows table threshold,
        (if variant ∈ thresholdRows table threshold then table.effect variant else 0) *
          genotype row variant := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro variant _ hn
      simp [hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro variant hv
      simp [hv]

end Descent.Portability.PThresholdTrainingLaw

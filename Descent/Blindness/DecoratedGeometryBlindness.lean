/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- `witnessDivergence_eq_threeAncestryDistance` and the two decoration lemmas name
-- `Portability.threeAncestryDistance`, `ancestryPosition`, `ancestryScore`,
-- `ancestryScoreSwapped` and `threeAncestryConditional`, and `Spectral.binarySecondAnnotation`.
-- All six used to arrive through `Descent.Program.Conventions`, which this file no longer
-- imports; the modules that DEFINE them are named instead.
import Descent.Portability.MetricSpecificPortability.PrecisionRecall
import Descent.Portability.ContinuumCalibration

assert_below Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Conditionals`, `Descent.Portability`, `Descent.Program`:
--   Conditionals: reaches 1 module(s) -- `Descent.Conditionals.ConditionalGain`
--   Portability: reaches 20 module(s) -- `Descent.Portability.ClinicalUtilityFairness`, `Descent.Portability.ContinuumCalibration`, `Descent.Portability.MetricSpecificPortability.PrecisionRecall` and 17 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.Blindness

open scoped BigOperators

/-!
# What a distance array cannot see, and what alignment can

A family of populations carrying ancestry-specific outcome fields is a metric measure space with a
decoration: allele-frequency divergence supplies the metric, sampling weight the measure, and
the population-specific conditional risk the mark.  Three finite facts about that object, each
stated exactly and each with a biological reading.

* **Profile twins.**  Two populations equidistant from every population are invisible to the
  divergence matrix: transposing them leaves every entry unchanged.  Equal allele frequencies
  produce exactly this degeneracy in Hudson's `F_ST`.  A decoration breaks it -- which is what
  ancestry-specific outcome data buys, and it is not a rate improvement but an identifiability
  one.

* **Margin versus alignment.**  A functional of the decoration alone is invariant under every
  weight-preserving relabelling of the populations, so it cannot see how the decoration sits on
  the geometry.  The metric-weighted Dirichlet energy can: three populations, one multiset of
  risks, two assignments, and the alignment energies are `10/3` and `2` while the margin energies
  are equal.  This is the same obstruction as the gauge witness of
  `ContinuumCalibrationProgram`, now with the metric supplying the weights.

* **Rare populations are not proportionally rare.**  A subpopulation of frequency `ε` carrying a
  different conditional moves a variance-type functional by order `√ε`, not `ε`.  No Lipschitz
  constant in the frequency exists: the exponent is exactly one half, and it is the contamination
  geometry that forces it.  A group too small to perturb any mass-based distance can still
  dominate a variance-based calibration report.

A fourth, in the same spirit, about resources rather than geometry.

* **Budget and noise are conjugate, not reciprocal.**  Clipping an inverse at budget `Λ` and
  reading a modulus of continuity at noise `ε` are related by a Legendre-type trade, not by
  `ε = 1/Λ`.  The always-true half is recorded, and a two-mode witness shows the reciprocal
  dictionary failing at maximum strength: budgeted error `0` against modulus `1`.

Each is stated in the generality it holds in: an arbitrary finite family of populations, an
arbitrary nonnegative weight, an arbitrary divergence.  The explicit witnesses are there to show
the general theorems are not vacuous and that their converses fail, not to stand in for them.

None of this is asymptotic.  Every statement below is an identity or an inequality between finite
sums, and the witnesses are explicit.
-/

section ProfileTwins

variable {Pop : Type*} [Fintype Pop] [DecidableEq Pop]

/-- Two populations are *profile twins* for a divergence when every population is exactly as far
from one as from the other.  This is the degeneracy a divergence matrix cannot resolve.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a finite equality condition on a supplied
divergence. -/
def IsProfileTwin (divergence : Pop → Pop → ℝ) (s t : Pop) : Prop :=
  ∀ u, divergence s u = divergence t u

/-- Twins are at divergence zero from each other, provided the divergence vanishes on the
diagonal.  There is nothing left in the matrix to separate them. -/
theorem isProfileTwin_divergence_self_eq_zero (divergence : Pop → Pop → ℝ) (s t : Pop)
    (htwin : IsProfileTwin divergence s t) (hdiag : divergence t t = 0) :
    divergence s t = 0 := by
  rw [htwin t, hdiag]

/-- Replacing one twin by the other in the first slot changes no entry. -/
theorem isProfileTwin_left_invariant (divergence : Pop → Pop → ℝ) (s t : Pop)
    (htwin : IsProfileTwin divergence s t) (a b : Pop) :
    divergence (Equiv.swap s t a) b = divergence a b := by
  rcases eq_or_ne a s with hs | hs
  · rw [hs, Equiv.swap_apply_left, htwin b]
  rcases eq_or_ne a t with ht | ht
  · rw [ht, Equiv.swap_apply_right, htwin b]
  · rw [Equiv.swap_apply_of_ne_of_ne hs ht]

/-- Replacing one twin by the other in the second slot changes no entry either, once the
divergence is symmetric. -/
theorem isProfileTwin_right_invariant (divergence : Pop → Pop → ℝ) (s t : Pop)
    (htwin : IsProfileTwin divergence s t)
    (hsymm : ∀ a b, divergence a b = divergence b a) (a b : Pop) :
    divergence a (Equiv.swap s t b) = divergence a b := by
  rw [hsymm a (Equiv.swap s t b), hsymm a b]
  exact isProfileTwin_left_invariant divergence s t htwin b a

/-- **Twins are invisible to the divergence matrix.**  Transposing a pair of profile twins leaves
every entry of the matrix exactly as it was, so no statistic of pairwise divergences -- no
`F_ST` matrix, no principal-coordinate embedding computed from one, no clustering of it --
can distinguish the two labellings. -/
theorem divergence_swap_twin_invariant (divergence : Pop → Pop → ℝ) (s t : Pop)
    (htwin : IsProfileTwin divergence s t)
    (hsymm : ∀ a b, divergence a b = divergence b a) (a b : Pop) :
    divergence (Equiv.swap s t a) (Equiv.swap s t b) = divergence a b := by
  rw [isProfileTwin_right_invariant divergence s t htwin hsymm (Equiv.swap s t a) b,
    isProfileTwin_left_invariant divergence s t htwin a b]

/-- **And a decoration breaks the tie.**  The divergence matrix is fixed by the transposition
while a population-specific outcome field is not, so ancestry-specific outcome data separates
populations that genetic divergence alone provably cannot.  What the decoration buys here is
identifiability, not a faster rate. -/
theorem twins_divergence_blind_but_decoration_apart (divergence : Pop → Pop → ℝ)
    (field : Pop → ℝ) (s t : Pop) (htwin : IsProfileTwin divergence s t)
    (hsymm : ∀ a b, divergence a b = divergence b a) (hfield : field s ≠ field t) :
    (∀ a b, divergence (Equiv.swap s t a) (Equiv.swap s t b) = divergence a b) ∧
      field (Equiv.swap s t s) ≠ field s := by
  refine ⟨fun a b ↦ divergence_swap_twin_invariant divergence s t htwin hsymm a b, ?_⟩
  rw [Equiv.swap_apply_left]
  exact fun hcontra ↦ hfield hcontra.symm

end ProfileTwins

/-! ## The biological metric: Hudson's `F_ST` between allele frequencies -/

section AlleleFrequencyGeometry

variable {Pop : Type*} [Fintype Pop] [DecidableEq Pop]

/-- Divergence between two populations at one locus: Hudson's `F_ST` between their allele
frequencies.  Its denominator vanishes when both populations are fixed for the same allele; that
junk branch is named at `Core.hudsonFst`, and every consumer here inherits the same
requirement.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is `hudsonFst` evaluated on a supplied frequency
field. -/
noncomputable def alleleFrequencyDivergence (frequency : Pop → ℝ) (s t : Pop) : ℝ :=
  Descent.Core.hudsonFst (frequency s) (frequency t)

/-- **The divergence is symmetric**, as a divergence between unordered populations must be.  This
is the hypothesis the twin theorems above require, discharged for the biological metric. -/
theorem alleleFrequencyDivergence_symm (frequency : Pop → ℝ) (s t : Pop) :
    alleleFrequencyDivergence frequency s t = alleleFrequencyDivergence frequency t s := by
  unfold alleleFrequencyDivergence Descent.Core.hudsonFst
  congr 1 <;> ring

/-- **The divergence vanishes on the diagonal, pinned.**  A population does not diverge from
itself, whatever its allele frequency. -/
@[simp] theorem alleleFrequencyDivergence_self (frequency : Pop → ℝ) (s : Pop) :
    alleleFrequencyDivergence frequency s s = 0 := by
  unfold alleleFrequencyDivergence Descent.Core.hudsonFst
  simp

/-- **Equal allele frequencies make profile twins.**  Two populations with the same frequency are
exactly the degeneracy of the previous section: the `F_ST` matrix cannot tell them apart, at any
number of loci, at any sample size.  Only their outcome fields can. -/
theorem isProfileTwin_alleleFrequencyDivergence (frequency : Pop → ℝ) (s t : Pop)
    (hfreq : frequency s = frequency t) :
    IsProfileTwin (alleleFrequencyDivergence frequency) s t := by
  intro u
  unfold alleleFrequencyDivergence
  rw [hfreq]

end AlleleFrequencyGeometry

/-! ## Margin versus alignment

A functional of the decoration alone -- the distribution of ancestry-specific risks, ignoring
which population carries which -- is what a margin reports.  A functional that pairs the
decoration with the geometry is what alignment reports.  The first is invariant under every
weight-preserving relabelling; the second is not, and the smallest witness has three populations.
-/

section MarginVersusAlignment

variable {Pop : Type*} [Fintype Pop]

/-- Margin energy of a decoration field: the weighted mean squared disagreement between two
independently drawn populations, with the geometry discarded.  It delegates to
`ContinuumCalibration.posteriorPairwiseDriftEnergy` at a single covariate rather than restating
that quadratic form.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite quadratic form. -/
noncomputable def marginEnergy (weight : Pop → ℝ) (field : Pop → ℝ) : ℝ :=
  Portability.posteriorPairwiseDriftEnergy (fun _ : Unit ↦ weight) (fun p _ ↦ field p) ()

/-- Alignment energy of a decoration field: the same disagreements, each weighted by how far
apart the two populations are.  This is the decorated Dirichlet energy, and it is the smallest
functional that can see the decoration sitting on the geometry rather than beside it.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite quadratic form. -/
noncomputable def alignmentEnergy (weight : Pop → ℝ) (divergence : Pop → Pop → ℝ)
    (field : Pop → ℝ) : ℝ :=
  ∑ s, ∑ t, weight s * weight t * divergence s t * (field s - field t) ^ 2

/-- The margin energy written out: half the doubly weighted squared disagreement. -/
theorem marginEnergy_eq (weight : Pop → ℝ) (field : Pop → ℝ) :
    marginEnergy weight field =
      (1 / 2) * ∑ s, weight s * ∑ t, weight t * (field s - field t) ^ 2 := by
  unfold marginEnergy Portability.posteriorPairwiseDriftEnergy
  rfl

/-- **A constant decoration has no margin energy, pinned.**  Populations that agree disagree by
nothing. -/
@[simp] theorem marginEnergy_const (weight : Pop → ℝ) (value : ℝ) :
    marginEnergy weight (fun _ ↦ value) = 0 := by
  rw [marginEnergy_eq]
  simp

/-- **A constant decoration has no alignment energy either, pinned.**  However far apart the
populations are, agreement costs nothing. -/
@[simp] theorem alignmentEnergy_const (weight : Pop → ℝ) (divergence : Pop → Pop → ℝ)
    (value : ℝ) :
    alignmentEnergy weight divergence (fun _ ↦ value) = 0 := by
  unfold alignmentEnergy
  simp

/-- **A zero-divergence geometry has no alignment energy, pinned.**  With every population at
divergence zero from every other there is no geometry for the decoration to align with, and the
alignment energy collapses -- while the margin energy of the same field need not. -/
@[simp] theorem alignmentEnergy_zero_divergence (weight : Pop → ℝ) (field : Pop → ℝ) :
    alignmentEnergy weight (fun _ _ ↦ (0 : ℝ)) field = 0 := by
  unfold alignmentEnergy
  simp

/-- **Margin energy is blind to relabelling.**  Under any permutation of the populations that
preserves their weights, the margin energy is unchanged: it depends on the decoration only
through its distribution.  Reporting the spread of ancestry-specific risks therefore says nothing
about which ancestries carry which risk. -/
theorem marginEnergy_perm_invariant (weight : Pop → ℝ) (field : Pop → ℝ) (relabel : Equiv.Perm Pop)
    (hweight : ∀ p, weight (relabel p) = weight p) :
    marginEnergy weight (fun p ↦ field (relabel p)) = marginEnergy weight field := by
  have hkey : ∀ F : Pop → Pop → ℝ,
      (∑ s, ∑ t, F (relabel s) (relabel t)) = ∑ s, ∑ t, F s t := by
    intro F
    calc
      (∑ s, ∑ t, F (relabel s) (relabel t)) = ∑ s, ∑ t, F (relabel s) t :=
        Finset.sum_congr rfl (fun s _ ↦ Equiv.sum_comp relabel (F (relabel s)))
      _ = ∑ s, ∑ t, F s t := Equiv.sum_comp relabel (fun s ↦ ∑ t, F s t)
  rw [marginEnergy_eq, marginEnergy_eq]
  congr 1
  have hexpand : ∀ g : Pop → ℝ,
      (∑ s, weight s * ∑ t, weight t * (g s - g t) ^ 2) =
        ∑ s, ∑ t, weight s * weight t * (g s - g t) ^ 2 := by
    intro g
    refine Finset.sum_congr rfl (fun s _ ↦ ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ ↦ by ring)
  rw [hexpand, hexpand]
  calc
    (∑ s, ∑ t, weight s * weight t * (field (relabel s) - field (relabel t)) ^ 2) =
        ∑ s, ∑ t, weight (relabel s) * weight (relabel t) *
          (field (relabel s) - field (relabel t)) ^ 2 := by
          refine Finset.sum_congr rfl (fun s _ ↦ Finset.sum_congr rfl (fun t _ ↦ ?_))
          rw [hweight s, hweight t]
    _ = ∑ s, ∑ t, weight s * weight t * (field s - field t) ^ 2 :=
        hkey (fun s t ↦ weight s * weight t * (field s - field t) ^ 2)

/-- Reindexing a double sum by a permutation changes nothing. -/
theorem sum_double_comp_perm (relabel : Equiv.Perm Pop) (F : Pop → Pop → ℝ) :
    (∑ s, ∑ t, F (relabel s) (relabel t)) = ∑ s, ∑ t, F s t := by
  calc
    (∑ s, ∑ t, F (relabel s) (relabel t)) = ∑ s, ∑ t, F (relabel s) t :=
      Finset.sum_congr rfl (fun s _ ↦ Equiv.sum_comp relabel (F (relabel s)))
    _ = ∑ s, ∑ t, F s t := Equiv.sum_comp relabel (fun s ↦ ∑ t, F s t)

/-- **Alignment energy is invariant under exactly the symmetries of the decorated geometry.**  A
relabelling that preserves both the sampling weights and the divergences leaves the alignment
energy unchanged.  Together with the witness below -- a weight-preserving relabelling that does
not preserve divergences, and does change the energy -- this locates the alignment functional
precisely: it sees every relabelling except the ones that are isomorphisms of the geometry, while
the margin sees none of them. -/
theorem alignmentEnergy_perm_invariant (weight : Pop → ℝ) (divergence : Pop → Pop → ℝ)
    (field : Pop → ℝ) (relabel : Equiv.Perm Pop)
    (hweight : ∀ p, weight (relabel p) = weight p)
    (hdivergence : ∀ a b, divergence (relabel a) (relabel b) = divergence a b) :
    alignmentEnergy weight divergence (fun p ↦ field (relabel p)) =
      alignmentEnergy weight divergence field := by
  unfold alignmentEnergy
  calc
    (∑ s, ∑ t, weight s * weight t * divergence s t *
        (field (relabel s) - field (relabel t)) ^ 2) =
        ∑ s, ∑ t, weight (relabel s) * weight (relabel t) *
          divergence (relabel s) (relabel t) *
            (field (relabel s) - field (relabel t)) ^ 2 := by
          refine Finset.sum_congr rfl (fun s _ ↦ Finset.sum_congr rfl (fun t _ ↦ ?_))
          rw [hweight s, hweight t, hdivergence s t]
    _ = ∑ s, ∑ t, weight s * weight t * divergence s t * (field s - field t) ^ 2 :=
        sum_double_comp_perm relabel
          (fun a b ↦ weight a * weight b * divergence a b * (field a - field b) ^ 2)

/-- Transposing two equally weighted populations preserves the weights. -/
theorem weight_swap_invariant [DecidableEq Pop] (weight : Pop → ℝ) (s t : Pop)
    (hweight : weight s = weight t) (p : Pop) :
    weight (Equiv.swap s t p) = weight p := by
  rcases eq_or_ne p s with hp | hp
  · rw [hp, Equiv.swap_apply_left, hweight]
  rcases eq_or_ne p t with hq | hq
  · rw [hq, Equiv.swap_apply_right, hweight]
  · rw [Equiv.swap_apply_of_ne_of_ne hp hq]

/-- **Profile twins are invisible to alignment as well.**  Transposing two equally weighted
populations that are equidistant from everything leaves the alignment energy unchanged too -- so
the identifiability obstruction of the first section is not repaired by looking at how the
decoration sits on the geometry.  Nothing computed from divergences and weights can see it; only
the decoration itself can. -/
theorem alignmentEnergy_swap_twin_invariant [DecidableEq Pop] (weight : Pop → ℝ)
    (divergence : Pop → Pop → ℝ) (field : Pop → ℝ) (s t : Pop)
    (htwin : IsProfileTwin divergence s t)
    (hsymm : ∀ a b, divergence a b = divergence b a) (hweight : weight s = weight t) :
    alignmentEnergy weight divergence (fun p ↦ field (Equiv.swap s t p)) =
      alignmentEnergy weight divergence field :=
  alignmentEnergy_perm_invariant weight divergence field (Equiv.swap s t)
    (weight_swap_invariant weight s t hweight)
    (fun a b ↦ divergence_swap_twin_invariant divergence s t htwin hsymm a b)

/-- **A separated population is charged in proportion to its frequency, not its square.**  If one
population's risk differs from every other's by at least `gap`, its contribution to the margin
energy is at least `w(1 - w)gap²` where `w` is its sampling weight.  The two-population witness
below is the case of two populations; the content is that no number of other populations dilutes
the first-order dependence on `w`. -/
theorem marginEnergy_ge_separated_population [DecidableEq Pop] (weight field : Pop → ℝ) (p : Pop)
    (gap : ℝ) (hweight : ∀ q, 0 ≤ weight q) (htotal : ∑ q, weight q = 1)
    (hgap : 0 ≤ gap) (hsep : ∀ q, q ≠ p → gap ≤ |field p - field q|) :
    weight p * (1 - weight p) * gap ^ 2 ≤ marginEnergy weight field := by
  have hsq : ∀ q, q ≠ p → gap ^ 2 ≤ (field p - field q) ^ 2 := by
    intro q hq
    calc
      gap ^ 2 ≤ |field p - field q| ^ 2 := by
        have := hsep q hq
        nlinarith [abs_nonneg (field p - field q)]
      _ = (field p - field q) ^ 2 := sq_abs _
  have hrest : (∑ q ∈ Finset.univ.erase p, weight q) = 1 - weight p := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ p), htotal]
  -- the row at `p`
  have hrow : weight p * (1 - weight p) * gap ^ 2 ≤
      weight p * ∑ t, weight t * (field p - field t) ^ 2 := by
    have hinner : (1 - weight p) * gap ^ 2 ≤ ∑ t, weight t * (field p - field t) ^ 2 := by
      calc
        (1 - weight p) * gap ^ 2 = ∑ t ∈ Finset.univ.erase p, weight t * gap ^ 2 := by
          rw [← Finset.sum_mul, hrest]
        _ ≤ ∑ t ∈ Finset.univ.erase p, weight t * (field p - field t) ^ 2 := by
          refine Finset.sum_le_sum (fun t ht ↦ ?_)
          exact mul_le_mul_of_nonneg_left (hsq t (Finset.ne_of_mem_erase ht)) (hweight t)
        _ ≤ ∑ t, weight t * (field p - field t) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
          exact fun t _ _ ↦ mul_nonneg (hweight t) (sq_nonneg _)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner (hweight p)
  -- every other row sees `p` itself
  have hother : ∀ s ∈ Finset.univ.erase p,
      weight s * (weight p * gap ^ 2) ≤ weight s * ∑ t, weight t * (field s - field t) ^ 2 := by
    intro s hs
    refine mul_le_mul_of_nonneg_left ?_ (hweight s)
    have hterm_nonneg : ∀ t ∈ (Finset.univ : Finset Pop),
        0 ≤ weight t * (field s - field t) ^ 2 :=
      fun t _ ↦ mul_nonneg (hweight t) (sq_nonneg _)
    have hsingle : weight p * (field s - field p) ^ 2 ≤
        ∑ t, weight t * (field s - field t) ^ 2 := by
      exact Finset.single_le_sum hterm_nonneg (Finset.mem_univ p)
    have hgapsq : gap ^ 2 ≤ (field s - field p) ^ 2 := by
      have hne : s ≠ p := Finset.ne_of_mem_erase hs
      have hswap : (field p - field s) ^ 2 = (field s - field p) ^ 2 := by ring
      rw [← hswap]
      exact hsq s hne
    calc
      weight p * gap ^ 2 ≤ weight p * (field s - field p) ^ 2 :=
        mul_le_mul_of_nonneg_left hgapsq (hweight p)
      _ ≤ ∑ t, weight t * (field s - field t) ^ 2 := hsingle
  have hsplit : (∑ s, weight s * ∑ t, weight t * (field s - field t) ^ 2) =
      weight p * (∑ t, weight t * (field p - field t) ^ 2) +
        ∑ s ∈ Finset.univ.erase p, weight s * ∑ t, weight t * (field s - field t) ^ 2 :=
    (Finset.add_sum_erase Finset.univ
      (fun s ↦ weight s * ∑ t, weight t * (field s - field t) ^ 2) (Finset.mem_univ p)).symm
  have htail : (1 - weight p) * (weight p * gap ^ 2) ≤
      ∑ s ∈ Finset.univ.erase p, weight s * ∑ t, weight t * (field s - field t) ^ 2 := by
    calc
      (1 - weight p) * (weight p * gap ^ 2) =
          ∑ s ∈ Finset.univ.erase p, weight s * (weight p * gap ^ 2) := by
        rw [← Finset.sum_mul, hrest]
      _ ≤ ∑ s ∈ Finset.univ.erase p, weight s * ∑ t, weight t * (field s - field t) ^ 2 :=
        Finset.sum_le_sum hother
  rw [marginEnergy_eq, hsplit]
  linarith

end MarginVersusAlignment

/-! ### The three-population witness

Three populations at divergences `1`, `2`, `3`; the same three risks in both assignments; equal
sampling weights.  The margin cannot tell the assignments apart because it never looks at the
geometry.  The alignment energy separates them by a factor of `5/3`, and the direction of the
separation is the biologically meaningful one: putting the extreme risks on the two most diverged
populations costs more Dirichlet energy than putting them on adjacent ones.
-/

section ThreePopulationWitness

/-- Divergence between the three populations: the gap between their positions, tabulated.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite divergence. -/
noncomputable def witnessDivergence : Fin 3 → Fin 3 → ℝ :=
  ![![0, 1, 3], ![1, 0, 2], ![3, 2, 0]]

/-- The divergence entries involving the third population, pinned. -/
@[simp] theorem witnessDivergence_zero_two : witnessDivergence 0 2 = 3 := rfl

@[simp] theorem witnessDivergence_one_two : witnessDivergence 1 2 = 2 := rfl

@[simp] theorem witnessDivergence_two_zero : witnessDivergence 2 0 = 3 := rfl

@[simp] theorem witnessDivergence_two_one : witnessDivergence 2 1 = 2 := rfl

@[simp] theorem witnessDivergence_two_two : witnessDivergence 2 2 = 0 := rfl

/-- The decorated witness uses the ancestry distance array verbatim. -/
theorem witnessDivergence_eq_threeAncestryDistance :
    witnessDivergence = Portability.threeAncestryDistance := by
  funext s t
  fin_cases s <;> fin_cases t <;>
    norm_num [witnessDivergence, Portability.threeAncestryDistance, Portability.ancestryPosition]

/-- The tabulated divergence is the gap between the positions, as claimed. -/
theorem witnessDivergence_eq_position_gap (s t : Fin 3) :
    witnessDivergence s t = |Portability.ancestryPosition s - Portability.ancestryPosition t| := by
  fin_cases s <;> fin_cases t <;>
    norm_num [witnessDivergence, Portability.ancestryPosition]

/-- The witness divergence is symmetric. -/
theorem witnessDivergence_symm (s t : Fin 3) :
    witnessDivergence s t = witnessDivergence t s := by
  fin_cases s <;> fin_cases t <;> norm_num [witnessDivergence]

/-- **The witness divergence vanishes on the diagonal, pinned.** -/
theorem witnessDivergence_self (s : Fin 3) : witnessDivergence s s = 0 := by
  fin_cases s <;> norm_num [witnessDivergence]

/-- Equal sampling weight on each of the three populations.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite weight. -/
noncomputable def witnessWeight (_p : Fin 3) : ℝ := 1 / 3

/-- Reference evaluation: the witness is uniform on three points. -/
@[simp] theorem witnessWeight_at_reference_point (p : Fin 3) : witnessWeight p = 1 / 3 := rfl


/-! **The two decorations are `Portability.ancestryScore` and
`Portability.ancestryScoreSwapped`.** This module names them; it does not redeclare their
bodies `![0, 1, 2]` and `![0, 2, 1]` under local names. A witness that carries its own copy
of what it is a witness ABOUT can drift from it, and a theorem recording that the copy has
not drifted yet is the corpus paying to check its own copy. The canonical names are used
directly below. -/

/-- The third population's risk under the aligned assignment, pinned. -/
@[simp] theorem ancestryScore_two : Portability.ancestryScore 2 = 2 := rfl

/-- Equivalently, the aligned decoration is the canonical three-ancestry conditional itself. -/
theorem ancestryScore_eq_threeAncestryConditional :
    Portability.ancestryScore = Portability.threeAncestryConditional := by
  simpa only [Portability.ancestryScore, Portability.threeAncestryConditional] using Portability.ancestryScore_eq_ancestryScore


/-- The third population's risk under the transposed assignment, pinned. -/
@[simp] theorem ancestryScoreSwapped_two : Portability.ancestryScoreSwapped 2 = 1 := rfl

/-- The two assignments carry the same three risks: they differ only in which population holds
which, so every functional of the decoration alone must agree on them. -/
theorem ancestryScoreSwapped_is_relabelling :
    Portability.ancestryScoreSwapped 0 = Portability.ancestryScore 0 ∧
      Portability.ancestryScoreSwapped 1 = Portability.ancestryScore 2 ∧
        Portability.ancestryScoreSwapped 2 = Portability.ancestryScore 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [Portability.ancestryScoreSwapped, Portability.ancestryScore, Portability.threeAncestryConditional, Matrix.cons_val_two, Matrix.tail_cons]

/-- Both assignments carry the same margin energy: the two decorations are the same multiset of
risks under the same weights. -/
theorem marginEnergy_witness_eq :
    marginEnergy witnessWeight Portability.ancestryScore =
      marginEnergy witnessWeight Portability.ancestryScoreSwapped := by
  rw [marginEnergy_eq, marginEnergy_eq]
  norm_num [witnessWeight, Portability.ancestryScore, Portability.threeAncestryConditional, Portability.ancestryScoreSwapped, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The margin energy of the witness, evaluated: two thirds. -/
theorem marginEnergy_witnessAligned_eq :
    marginEnergy witnessWeight Portability.ancestryScore = 2 / 3 := by
  rw [marginEnergy_eq]
  norm_num [witnessWeight, Portability.ancestryScore, Portability.threeAncestryConditional, Fin.sum_univ_three, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- The alignment energy of the increasing assignment: ten thirds. -/
theorem alignmentEnergy_witnessAligned_eq :
    alignmentEnergy witnessWeight witnessDivergence Portability.ancestryScore = 10 / 3 := by
  unfold alignmentEnergy
  norm_num [witnessWeight, witnessDivergence, Portability.ancestryScore, Portability.threeAncestryConditional, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- The alignment energy of the transposed assignment: two. -/
theorem alignmentEnergy_witnessSwapped_eq :
    alignmentEnergy witnessWeight witnessDivergence Portability.ancestryScoreSwapped = 2 := by
  unfold alignmentEnergy
  norm_num [witnessWeight, witnessDivergence, Portability.ancestryScoreSwapped, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **Alignment sees what the margin cannot.**  Two decorations with identical margins -- the same
risks, the same weights, the same geometry -- have different alignment energies.  So a report of
how much ancestry-specific risks vary carries no information about how that variation sits on the
genetic geometry, and a claim about the latter cannot be supported by a measurement of the
former.  This is the gauge obstruction of `ContinuumCalibrationProgram` with the metric supplying
the weights. -/
theorem alignment_separates_what_margin_identifies :
    marginEnergy witnessWeight Portability.ancestryScore =
        marginEnergy witnessWeight Portability.ancestryScoreSwapped ∧
      alignmentEnergy witnessWeight witnessDivergence Portability.ancestryScore ≠
        alignmentEnergy witnessWeight witnessDivergence Portability.ancestryScoreSwapped := by
  refine ⟨marginEnergy_witness_eq, ?_⟩
  rw [alignmentEnergy_witnessAligned_eq, alignmentEnergy_witnessSwapped_eq]
  norm_num

end ThreePopulationWitness

/-! ## Rare populations are not proportionally rare

A subpopulation at frequency `ε` carrying a different conditional contributes `ε(1 - ε)` to a
variance functional, hence `√(ε(1-ε))` to its square root.  Against a contamination-type
distance, which charges the perturbation `ε`, the functional therefore moves like `√ε`: the
exponent is one half and no Lipschitz constant exists.  The practical reading is blunt.  A group
small enough to leave every mass-based diagnostic unmoved can still be the dominant term in a
variance-based calibration report, and shrinking it does not shrink its influence proportionally.
-/

section RareSubpopulation

/-- Two populations, the second at frequency `rare`.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite weight. -/
noncomputable def rareWeight (rare : ℝ) (p : Bool) : ℝ := if p then rare else 1 - rare

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem rareWeight_at_reference_point :
    rareWeight 1 true = 1 := by
  norm_num [rareWeight]


/-- The rare population carries risk one, the common population risk zero.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is a fixed finite decoration. -/
noncomputable def rareField : Bool → ℝ := Spectral.binarySecondAnnotation

/-- The rare-population mark is the shared binary indicator. -/
theorem rareField_eq_binarySecondAnnotation : rareField = Spectral.binarySecondAnnotation := rfl

/-- **The rare population's margin energy is exactly `ε(1 - ε)`.**  Its contribution to a
variance-type functional is first order in its frequency, not second. -/
theorem marginEnergy_rare_eq (rare : ℝ) :
    marginEnergy (rareWeight rare) rareField = rare * (1 - rare) := by
  rw [marginEnergy_eq]
  norm_num [rareWeight, rareField, Spectral.binarySecondAnnotation]
  ring

/-- **The energy at an absent subpopulation, pinned.**  A group of frequency zero contributes
nothing, so the previous theorem is measuring the group and not an artefact of the encoding. -/
theorem marginEnergy_rare_absent : marginEnergy (rareWeight 0) rareField = 0 := by
  rw [marginEnergy_rare_eq]
  norm_num

/-- **The square-root law: no Lipschitz constant in the frequency exists.**  For every proposed
constant there is a frequency at which the standard deviation contributed by the rare population
exceeds that constant times its frequency.  The influence of a rare ancestry group on a
variance-based calibration report is not proportional to how rare it is; the exponent is one
half, and it is forced by the contamination geometry rather than by any pathology of the
example. -/
theorem rare_subpopulation_not_lipschitz (bound : ℝ) (hbound : 0 < bound) :
    ∃ rare : ℝ, 0 < rare ∧ rare < 1 ∧
      bound * rare < Real.sqrt (marginEnergy (rareWeight rare) rareField) := by
  refine ⟨1 / (2 * (1 + bound ^ 2)), ?_, ?_, ?_⟩
  · positivity
  · rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg bound]
  · rw [marginEnergy_rare_eq]
    set rare : ℝ := 1 / (2 * (1 + bound ^ 2)) with hrare
    have hpos : 0 < rare := by rw [hrare]; positivity
    have hsmall : (1 + bound ^ 2) * rare = 1 / 2 := by
      rw [hrare]
      field_simp
    have hgap : (bound * rare) ^ 2 < rare * (1 - rare) := by nlinarith
    calc
      bound * rare = Real.sqrt ((bound * rare) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ < Real.sqrt (rare * (1 - rare)) := Real.sqrt_lt_sqrt (sq_nonneg _) hgap

end RareSubpopulation

/-! ## Budget and noise are conjugate, not reciprocal

A recalibration with a bounded coefficient is a clipped inverse: on a spectral mode of root gain
`g` it keeps the fraction `(1 - Λ g)` of the error, clipped at zero, and the worst mode decides.
A modulus of continuity instead asks how large a source can hide below a noise level.  The two
are traded against each other by a Legendre-type calibration, and the reciprocal dictionary
`ε = 1/Λ` is not the trade: the witness below has budgeted error `0` where the reciprocal reading
predicts `1`.
-/

section BudgetConjugacy

/-- Residual error left on one spectral mode by a recalibration of bounded coefficient, in root
coordinates: root source times the clipped surviving fraction.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite expression. -/
noncomputable def clippedModeError (rootSource rootGain budget : ℝ) : ℝ :=
  rootSource * max 0 (1 - budget * rootGain)

/-- **The zero-budget value, pinned.**  With no correction allowed the whole source survives, so
the budget scale is anchored at the uncorrected error rather than at zero. -/
@[simp] theorem clippedModeError_zero_budget (rootSource rootGain : ℝ) :
    clippedModeError rootSource rootGain 0 = rootSource := by
  unfold clippedModeError
  norm_num

/-- **The clip is a floor at zero, named.**  Past the budget at which a mode is fully corrected
the expression does not go negative and start crediting the correction: it stops at zero.  A
consumer that removes the clip would find over-correction paying for itself, which is the defect
the `max` exists to prevent. -/
theorem clippedModeError_beyond_full_correction (rootSource rootGain budget : ℝ)
    (hclip : 1 ≤ budget * rootGain) :
    clippedModeError rootSource rootGain budget = 0 := by
  unfold clippedModeError
  rw [max_eq_left (by linarith)]
  ring

/-- **The Legendre lower bound, always true.**  A mode hiding below the noise level leaves at
least its source minus the budget spent reaching it.  This is the half of the budget-to-noise
dictionary that survives, and it is a conjugate relation: source minus budget times noise, not
source evaluated at a reciprocal.

"Always true" is now literal. The statement carried a fourth premise
`hclip : budget * noise ≤ 1`, restricting it to budgets that have not yet clipped; a scan of
the kernel-accepted proof term found `hclip` occurring nowhere, and it cannot be needed --
past the clip both sides only move further apart, since the left side goes negative while the
right side floors at zero.  The premise has been removed, and the bound holds at every
budget. -/
theorem clippedModeError_ge_conjugate (rootSource rootGain budget noise : ℝ)
    (hsource : 0 ≤ rootSource) (hbudget : 0 ≤ budget) (hgain : rootGain ≤ noise) :
    rootSource * (1 - budget * noise) ≤ clippedModeError rootSource rootGain budget := by
  unfold clippedModeError
  have hmono : budget * rootGain ≤ budget * noise := mul_le_mul_of_nonneg_left hgain hbudget
  have hle : 1 - budget * noise ≤ max 0 (1 - budget * rootGain) :=
    le_trans (by linarith) (le_max_right 0 (1 - budget * rootGain))
  exact mul_le_mul_of_nonneg_left hle hsource

/-- **The reciprocal dictionary fails, at full strength.**  A single mode of root source one and
root gain `1/2`, at budget `2`, is fully corrected: its budgeted error is zero.  The modulus of
continuity read at the reciprocal noise level `1/2` reports the whole source, one.  So budgeted
error is not the modulus evaluated at the reciprocal of the budget, and no constant repairs the
identification -- the gap here is the entire quantity.  Budget and noise are conjugate variables;
only the Legendre inequality above transfers. -/
theorem clippedModeError_ne_modulus_at_reciprocal :
    clippedModeError 1 (1 / 2) 2 = 0 ∧ (1 : ℝ) / 2 ≤ 1 / 2 ∧ (0 : ℝ) ≠ 1 := by
  refine ⟨?_, le_refl _, ?_⟩
  · unfold clippedModeError
    norm_num
  · norm_num

/-- Worst-mode residual error of a bounded-coefficient recalibration over a finite spectrum.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite maximum. -/
noncomputable def spectrumBudgetedError {Mode : Type*} [Fintype Mode] [Nonempty Mode]
    (rootSource rootGain : Mode → ℝ) (budget : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i ↦ clippedModeError (rootSource i) (rootGain i) budget)

/-- **The zero-budget spectrum value, pinned.**  With no correction allowed the worst mode keeps
its whole source. -/
theorem spectrumBudgetedError_zero_budget {Mode : Type*} [Fintype Mode] [Nonempty Mode]
    (rootSource rootGain : Mode → ℝ) :
    spectrumBudgetedError rootSource rootGain 0 =
      Finset.univ.sup' Finset.univ_nonempty rootSource := by
  unfold spectrumBudgetedError
  simp

/-- **The Legendre bound for a whole spectrum.**  Whatever the budget, the worst-mode error is at
least the source of any mode hiding below the noise level, less the budget spent reaching it.  So
the conjugate trade is not an artefact of looking at one mode: it is the general lower bound, and
it is the only half of the reciprocal dictionary that survives. -/
theorem spectrumBudgetedError_ge_conjugate {Mode : Type*} [Fintype Mode] [Nonempty Mode]
    (rootSource rootGain : Mode → ℝ) (budget noise : ℝ) (mode : Mode)
    (hsource : 0 ≤ rootSource mode) (hbudget : 0 ≤ budget)
    (hgain : rootGain mode ≤ noise) :
    rootSource mode * (1 - budget * noise) ≤
      spectrumBudgetedError rootSource rootGain budget :=
  le_trans
    (clippedModeError_ge_conjugate (rootSource mode) (rootGain mode) budget noise hsource hbudget
      hgain)
    (Finset.le_sup' (fun i ↦ clippedModeError (rootSource i) (rootGain i) budget)
      (Finset.mem_univ mode))

end BudgetConjugacy

end Descent.Blindness

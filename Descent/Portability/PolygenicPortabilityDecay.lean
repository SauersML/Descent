/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusPortabilityDecay

assert_below Descent.Decision Descent.Program

/-!
# Polygenic portability decay

A polygenic score sums tag loci `i` with weights `w_i`, and the trait sums causal loci `j` with
effects `β_j`.  A source and a target population split from one ancestor `T` ago.  How much of
the score's expected squared correlation with the trait survives in the target?

The model is the one of `TwoLocusPortabilityDecay`: the NOTE1 low-order moment system
`H/DD/Dz/pi2`, the corpus split instruction, then one corpus epoch of
`augmentedLowOrderLDGenerator` with drift `c_S, c_T` and no migration or mutation.  Each
tag–causal pair `p = (i, j)` runs that history under the common demographic rates, with its own
recombination rate `ρ^p` in every deme (`withRecombination`) and its own ancestral moment vector.
The score coefficient of the pair is `a_p = w_i β_j` (`pairCoefficient`).

The score statistic is a ratio of expectations, `E[C_S C_T] / E[V_S G_T]`.  Here
`C = ∑_p a_p D^p` is the score–trait covariance, `V = ∑_i w_i² π^i` the score variance and
`G = ∑_j β_j² π^j` the genetic variance.  With linkage equilibrium inside the tag panel and
inside the causal set, `E[V_S G_T] = ∑_p a_p² E[π^i_S π^j_T]` is a sum of corpus pair
coordinates.  The covariance product has diagonal terms `a_p² E[D^p_S D^p_T]`, which are corpus
pair coordinates, and cross terms `a_p a_q E[D^p_S D^q_T]` between different pairs.

## Main results

- `scoreMoment_DD`, `scoreMoment_pi2`: the diagonal linkage signal is
  `e^{-(c_S + c_T) T} ∑_p a_p² E[D_p²](0) e^{-r_p T}` with `r_p = (ρ^p_S + ρ^p_T)/2`
  (`pairRate`), and the heterozygosity moment is `e^{-(c_S + c_T) T}` times its ancestral value.
- `scorePortabilityRatio_eq`: without cross terms the target-to-source ratio is
  `polygenicDecay ω r T = ∑_p ω_p e^{-r_p T}`, the corpus pairwise decay terms weighted by the
  signal shares `ω_p = a_p² E[D_p²](0) / ∑_q a_q² E[D_q²](0)` (`pairShare`, `sum_pairShare`).
  Drift cancels: it multiplies every pair's numerator and denominator by one common factor.
- `scorePortabilityRatio_antitone_duration`, `scorePortabilityRatio_antitone_recombination`: with
  nonnegative ancestral `E[D²]`, the ratio decreases in the split time and in every pairwise
  recombination rate.
- `tendsto_scorePortabilityRatio_atTop`: as `T → ∞` the ratio tends to the coverage floor
  `∑_{p : r_p = 0} ω_p` (`coverageFloor`), the signal share of the pairs that recombine in
  neither deme (`pairRate_eq_zero_iff`).
- `crossScorePortabilityRatio_eq`: with cross terms the ratio is
  `∑_{p, q} Ω_{pq} e^{-r_{pq} T}` (`crossPolygenicDecay`), with
  `Ω_{pq} = a_p a_q E[D_p D_q](0) / ∑ a a E[D D](0)` (`crossShare`) and
  `r_{pq} = (ρ^p_S + ρ^q_T)/2` (`crossRate`).
- `crossScorePortabilityRatio_eq_diagonal_add`: what survives beyond the diagonal is exactly the
  off-diagonal sum `∑_{p ≠ q} Ω_{pq} e^{-r_{pq} T}`.
- `crossScorePortabilityRatio_eq_of_uncorrelated`: if the ancestral linkage covariance of every
  two different pairs vanishes, the full ratio is the diagonal ratio, and the clean law holds.
- `crossScorePortabilityRatio_rankOne`: for a deterministic ancestral state,
  `E[D_p D_q](0) = x_p x_q`, the ratio factors as
  `(∑_p ν_p e^{-(ρ^p_S/2) T}) (∑_q ν_q e^{-(ρ^q_T/2) T})` with the signed signal shares
  `ν_p = a_p x_p / ∑ a x` (`signalShare`).  Its floor is the product of the covered signed shares
  (`tendsto_polygenicDecay_mul_atTop`).
- `cancellingDecay_zero`, `cancellingDecay_log_two`, `not_antitoneOn_cancellingDecay`: for
  correlated pairs both the monotonicity and the bound by one fail.  Signed shares `2` and `-1`
  at recombination rates `0` and `2` give `1` at the split and `9/4` at `T = log 2`.

## Significance

After divergence a polygenic score keeps a signal-weighted mean of the two-locus decays of its
tag–causal pairs.  Drift cancels whatever the two drift rates are, as it does for one pair.  The
part that no divergence time removes is the share of the signal carried by pairs at zero
recombination, that is, by causal variants the panel tags exactly.  Portability decays toward
causal-variant coverage, not toward zero.

The clean law needs uncorrelated linkage between different pairs, the case of pairs whose
linkage values are independent with mean zero.  Otherwise the cross terms survive, each at the
mean of two pair rates.  When every signed share is nonnegative the law stays monotone
(`crossPolygenicDecay_antitone_duration`), and for one recombination profile in both demes the
floor of a deterministic state is the square of the covered signed share.  When pair signals
partly cancel, the decay of a cancelling pair raises portability, even above its source value.

## The mechanism

After the split, and with no migration, the two demes evolve independently given the split
state.  Each deme's linkage decays at its own rate `c + ρ/2`, and a cross moment of the two demes
decays at the sum of the two rates.  The corpus row of `DD(S, T)` records exactly that rate,
`c_S + c_T + (ρ_S + ρ_T)/2`.  The cross moment of pair `p` in the source and pair `q` in the
target is read as the `DD(S, T)` coordinate of the history whose recombination rate is `ρ^p` in
the source and `ρ^q` in the target (`mixedRecombination`, `crossPairMoment`).  That reading is
the modeling step of this module; for `p = q` it is the corpus pair coordinate itself.

## Scope

The source reference is the split-time value, as in `TwoLocusPortabilityDecay`.  The score
variances use linkage equilibrium inside the tag panel and inside the causal set.  Migration and
mutation are zero after the split.

## Empirical status

None.  The bodies here are algebra on finite sums of corpus moment coordinates and of real
exponentials.  No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PolygenicPortabilityDecay

open Descent.Coalescent Descent.Portability.TwoLocusPortabilityDecay

noncomputable section

/-! ## The weighted decay law -/

section WeightedDecay

variable {P : Type*} [Fintype P]

/-- **The weighted portability decay** `∑_p s_p e^{-r_p T}`: one corpus pairwise decay term per
index, weighted by its share.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of real exponentials. -/
def polygenicDecay (share rate : P → ℝ) (duration : ℝ) : ℝ :=
  ∑ index, share index * portabilityDecay (rate index) duration

/-- **The coverage floor** `∑_{p : r_p = 0} s_p`: the share carried by the indices at zero rate.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of shares. -/
def coverageFloor (share rate : P → ℝ) : ℝ :=
  ∑ index, (if rate index = 0 then share index else 0)

/-- At the split the weighted decay is the total share. -/
theorem polygenicDecay_zero_duration (share rate : P → ℝ) :
    polygenicDecay share rate 0 = ∑ index, share index := by
  simp only [polygenicDecay, portabilityDecay, mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **The weighted decay decreases with the split time.**

Assumes: nonnegative shares and nonnegative rates. -/
theorem polygenicDecay_antitone_duration {share rate : P → ℝ}
    (hshare : ∀ index, 0 ≤ share index) (hrate : ∀ index, 0 ≤ rate index) :
    Antitone (polygenicDecay share rate) := by
  intro earlier later hlater
  simp only [polygenicDecay]
  exact Finset.sum_le_sum fun index _ ↦ mul_le_mul_of_nonneg_left
    (portabilityDecay_antitone_duration (hrate index) hlater) (hshare index)

/-- **The weighted decay decreases in every rate.**

Assumes: nonnegative shares and `0 ≤ duration`. -/
theorem polygenicDecay_antitone_rate {share : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    {duration : ℝ} (hduration : 0 ≤ duration) :
    Antitone fun (rate : P → ℝ) ↦ polygenicDecay share rate duration := by
  intro slower faster hle
  simp only [polygenicDecay]
  exact Finset.sum_le_sum fun index _ ↦ mul_le_mul_of_nonneg_left
    (portabilityDecay_antitone_rate hduration (hle index)) (hshare index)

/-- **The weighted decay tends to its coverage floor.**  An index at zero rate keeps its share,
and every other term is lost.

Assumes: nonnegative rates. -/
theorem tendsto_polygenicDecay_atTop {share rate : P → ℝ} (hrate : ∀ index, 0 ≤ rate index) :
    Filter.Tendsto (polygenicDecay share rate) Filter.atTop
      (nhds (coverageFloor share rate)) := by
  have hterm : ∀ index ∈ (Finset.univ : Finset P),
      Filter.Tendsto (fun duration ↦ share index * portabilityDecay (rate index) duration)
        Filter.atTop (nhds (if rate index = 0 then share index else 0)) := by
    intro index _
    rcases (hrate index).eq_or_lt with hzero | hpos
    · rw [if_pos hzero.symm, ← hzero]
      simp only [portabilityDecay_zero_rate, mul_one]
      exact tendsto_const_nhds
    · rw [if_neg hpos.ne']
      have hlimit := (tendsto_portabilityDecay_atTop hpos).const_mul (share index)
      rwa [mul_zero] at hlimit
  have hsum := tendsto_finset_sum Finset.univ hterm
  exact hsum

/-- The coverage floor is nonnegative.

Assumes: nonnegative shares. -/
theorem coverageFloor_nonneg {share : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    (rate : P → ℝ) : 0 ≤ coverageFloor share rate := by
  rw [coverageFloor]
  refine Finset.sum_nonneg fun index _ ↦ ?_
  split_ifs
  · exact hshare index
  · exact le_rfl

/-- **The coverage floor is at most the total share.**

Assumes: nonnegative shares. -/
theorem coverageFloor_le_sum {share : P → ℝ} (hshare : ∀ index, 0 ≤ share index)
    (rate : P → ℝ) : coverageFloor share rate ≤ ∑ index, share index := by
  rw [coverageFloor]
  refine Finset.sum_le_sum fun index _ ↦ ?_
  split_ifs
  · exact le_rfl
  · exact hshare index

/-- **The weighted decay over ordered pairs of indices**, `∑_{p, q} s_{pq} e^{-r_{pq} T}`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of real exponentials. -/
def crossPolygenicDecay (share rate : P → P → ℝ) (duration : ℝ) : ℝ :=
  ∑ first, ∑ second, share first second * portabilityDecay (rate first second) duration

/-- The weighted decay over ordered pairs is the weighted decay over the product index. -/
theorem crossPolygenicDecay_eq_polygenicDecay (share rate : P → P → ℝ) (duration : ℝ) :
    crossPolygenicDecay share rate duration
      = polygenicDecay (fun (pairs : P × P) ↦ share pairs.1 pairs.2)
          (fun (pairs : P × P) ↦ rate pairs.1 pairs.2) duration := by
  simp only [crossPolygenicDecay, polygenicDecay, Fintype.sum_prod_type]

/-- **The weighted decay over ordered pairs decreases with the split time.**

Assumes: nonnegative shares and nonnegative rates. -/
theorem crossPolygenicDecay_antitone_duration {share rate : P → P → ℝ}
    (hshare : ∀ first second, 0 ≤ share first second)
    (hrate : ∀ first second, 0 ≤ rate first second) :
    Antitone (crossPolygenicDecay share rate) := by
  intro earlier later hlater
  rw [crossPolygenicDecay_eq_polygenicDecay, crossPolygenicDecay_eq_polygenicDecay]
  exact polygenicDecay_antitone_duration (fun pairs ↦ hshare pairs.1 pairs.2)
    (fun pairs ↦ hrate pairs.1 pairs.2) hlater

/-- **The weighted decay over ordered pairs tends to its coverage floor.**

Assumes: nonnegative rates. -/
theorem tendsto_crossPolygenicDecay_atTop {share rate : P → P → ℝ}
    (hrate : ∀ first second, 0 ≤ rate first second) :
    Filter.Tendsto (crossPolygenicDecay share rate) Filter.atTop
      (nhds (coverageFloor (fun (pairs : P × P) ↦ share pairs.1 pairs.2)
        (fun (pairs : P × P) ↦ rate pairs.1 pairs.2))) := by
  have hlimit := tendsto_polygenicDecay_atTop
    (share := fun (pairs : P × P) ↦ share pairs.1 pairs.2)
    (rate := fun (pairs : P × P) ↦ rate pairs.1 pairs.2) fun pairs ↦ hrate pairs.1 pairs.2
  exact hlimit.congr fun duration ↦
    (crossPolygenicDecay_eq_polygenicDecay share rate duration).symm

/-- **The diagonal and the survivors.**  The weighted decay over ordered pairs is its diagonal
sum plus the sum over the ordered pairs of different indices. -/
theorem crossPolygenicDecay_eq_diagonal_add [DecidableEq P] (share rate : P → P → ℝ)
    (duration : ℝ) :
    crossPolygenicDecay share rate duration
      = ∑ index, share index index * portabilityDecay (rate index index) duration
        + ∑ first, ∑ second, (if first = second then 0
          else share first second * portabilityDecay (rate first second) duration) := by
  rw [crossPolygenicDecay, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun first _ ↦ ?_
  have hsplit : ∑ second, share first second * portabilityDecay (rate first second) duration
      = ∑ second, ((if first = second then
            share first second * portabilityDecay (rate first second) duration else 0)
          + (if first = second then 0
            else share first second * portabilityDecay (rate first second) duration)) :=
    Finset.sum_congr rfl fun second _ ↦ by split_ifs <;> ring
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ first,
    if_pos (Finset.mem_univ first)]

/-- The decay at a sum of two rates is the product of the two decays. -/
theorem portabilityDecay_add (first second duration : ℝ) :
    portabilityDecay (first + second) duration
      = portabilityDecay first duration * portabilityDecay second duration := by
  rw [portabilityDecay, portabilityDecay, portabilityDecay, ← Real.exp_add]
  congr 1
  ring

/-- **Rank-one shares factor the law.**  With shares `ν_p ν_q` and rates `(ρ^S_p + ρ^T_q)/2`, the
weighted decay over ordered pairs is the product of the two one-index decays at half rates. -/
theorem crossPolygenicDecay_rankOne (signal sourceRate targetRate : P → ℝ) (duration : ℝ) :
    crossPolygenicDecay (fun first second ↦ signal first * signal second)
        (fun first second ↦ (sourceRate first + targetRate second) / 2) duration
      = polygenicDecay signal (fun index ↦ sourceRate index / 2) duration
        * polygenicDecay signal (fun index ↦ targetRate index / 2) duration := by
  rw [crossPolygenicDecay, polygenicDecay, polygenicDecay, Finset.sum_mul]
  refine Finset.sum_congr rfl fun first _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun second _ ↦ ?_
  rw [add_div, portabilityDecay_add]
  ring

/-- **The floor of a rank-one law is the product of the covered signed shares.**

Assumes: nonnegative rates in both demes. -/
theorem tendsto_polygenicDecay_mul_atTop {signal sourceRate targetRate : P → ℝ}
    (hsource : ∀ index, 0 ≤ sourceRate index) (htarget : ∀ index, 0 ≤ targetRate index) :
    Filter.Tendsto
      (fun duration ↦ polygenicDecay signal (fun index ↦ sourceRate index / 2) duration
        * polygenicDecay signal (fun index ↦ targetRate index / 2) duration)
      Filter.atTop
      (nhds (coverageFloor signal (fun index ↦ sourceRate index / 2)
        * coverageFloor signal (fun index ↦ targetRate index / 2))) :=
  (tendsto_polygenicDecay_atTop (share := signal)
      fun index ↦ div_nonneg (hsource index) zero_le_two).mul
    (tendsto_polygenicDecay_atTop (share := signal)
      fun index ↦ div_nonneg (htarget index) zero_le_two)

end WeightedDecay

/-! ## Cancelling pair signals -/

/-- **The sign-cancelling two-pair law.**  Rank-one shares from the signed signal shares `2` and
`-1`, with recombination rates `0` and `2` in both demes.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of real exponentials. -/
def cancellingDecay (duration : ℝ) : ℝ :=
  crossPolygenicDecay (fun first second : Fin 2 ↦ ![(2 : ℝ), -1] first * ![(2 : ℝ), -1] second)
    (fun first second : Fin 2 ↦ (![(0 : ℝ), 2] first + ![(0 : ℝ), 2] second) / 2) duration

/-- The sign-cancelling law is the square of one signed decay sum. -/
theorem cancellingDecay_eq (duration : ℝ) :
    cancellingDecay duration
      = polygenicDecay ![(2 : ℝ), -1] (fun index ↦ ![(0 : ℝ), 2] index / 2) duration
        * polygenicDecay ![(2 : ℝ), -1] (fun index ↦ ![(0 : ℝ), 2] index / 2) duration :=
  crossPolygenicDecay_rankOne ![(2 : ℝ), -1] ![(0 : ℝ), 2] ![(0 : ℝ), 2] duration

/-- At the split the sign-cancelling law is `1`. -/
theorem cancellingDecay_zero : cancellingDecay 0 = 1 := by
  rw [cancellingDecay_eq, polygenicDecay_zero_duration]
  norm_num [Fin.sum_univ_two]

/-- **At `T = log 2` the sign-cancelling law is `9/4`**, above its value at the split. -/
theorem cancellingDecay_log_two : cancellingDecay (Real.log 2) = 9 / 4 := by
  have hhalf : portabilityDecay 1 (Real.log 2) = 2⁻¹ := by
    rw [portabilityDecay, one_mul, Real.exp_neg, Real.exp_log two_pos]
  rw [cancellingDecay_eq, polygenicDecay]
  norm_num [Fin.sum_univ_two, portabilityDecay_zero_rate, hhalf]

/-- **Correlated pair signals break the monotone law.**  The sign-cancelling law is not antitone
in the split time. -/
theorem not_antitoneOn_cancellingDecay : ¬ AntitoneOn cancellingDecay (Set.Ici 0) := by
  intro hanti
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hle := hanti Set.left_mem_Ici (Set.mem_Ici.mpr hlog) hlog
  rw [cancellingDecay_zero, cancellingDecay_log_two] at hle
  norm_num at hle

/-! ## The rates of one pair -/

variable {D : ℕ}

/-- **The two-locus rates of one tag–causal pair**: the demographic rates of `rates`, with the
recombination profile `profile` of the pair in every deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A record update of the corpus rates. -/
def withRecombination (rates : ManyDemeLDRates D) (profile : Fin D → ℝ)
    (hprofile : ∀ deme, 0 ≤ profile deme) : ManyDemeLDRates D where
  coalescence := rates.coalescence
  migration := rates.migration
  mutation := rates.mutation
  recombination := profile
  coalescence_pos := rates.coalescence_pos
  migration_nonneg := rates.migration_nonneg
  migration_self := rates.migration_self
  mutation_nonneg := rates.mutation_nonneg
  recombination_nonneg := hprofile

/-- The pair rates keep the demographic drift. -/
theorem withRecombination_coalescence (rates : ManyDemeLDRates D) (profile : Fin D → ℝ)
    (hprofile : ∀ deme, 0 ≤ profile deme) :
    (withRecombination rates profile hprofile).coalescence = rates.coalescence :=
  rfl

/-- The pair rates carry the recombination profile of the pair. -/
theorem withRecombination_recombination (rates : ManyDemeLDRates D) (profile : Fin D → ℝ)
    (hprofile : ∀ deme, 0 ≤ profile deme) :
    (withRecombination rates profile hprofile).recombination = profile :=
  rfl

/-- **The drift factor** `e^{-(c_S + c_T) T}`, common to every pair of the score.

Empirical status: NOT AN EMPIRICAL CLAIM.  A real exponential. -/
def driftFactor (rates : ManyDemeLDRates D) (parent child : Fin D) (duration : ℝ) : ℝ :=
  Real.exp (-(rates.coalescence parent + rates.coalescence child) * duration)

/-- The drift factor is positive. -/
theorem driftFactor_pos (rates : ManyDemeLDRates D) (parent child : Fin D) (duration : ℝ) :
    0 < driftFactor rates parent child duration :=
  Real.exp_pos _

/-- **The cross-population linkage covariance of one pair** is the drift factor times the decay
term of the pair times the ancestral `E[D²]`.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem splitHistoryState_withRecombination_DD (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (profile : Fin D → ℝ)
    (hprofile : ∀ deme, 0 ≤ profile deme) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState (withRecombination rates profile hprofile) parent child hduration ancestral
        (some (.DD parent child))
      = driftFactor rates parent child duration
        * portabilityDecay ((profile parent + profile child) / 2) duration
        * ancestral (some (.DD parent parent)) := by
  rw [splitHistoryState_DD (withRecombination rates profile hprofile) hmigration hmutation hne
      hduration ancestral, withRecombination_coalescence, withRecombination_recombination,
    driftFactor, portabilityDecay, ← Real.exp_add]
  congr 2
  ring

/-- **The cross-population heterozygosity product of one pair** is the drift factor times the
ancestral `E[π^A π^B]`.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem splitHistoryState_withRecombination_pi2 (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (profile : Fin D → ℝ)
    (hprofile : ∀ deme, 0 ≤ profile deme) {parent child : Fin D} (hne : parent ≠ child)
    {duration : ℝ} (hduration : 0 ≤ duration) (ancestral : AffineLowOrderLDCoordinate D → ℝ) :
    splitHistoryState (withRecombination rates profile hprofile) parent child hduration ancestral
        (some (.pi2 parent parent child child))
      = driftFactor rates parent child duration
        * ancestral (some (.pi2 parent parent parent parent)) := by
  rw [splitHistoryState_pi2 (withRecombination rates profile hprofile) hmigration hmutation hne
      hduration ancestral, withRecombination_coalescence, driftFactor]

/-! ## Tag–causal pairs -/

variable {ι κ : Type*}

/-- **The score coefficient of a tag–causal pair**, `a_{ij} = w_i β_j`: the score weight of the
tag times the effect of the causal locus.

Empirical status: NOT AN EMPIRICAL CLAIM.  A product of two real numbers. -/
def pairCoefficient (weight : ι → ℝ) (effect : κ → ℝ) (pair : ι × κ) : ℝ :=
  weight pair.1 * effect pair.2

/-- **The decay rate of a tag–causal pair**, `r_{ij} = (ρ^{ij}_S + ρ^{ij}_T)/2`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A mean of two rates. -/
def pairRate (recombination : ι × κ → Fin D → ℝ) (parent child : Fin D) (pair : ι × κ) : ℝ :=
  (recombination pair parent + recombination pair child) / 2

/-- The decay rate of a pair is nonnegative.

Assumes: nonnegative recombination rates. -/
theorem pairRate_nonneg {recombination : ι × κ → Fin D → ℝ}
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (parent child : Fin D)
    (pair : ι × κ) : 0 ≤ pairRate recombination parent child pair :=
  div_nonneg (add_nonneg (hrecombination pair parent) (hrecombination pair child)) zero_le_two

/-- **Faster recombination gives a faster pair decay.**

Assumes: `slower ≤ faster` pointwise. -/
theorem pairRate_le {slower faster : ι × κ → Fin D → ℝ} (hle : slower ≤ faster)
    (parent child : Fin D) (pair : ι × κ) :
    pairRate slower parent child pair ≤ pairRate faster parent child pair := by
  have hparent := hle pair parent
  have hchild := hle pair child
  simp only [pairRate]
  linarith

/-- **A pair keeps its share exactly when it recombines in neither deme.**

Assumes: nonnegative recombination rates. -/
theorem pairRate_eq_zero_iff {recombination : ι × κ → Fin D → ℝ}
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (parent child : Fin D)
    (pair : ι × κ) :
    pairRate recombination parent child pair = 0
      ↔ recombination pair parent = 0 ∧ recombination pair child = 0 := by
  have hparent := hrecombination pair parent
  have hchild := hrecombination pair child
  simp only [pairRate]
  constructor
  · intro hzero
    constructor <;> linarith
  · rintro ⟨hzeroParent, hzeroChild⟩
    rw [hzeroParent, hzeroChild]
    norm_num

/-- **The mixed recombination profile of an ordered pair of pairs**: the second pair's rate in
the target deme `child`, and the first pair's rate in every other deme.

Empirical status: NOT AN EMPIRICAL CLAIM.  A case split between two rate profiles. -/
def mixedRecombination (recombination : ι × κ → Fin D → ℝ) (child : Fin D)
    (first second : ι × κ) (deme : Fin D) : ℝ :=
  if deme = child then recombination second deme else recombination first deme

/-- The mixed recombination profile is nonnegative.

Assumes: nonnegative recombination rates. -/
theorem mixedRecombination_nonneg {recombination : ι × κ → Fin D → ℝ}
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (child : Fin D)
    (first second : ι × κ) (deme : Fin D) :
    0 ≤ mixedRecombination recombination child first second deme := by
  rw [mixedRecombination]
  split_ifs
  · exact hrecombination second deme
  · exact hrecombination first deme

/-- **The decay rate of an ordered pair of pairs**, `r_{pq} = (ρ^p_S + ρ^q_T)/2`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A mean of two rates. -/
def crossRate (recombination : ι × κ → Fin D → ℝ) (parent child : Fin D)
    (first second : ι × κ) : ℝ :=
  (recombination first parent + recombination second child) / 2

/-- On the diagonal the decay rate of an ordered pair of pairs is the decay rate of the pair. -/
theorem crossRate_self (recombination : ι × κ → Fin D → ℝ) (parent child : Fin D)
    (pair : ι × κ) :
    crossRate recombination parent child pair pair = pairRate recombination parent child pair :=
  rfl

/-- **The cross-population cross moment of two pairs**, `E[D^p_S D^q_T]`: the `DD(S, T)`
coordinate of the split history with the first pair's recombination rate in the source and the
second pair's in the target, from the joint ancestral vector of the two pairs.

Empirical status: NOT AN EMPIRICAL CLAIM.  A moment coordinate of a corpus split history. -/
def crossPairMoment (rates : ManyDemeLDRates D) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (parent child : Fin D)
    {duration : ℝ} (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (first second : ι × κ) : ℝ :=
  splitHistoryState
    (withRecombination rates (mixedRecombination recombination child first second)
      (mixedRecombination_nonneg hrecombination child first second))
    parent child hduration (crossAncestral first second) (some (.DD parent child))

/-- **The cross moment of two pairs decays at the mean of their two rates**, times the drift
factor.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem crossPairMoment_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (first second : ι × κ) :
    crossPairMoment rates recombination hrecombination parent child hduration crossAncestral
        first second
      = driftFactor rates parent child duration
        * portabilityDecay (crossRate recombination parent child first second) duration
        * crossAncestral first second (some (.DD parent parent)) := by
  rw [crossPairMoment, splitHistoryState_withRecombination_DD rates hmigration hmutation _ _ hne
      hduration, crossRate, mixedRecombination, mixedRecombination, if_neg hne, if_pos rfl]

/-! ## The score without cross terms -/

variable [Fintype ι] [Fintype κ]

/-- **A score moment of the split history**, `∑_{ij} (w_i β_j)² m^{ij}(T)`: the coordinate `m`
of every pair's own split history, weighted by the squared score coefficient.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of moment coordinates. -/
def scoreMoment (rates : ManyDemeLDRates D) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) (parent child : Fin D) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (coordinate : AffineLowOrderLDCoordinate D) : ℝ :=
  ∑ pair, pairCoefficient weight effect pair ^ 2
    * splitHistoryState (withRecombination rates (recombination pair) (hrecombination pair))
        parent child hduration (ancestral pair) coordinate

/-- **An ancestral score moment**, `∑_{ij} (w_i β_j)² m^{ij}(0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of moment coordinates. -/
def ancestralScoreMoment (weight : ι → ℝ) (effect : κ → ℝ)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (coordinate : AffineLowOrderLDCoordinate D) : ℝ :=
  ∑ pair, pairCoefficient weight effect pair ^ 2 * ancestral pair coordinate

/-- **The polygenic portability ratio without cross terms**: the diagonal linkage signal
`∑_p a_p² E[D^p_S D^p_T]` over the heterozygosity moment, relative to the same ratio at the split.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of score moments. -/
def scorePortabilityRatio (rates : ManyDemeLDRates D) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) (parent child : Fin D) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  scoreMoment rates recombination hrecombination weight effect parent child hduration ancestral
      (some (.DD parent child))
    / scoreMoment rates recombination hrecombination weight effect parent child hduration
      ancestral (some (.pi2 parent parent child child))
    / (ancestralScoreMoment weight effect ancestral (some (.DD parent parent))
      / ancestralScoreMoment weight effect ancestral (some (.pi2 parent parent parent parent)))

/-- **The signal share of a tag–causal pair**, `ω_p = a_p² E[D_p²](0) / ∑_q a_q² E[D_q²](0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of ancestral score moments. -/
def pairShare (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ) (pair : ι × κ) : ℝ :=
  pairCoefficient weight effect pair ^ 2 * ancestral pair (some (.DD parent parent))
    / ancestralScoreMoment weight effect ancestral (some (.DD parent parent))

/-- **The diagonal linkage signal of the score** is the drift factor times
`∑_p a_p² E[D_p²](0) e^{-r_p T}`.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem scoreMoment_DD (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ) :
    scoreMoment rates recombination hrecombination weight effect parent child hduration ancestral
        (some (.DD parent child))
      = driftFactor rates parent child duration
        * ∑ pair, pairCoefficient weight effect pair ^ 2
          * ancestral pair (some (.DD parent parent))
          * portabilityDecay (pairRate recombination parent child pair) duration := by
  rw [scoreMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun pair _ ↦ ?_
  rw [splitHistoryState_withRecombination_DD rates hmigration hmutation (recombination pair)
    (hrecombination pair) hne hduration (ancestral pair), pairRate]
  ring

/-- **The heterozygosity moment of the score** is the drift factor times its ancestral value.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem scoreMoment_pi2 (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ) :
    scoreMoment rates recombination hrecombination weight effect parent child hduration ancestral
        (some (.pi2 parent parent child child))
      = driftFactor rates parent child duration
        * ancestralScoreMoment weight effect ancestral
          (some (.pi2 parent parent parent parent)) := by
  rw [scoreMoment, ancestralScoreMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun pair _ ↦ ?_
  rw [splitHistoryState_withRecombination_pi2 rates hmigration hmutation (recombination pair)
    (hrecombination pair) hne hduration (ancestral pair)]
  ring

/-- **The polygenic portability decay law.**  Without cross terms, the target-to-source ratio of
the expected squared correlation of the score is `∑_p ω_p e^{-r_p T}`: the corpus pairwise decay
terms weighted by the signal shares of the pairs.  Drift does not enter.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral heterozygosity
moment of the score. -/
theorem scorePortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration) (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect ancestral
      (some (.pi2 parent parent parent parent)) ≠ 0) :
    scorePortabilityRatio rates recombination hrecombination weight effect parent child hduration
        ancestral
      = polygenicDecay (pairShare weight effect parent ancestral)
          (pairRate recombination parent child) duration := by
  rw [scorePortabilityRatio, scoreMoment_DD rates hmigration hmutation recombination
      hrecombination weight effect hne hduration ancestral,
    scoreMoment_pi2 rates hmigration hmutation recombination hrecombination weight effect hne
      hduration ancestral,
    mul_div_mul_left _ _ (driftFactor_pos rates parent child duration).ne',
    div_div_div_cancel_right₀, polygenicDecay, Finset.sum_div]
  · refine Finset.sum_congr rfl fun pair _ ↦ ?_
    rw [pairShare]
    ring
  · exact hheterozygosity

/-- **The signal shares sum to one.**

Assumes: a nonzero ancestral linkage signal of the score. -/
theorem sum_pairShare (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hsignal : ancestralScoreMoment weight effect ancestral (some (.DD parent parent)) ≠ 0) :
    ∑ pair, pairShare weight effect parent ancestral pair = 1 := by
  simp only [pairShare]
  rw [← Finset.sum_div]
  exact div_self hsignal

/-- **The signal shares are nonnegative.**

Assumes: a nonnegative ancestral `E[D²]` for every pair. -/
theorem pairShare_nonneg (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hlinkage : ∀ pair, 0 ≤ ancestral pair (some (.DD parent parent))) (pair : ι × κ) :
    0 ≤ pairShare weight effect parent ancestral pair := by
  rw [pairShare, ancestralScoreMoment]
  exact div_nonneg (mul_nonneg (sq_nonneg _) (hlinkage pair))
    (Finset.sum_nonneg fun other _ ↦ mul_nonneg (sq_nonneg _) (hlinkage other))

/-- **Polygenic portability decreases with the split time.**

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral heterozygosity moment
of the score, a nonnegative ancestral `E[D²]` for every pair, and `0 ≤ earlier ≤ later`. -/
theorem scorePortabilityRatio_antitone_duration (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect ancestral
      (some (.pi2 parent parent parent parent)) ≠ 0)
    (hlinkage : ∀ pair, 0 ≤ ancestral pair (some (.DD parent parent))) {earlier later : ℝ}
    (hearlier : 0 ≤ earlier) (hlater : earlier ≤ later) :
    scorePortabilityRatio rates recombination hrecombination weight effect parent child
        (hearlier.trans hlater) ancestral
      ≤ scorePortabilityRatio rates recombination hrecombination weight effect parent child
        hearlier ancestral := by
  rw [scorePortabilityRatio_eq rates hmigration hmutation recombination hrecombination weight
      effect hne (hearlier.trans hlater) ancestral hheterozygosity,
    scorePortabilityRatio_eq rates hmigration hmutation recombination hrecombination weight
      effect hne hearlier ancestral hheterozygosity]
  exact polygenicDecay_antitone_duration
    (pairShare_nonneg weight effect parent ancestral hlinkage)
    (pairRate_nonneg hrecombination parent child) hlater

/-- **Polygenic portability decreases in every pairwise recombination rate.**

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral heterozygosity moment
of the score, a nonnegative ancestral `E[D²]` for every pair, and `slower ≤ faster` pointwise. -/
theorem scorePortabilityRatio_antitone_recombination (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) {slower faster : ι × κ → Fin D → ℝ}
    (hslower : ∀ pair deme, 0 ≤ slower pair deme) (hfaster : ∀ pair deme, 0 ≤ faster pair deme)
    (hle : slower ≤ faster) (weight : ι → ℝ) (effect : κ → ℝ) {parent child : Fin D}
    (hne : parent ≠ child) {duration : ℝ} (hduration : 0 ≤ duration)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect ancestral
      (some (.pi2 parent parent parent parent)) ≠ 0)
    (hlinkage : ∀ pair, 0 ≤ ancestral pair (some (.DD parent parent))) :
    scorePortabilityRatio rates faster hfaster weight effect parent child hduration ancestral
      ≤ scorePortabilityRatio rates slower hslower weight effect parent child hduration
        ancestral := by
  rw [scorePortabilityRatio_eq rates hmigration hmutation faster hfaster weight effect hne
      hduration ancestral hheterozygosity,
    scorePortabilityRatio_eq rates hmigration hmutation slower hslower weight effect hne
      hduration ancestral hheterozygosity]
  exact polygenicDecay_antitone_rate (pairShare_nonneg weight effect parent ancestral hlinkage)
    hduration fun pair ↦ pairRate_le hle parent child pair

/-- **Polygenic portability tends to the coverage floor.**  As the split time grows, the ratio
tends to the signal share carried by the pairs at zero recombination.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral heterozygosity
moment of the score. -/
theorem tendsto_scorePortabilityRatio_atTop (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child)
    (ancestral : ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect ancestral
      (some (.pi2 parent parent parent parent)) ≠ 0) :
    Filter.Tendsto
      (fun duration : ℝ ↦ scorePortabilityRatio rates recombination hrecombination weight effect
        parent child (le_max_right duration 0) ancestral)
      Filter.atTop
      (nhds (coverageFloor (pairShare weight effect parent ancestral)
        (pairRate recombination parent child))) := by
  have hagree : ∀ duration : ℝ, 0 ≤ duration →
      polygenicDecay (pairShare weight effect parent ancestral)
          (pairRate recombination parent child) duration
        = scorePortabilityRatio rates recombination hrecombination weight effect parent child
          (le_max_right duration 0) ancestral := by
    intro duration hduration
    rw [scorePortabilityRatio_eq rates hmigration hmutation recombination hrecombination weight
      effect hne (le_max_right duration 0) ancestral hheterozygosity, max_eq_left hduration]
  refine (tendsto_polygenicDecay_atTop (pairRate_nonneg hrecombination parent child)).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with duration hduration
  exact hagree duration hduration

/-! ## Cross terms between pairs -/

/-- **The full cross-population linkage signal of the score**,
`E[C_S C_T] = ∑_{p, q} a_p a_q E[D^p_S D^q_T]`, cross terms included.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of moment coordinates. -/
def crossScoreLinkage (rates : ManyDemeLDRates D) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) (parent child : Fin D) {duration : ℝ} (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  ∑ first, ∑ second, pairCoefficient weight effect first * pairCoefficient weight effect second
    * crossPairMoment rates recombination hrecombination parent child hduration crossAncestral
      first second

/-- **The full ancestral linkage signal of the score**, `∑_{p, q} a_p a_q E[D_p D_q](0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite weighted sum of moment coordinates. -/
def ancestralCrossScoreLinkage (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  ∑ first, ∑ second, pairCoefficient weight effect first * pairCoefficient weight effect second
    * crossAncestral first second (some (.DD parent parent))

/-- **The signal share of an ordered pair of pairs**,
`Ω_{pq} = a_p a_q E[D_p D_q](0) / ∑ a a E[D D](0)`.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of ancestral score moments. -/
def crossShare (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (first second : ι × κ) : ℝ :=
  pairCoefficient weight effect first * pairCoefficient weight effect second
      * crossAncestral first second (some (.DD parent parent))
    / ancestralCrossScoreLinkage weight effect parent crossAncestral

/-- **The polygenic portability ratio with cross terms**: the full linkage signal over the
heterozygosity moment, relative to the same ratio at the split.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of two ratios of score moments. -/
def crossScorePortabilityRatio (rates : ManyDemeLDRates D) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) (parent child : Fin D) {duration : ℝ} (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ) : ℝ :=
  crossScoreLinkage rates recombination hrecombination weight effect parent child hduration
      crossAncestral
    / scoreMoment rates recombination hrecombination weight effect parent child hduration
      (fun pair ↦ crossAncestral pair pair) (some (.pi2 parent parent child child))
    / (ancestralCrossScoreLinkage weight effect parent crossAncestral
      / ancestralScoreMoment weight effect (fun pair ↦ crossAncestral pair pair)
        (some (.pi2 parent parent parent parent)))

/-- **The full linkage signal of the score** is the drift factor times
`∑_{p, q} a_p a_q E[D_p D_q](0) e^{-r_{pq} T}`.

Assumes: no migration, no mutation, and `parent ≠ child`. -/
theorem crossScoreLinkage_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ) :
    crossScoreLinkage rates recombination hrecombination weight effect parent child hduration
        crossAncestral
      = driftFactor rates parent child duration
        * ∑ first, ∑ second, pairCoefficient weight effect first
          * pairCoefficient weight effect second
          * crossAncestral first second (some (.DD parent parent))
          * portabilityDecay (crossRate recombination parent child first second) duration := by
  rw [crossScoreLinkage, Finset.mul_sum]
  refine Finset.sum_congr rfl fun first _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun second _ ↦ ?_
  rw [crossPairMoment_eq rates hmigration hmutation recombination hrecombination hne hduration
    crossAncestral first second]
  ring

/-- **The polygenic portability law with cross terms.**  The target-to-source ratio of the score
is `∑_{p, q} Ω_{pq} e^{-r_{pq} T}`, one corpus decay term for every ordered pair of pairs at the
mean of the source rate of the first and the target rate of the second.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral heterozygosity
moment of the score. -/
theorem crossScorePortabilityRatio_eq (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect (fun pair ↦ crossAncestral pair pair)
      (some (.pi2 parent parent parent parent)) ≠ 0) :
    crossScorePortabilityRatio rates recombination hrecombination weight effect parent child
        hduration crossAncestral
      = crossPolygenicDecay (crossShare weight effect parent crossAncestral)
          (crossRate recombination parent child) duration := by
  rw [crossScorePortabilityRatio, crossScoreLinkage_eq rates hmigration hmutation recombination
      hrecombination weight effect hne hduration crossAncestral,
    scoreMoment_pi2 rates hmigration hmutation recombination hrecombination weight effect hne
      hduration,
    mul_div_mul_left _ _ (driftFactor_pos rates parent child duration).ne',
    div_div_div_cancel_right₀, crossPolygenicDecay, Finset.sum_div]
  · refine Finset.sum_congr rfl fun first _ ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun second _ ↦ ?_
    rw [crossShare]
    ring
  · exact hheterozygosity

/-- **What survives beyond the diagonal.**  The full ratio is the diagonal sum
`∑_p Ω_{pp} e^{-r_p T}` plus the cross terms `Ω_{pq} e^{-r_{pq} T}` of the ordered pairs of
different pairs.

Assumes: no migration, no mutation, `parent ≠ child`, and a nonzero ancestral heterozygosity
moment of the score. -/
theorem crossScorePortabilityRatio_eq_diagonal_add [DecidableEq ι] [DecidableEq κ]
    (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect (fun pair ↦ crossAncestral pair pair)
      (some (.pi2 parent parent parent parent)) ≠ 0) :
    crossScorePortabilityRatio rates recombination hrecombination weight effect parent child
        hduration crossAncestral
      = ∑ pair, crossShare weight effect parent crossAncestral pair pair
          * portabilityDecay (pairRate recombination parent child pair) duration
        + ∑ first, ∑ second, (if first = second then 0
          else crossShare weight effect parent crossAncestral first second
            * portabilityDecay (crossRate recombination parent child first second) duration) := by
  rw [crossScorePortabilityRatio_eq rates hmigration hmutation recombination hrecombination weight
      effect hne hduration crossAncestral hheterozygosity,
    crossPolygenicDecay_eq_diagonal_add (crossShare weight effect parent crossAncestral)
      (crossRate recombination parent child) duration]
  rfl

/-- **The clean law holds for uncorrelated pairs.**  If the ancestral linkage covariance
`E[D_p D_q](0)` vanishes for every two different pairs, the full ratio is the ratio without cross
terms, whose closed form is `scorePortabilityRatio_eq`.

Assumes: no migration, no mutation, `parent ≠ child`, and `E[D_p D_q](0) = 0` for `p ≠ q`. -/
theorem crossScorePortabilityRatio_eq_of_uncorrelated (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (huncorrelated : ∀ first second, first ≠ second →
      crossAncestral first second (some (.DD parent parent)) = 0) :
    crossScorePortabilityRatio rates recombination hrecombination weight effect parent child
        hduration crossAncestral
      = scorePortabilityRatio rates recombination hrecombination weight effect parent child
        hduration (fun pair ↦ crossAncestral pair pair) := by
  have hsignal : crossScoreLinkage rates recombination hrecombination weight effect parent child
        hduration crossAncestral
      = scoreMoment rates recombination hrecombination weight effect parent child hduration
        (fun pair ↦ crossAncestral pair pair) (some (.DD parent child)) := by
    rw [crossScoreLinkage, scoreMoment]
    refine Finset.sum_congr rfl fun first _ ↦ ?_
    have hvanish : ∀ second ∈ (Finset.univ : Finset (ι × κ)), second ≠ first →
        pairCoefficient weight effect first * pairCoefficient weight effect second
          * crossPairMoment rates recombination hrecombination parent child hduration
            crossAncestral first second = 0 := by
      intro second _ hsecond
      rw [crossPairMoment_eq rates hmigration hmutation recombination hrecombination hne
        hduration crossAncestral, huncorrelated first second hsecond.symm, mul_zero, mul_zero]
    rw [Finset.sum_eq_single_of_mem first (Finset.mem_univ first) hvanish,
      crossPairMoment_eq rates hmigration hmutation recombination hrecombination hne hduration
        crossAncestral,
      splitHistoryState_withRecombination_DD rates hmigration hmutation (recombination first)
        (hrecombination first) hne hduration, crossRate]
    ring
  have hreference : ancestralCrossScoreLinkage weight effect parent crossAncestral
      = ancestralScoreMoment weight effect (fun pair ↦ crossAncestral pair pair)
        (some (.DD parent parent)) := by
    rw [ancestralCrossScoreLinkage, ancestralScoreMoment]
    refine Finset.sum_congr rfl fun first _ ↦ ?_
    have hvanish : ∀ second ∈ (Finset.univ : Finset (ι × κ)), second ≠ first →
        pairCoefficient weight effect first * pairCoefficient weight effect second
          * crossAncestral first second (some (.DD parent parent)) = 0 := by
      intro second _ hsecond
      rw [huncorrelated first second hsecond.symm, mul_zero]
    rw [Finset.sum_eq_single_of_mem first (Finset.mem_univ first) hvanish]
    ring
  rw [crossScorePortabilityRatio, scorePortabilityRatio, hsignal, hreference]

/-- **The signed signal share of a pair under a deterministic ancestral state**,
`ν_p = a_p x_p / ∑_q a_q x_q`, with `x_p` the ancestral linkage of the pair.

Empirical status: NOT AN EMPIRICAL CLAIM.  A ratio of finite sums. -/
def signalShare (weight : ι → ℝ) (effect : κ → ℝ) (linkage : ι × κ → ℝ) (pair : ι × κ) : ℝ :=
  pairCoefficient weight effect pair * linkage pair
    / ∑ other, pairCoefficient weight effect other * linkage other

/-- **A deterministic ancestral state gives rank-one shares.**  If `E[D_p D_q](0) = x_p x_q`, the
share of an ordered pair of pairs is `ν_p ν_q`.

Assumes: `E[D_p D_q](0) = x_p x_q` for every two pairs. -/
theorem crossShare_rankOne (weight : ι → ℝ) (effect : κ → ℝ) (parent : Fin D)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ) (linkage : ι × κ → ℝ)
    (hrankOne : ∀ first second,
      crossAncestral first second (some (.DD parent parent)) = linkage first * linkage second)
    (first second : ι × κ) :
    crossShare weight effect parent crossAncestral first second
      = signalShare weight effect linkage first * signalShare weight effect linkage second := by
  have hreference : ancestralCrossScoreLinkage weight effect parent crossAncestral
      = (∑ other, pairCoefficient weight effect other * linkage other) ^ 2 := by
    rw [ancestralCrossScoreLinkage, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun one _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun another _ ↦ ?_
    rw [hrankOne]
    ring
  rw [crossShare, hreference, hrankOne, signalShare, signalShare]
  ring

/-- **The rank-one portability law.**  For a deterministic ancestral state the ratio with cross
terms is `(∑_p ν_p e^{-(ρ^p_S/2) T}) (∑_q ν_q e^{-(ρ^q_T/2) T})`.

Assumes: no migration, no mutation, `parent ≠ child`, a nonzero ancestral heterozygosity moment
of the score, and `E[D_p D_q](0) = x_p x_q` for every two pairs. -/
theorem crossScorePortabilityRatio_rankOne (rates : ManyDemeLDRates D)
    (hmigration : ∀ source target, rates.migration source target = 0)
    (hmutation : ∀ deme, rates.mutation deme = 0) (recombination : ι × κ → Fin D → ℝ)
    (hrecombination : ∀ pair deme, 0 ≤ recombination pair deme) (weight : ι → ℝ)
    (effect : κ → ℝ) {parent child : Fin D} (hne : parent ≠ child) {duration : ℝ}
    (hduration : 0 ≤ duration)
    (crossAncestral : ι × κ → ι × κ → AffineLowOrderLDCoordinate D → ℝ)
    (hheterozygosity : ancestralScoreMoment weight effect (fun pair ↦ crossAncestral pair pair)
      (some (.pi2 parent parent parent parent)) ≠ 0) (linkage : ι × κ → ℝ)
    (hrankOne : ∀ first second,
      crossAncestral first second (some (.DD parent parent)) = linkage first * linkage second) :
    crossScorePortabilityRatio rates recombination hrecombination weight effect parent child
        hduration crossAncestral
      = polygenicDecay (signalShare weight effect linkage)
          (fun pair ↦ recombination pair parent / 2) duration
        * polygenicDecay (signalShare weight effect linkage)
          (fun pair ↦ recombination pair child / 2) duration := by
  have hshare : crossShare weight effect parent crossAncestral
      = fun first second ↦ signalShare weight effect linkage first
        * signalShare weight effect linkage second := by
    funext first second
    exact crossShare_rankOne weight effect parent crossAncestral linkage hrankOne first second
  rw [crossScorePortabilityRatio_eq rates hmigration hmutation recombination hrecombination weight
      effect hne hduration crossAncestral hheterozygosity, hshare]
  exact crossPolygenicDecay_rankOne (signalShare weight effect linkage)
    (fun pair ↦ recombination pair parent) (fun pair ↦ recombination pair child) duration

end

end Descent.Portability.PolygenicPortabilityDecay

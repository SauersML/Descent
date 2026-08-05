/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Tactic
import Descent.Core.Ratios

namespace Descent

/-!
# The ancestral recombination graph: coalescence competing with recombination

Hudson, *Properties of a neutral allele model with intragenic recombination* (Theor. Popul.
Biol. 23, 183-201, 1983), and Griffiths and Marjoram after him, replace the coalescent tree
by a graph: going backwards, lineages coalesce at the Kingman rate AND split, because a
recombinant lineage has two parents, one for each side of the breakpoint.  With `k` lineages
and scaled recombination rate `ρ`, the two rates are

  coalescence   `d_k = k(k-1)/2`,        recombination   `k ρ / 2`,

and every classical two-locus quantity comes from how those two compete.

That competition is the same one `Descent.Coalescent.CompetingRates` handles for the
coalescent's own clocks -- the first event is exponential at the total rate, and which kind
it is has probability proportional to its rate -- so it needs no new machinery, only the
rates.  What this file adds is those rates, the fact that `ρ = 0` returns Kingman exactly,
and the classical pairwise answer.

**The pairwise answer.**  For two lineages the coalescence rate is `1` and the recombination
rate is `ρ`, so the two loci reach their common ancestor without an intervening
recombination with probability `1/(1+ρ)`.  That single number is the backbone of two-locus
theory: it is the probability of identity by descent at both loci, and it decays in `ρ`
exactly as linkage disequilibrium does.

## Main results

- `argEventRate`: `d_k + kρ/2`, the total rate of the next event.
- `argEventRate_zero_recomb`: at `ρ = 0` it is `deathRate` -- Kingman is the `ρ = 0` fibre.
- `recombFirstProb`: the chance the next event is a recombination.
- `pairCoalesceFirstProb_eq`: **Hudson's `1/(1+ρ)`** for a pair.
- `pairCoalesceFirstProb_antitone`: more recombination, less joint identity.
- `tendsto_pairCoalesceFirstProb`: and it vanishes as `ρ → ∞`, the two loci becoming
  independent.
-/

namespace Coalescent

open Filter

/-- The recombination rate with `k` lineages: each lineage splits at rate `ρ/2`.

Empirical status: THIS IS THE MODEL.  `ρ = 4 N_e r` is the scaled rate, and the `1/2` is the
same time-unit convention that makes the per-pair coalescence rate `1`; see
`Descent.Program.Conventions`. -/
noncomputable def recombRate (k : ℕ) (rho : ℝ) : ℝ := Descent.Core.halfLineageRate k rho

/-- The total rate of the next event in the ancestral recombination graph: a coalescence or
a recombination, whichever comes first. -/
noncomputable def argEventRate (k : ℕ) (rho : ℝ) : ℝ := deathRate k + recombRate k rho

/-- **Kingman is the `ρ = 0` fibre.**  With no recombination the graph is a tree and the
event rate is `deathRate` exactly, so `Descent.Coalescent`'s whole development is the
zero-recombination case of the ARG. -/
@[simp] theorem argEventRate_zero_recomb (k : ℕ) : argEventRate k 0 = deathRate k := by
  unfold argEventRate recombRate Descent.Core.halfLineageRate
  ring

theorem recombRate_nonneg {k : ℕ} {rho : ℝ} (h : 0 ≤ rho) : 0 ≤ recombRate k rho := by
  unfold recombRate Descent.Core.halfLineageRate
  positivity

theorem argEventRate_pos {k : ℕ} (hk : 2 ≤ k) {rho : ℝ} (hrho : 0 ≤ rho) :
    0 < argEventRate k rho := by
  have hd := deathRate_pos hk
  have hr := recombRate_nonneg (k := k) hrho
  unfold argEventRate
  linarith

/-- The chance that the next event is a recombination rather than a coalescence: rates in
proportion, as competing exponentials always are.

Empirical status: DERIVED from `recombRate` and `argEventRate`.  For competing exponentials
the probability that one fires first is its rate over the total, which is a fact about
exponentials and not about a genome; the empirical content is in `recombRate`, whose own
marker carries it. -/
noncomputable def recombFirstProb (k : ℕ) (rho : ℝ) : ℝ :=
  recombRate k rho / argEventRate k rho

/-- The complementary chance, that the next event is a coalescence.

Empirical status: DERIVED from `deathRate` and `argEventRate`, by the same competing-
exponential argument as `recombFirstProb`, of which this is the complement. -/
noncomputable def coalesceFirstProb (k : ℕ) (rho : ℝ) : ℝ :=
  deathRate k / argEventRate k rho

/-- The two exhaust the possibilities: something happens, and it is one or the other. -/
theorem recombFirstProb_add_coalesceFirstProb {k : ℕ} (hk : 2 ≤ k) {rho : ℝ}
    (hrho : 0 ≤ rho) : recombFirstProb k rho + coalesceFirstProb k rho = 1 := by
  have hpos := argEventRate_pos hk hrho
  have hne : argEventRate k rho ≠ 0 := ne_of_gt hpos
  unfold recombFirstProb coalesceFirstProb
  rw [div_add_div_same, div_eq_one_iff_eq hne]
  unfold argEventRate recombRate Descent.Core.halfLineageRate
  ring

/-- **Hudson's `1/(1+ρ)`.**  Two lineages coalesce at rate `1` and recombine at rate `ρ`, so
they reach a common ancestor with no intervening recombination with probability `1/(1+ρ)`.

This is the backbone of two-locus theory: the probability of joint identity by descent, and
the shape in which linkage disequilibrium decays with distance. -/
theorem pairCoalesceFirstProb_eq {rho : ℝ} (hrho : 0 ≤ rho) :
    coalesceFirstProb 2 rho = 1 / (1 + rho) := by
  have hne : (1 : ℝ) + rho ≠ 0 := by linarith
  unfold coalesceFirstProb argEventRate recombRate Descent.Core.halfLineageRate
  rw [deathRate_two]
  push_cast
  field_simp

/-- More recombination, less joint identity: the pairwise probability falls in `ρ`. -/
theorem pairCoalesceFirstProb_antitone {rho rho' : ℝ} (h0 : 0 ≤ rho) (h : rho ≤ rho') :
    coalesceFirstProb 2 rho' ≤ coalesceFirstProb 2 rho := by
  have h0' : 0 ≤ rho' := le_trans h0 h
  rw [pairCoalesceFirstProb_eq h0, pairCoalesceFirstProb_eq h0']
  gcongr

/-- **Free recombination decouples the loci.**  As `ρ → ∞` the chance of coalescing before a
recombination vanishes: the two sides of the breakpoint have independent genealogies, which
is the limit in which two-locus statistics carry no linkage information at all. -/
theorem tendsto_pairCoalesceFirstProb :
    Tendsto (fun rho : ℝ => coalesceFirstProb 2 rho) atTop (nhds 0) := by
  have hcongr : ∀ᶠ rho : ℝ in atTop, coalesceFirstProb 2 rho = 1 / (1 + rho) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with rho hrho
    exact pairCoalesceFirstProb_eq hrho
  have hlim : Tendsto (fun rho : ℝ => 1 / (1 + rho)) atTop (nhds 0) := by
    have h : Tendsto (fun rho : ℝ => 1 + rho) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 tendsto_id
    exact h.inv_tendsto_atTop.congr fun rho => (one_div _).symm
  exact hlim.congr' (hcongr.mono fun rho h => h.symm)

/-- At zero recombination the pair coalesces first with certainty -- there is nothing else
that can happen, and the ARG is Kingman's tree. -/
@[simp] theorem pairCoalesceFirstProb_zero : coalesceFirstProb 2 0 = 1 := by
  rw [pairCoalesceFirstProb_eq le_rfl]
  norm_num

end Coalescent

end Descent

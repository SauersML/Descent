/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.ObservationalCeiling
import Descent.Pangenome.HaplotypeGluing

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

open Descent.Pangenome.HaplotypeGluing

/-!
# Marginal frequencies cannot decide whether phantom recombinants exist

`Descent.Pangenome.HaplotypeGluing` builds the finite local-to-global core: a two-chart
panel, the compatible matching families it admits, and the **gluing defect** — locally
observed, overlap-compatible haplotypes that no observed chromosome carries. It proves the
defect is exactly the graph-splicing language's phantom set, and that classical two-locus
`D` is the same obstruction measured probabilistically.

This file adds the impossibility that makes the defect an epistemic object rather than a
bookkeeping one. Take the observation to be what marginal data reports: **which local
pieces were seen on each side**, and nothing about which pieces were seen *together*. Then
`marginals_probeBlindness` exhibits two panels with identical marginals, one gluing and one
not, so `ProbeBlindness.no_criterion_of_factors` says no statistic computed from marginal
frequencies decides whether phantom recombinants exist — not a better estimator, not a
hierarchy of tests, not any function of that data.

## Why this is the expected answer and still worth proving

Haplotype phase is exactly the information marginals discard, so a reader may find the
conclusion obvious. What is not obvious, and is what the theorem supplies, is the SHAPE:
the failure is a witness pair rather than a variance, so it does not shrink with sample
size and it is not repaired by a smarter estimator. The two panels below are the smallest
possible instance — two chromosomes over two biallelic sites — and they already saturate
it. Any claim to detect phantom recombinants from allele frequencies must therefore be
reading something other than the marginals, and can be asked what.

## Relation to `Descent.Conditionals.LocalToGlobalCoherence`

That file proves the asymptotic, probabilistic form of the same shape: local law systems
agreeing on every bounded-radius union of cover elements, one globally realizable and one
at total-variation distance `1/2 - sqrt 5 / 6` from every global law. It cannot be imported
here — it sits above `Descent.Blindness` in the layer order — and it is a different
theorem, not this one in disguise: its separation is quantitative and asymptotic and needs
Ramanujan graphs, while this one is exact, finite and needs four haplotypes. What they
share is the moral, and the corpus now proves it at both resolutions: agreement on
overlaps is not realizability, and no amount of local data closes the gap.
-/

/-- The **crossover closure condition** on a set of observed two-locus haplotypes: every
left piece seen with something, joined to every right piece seen with something, is itself
seen. This is `HasGluing` for the trivial-overlap panel, and `crossoverClosed_iff_hasGluing`
proves it. -/
def CrossoverClosed (observed : Set (Fin 2 × Fin 2)) : Prop :=
  ∀ first ∈ observed, ∀ second ∈ observed, (first.1, second.2) ∈ observed

/-- The two-chart panel carried by a set of observed haplotypes, with a trivial overlap:
the two sites are read independently and every pair is compatible. -/
def trivialOverlapPanel (observed : Set (Fin 2 × Fin 2)) :
    TwoChartPanel observed (Fin 2) (Fin 2) Unit where
  left := fun haplotype ↦ haplotype.val.1
  right := fun haplotype ↦ haplotype.val.2
  leftOverlap := fun _piece ↦ ()
  rightOverlap := fun _piece ↦ ()
  compatible := fun _haplotype ↦ rfl

/-- The panel's observed sections are the observed haplotypes themselves. -/
theorem observedSections_trivialOverlapPanel (observed : Set (Fin 2 × Fin 2)) :
    (trivialOverlapPanel observed).observedSections = observed := by
  ext haplotype
  constructor
  · rintro ⟨⟨pair, hpair⟩, rfl⟩
    exact hpair
  · intro hhaplotype
    exact ⟨⟨haplotype, hhaplotype⟩, rfl⟩

/-- The panel's matching families are exactly the crossovers of observed pieces. -/
theorem mem_matchingClosure_trivialOverlapPanel (observed : Set (Fin 2 × Fin 2))
    (pair : Fin 2 × Fin 2) :
    pair ∈ (trivialOverlapPanel observed).matchingClosure ↔
      (∃ first ∈ observed, first.1 = pair.1) ∧ (∃ second ∈ observed, second.2 = pair.2) := by
  constructor
  · rintro ⟨-, ⟨⟨first, hfirst⟩, hleft⟩, ⟨⟨second, hsecond⟩, hright⟩⟩
    exact ⟨⟨first, hfirst, hleft⟩, ⟨second, hsecond, hright⟩⟩
  · rintro ⟨⟨first, hfirst, hleft⟩, ⟨second, hsecond, hright⟩⟩
    exact ⟨rfl, ⟨⟨first, hfirst⟩, hleft⟩, ⟨⟨second, hsecond⟩, hright⟩⟩

/-- **The crossover condition is the gluing axiom.** The set-level statement and
`HaplotypeGluing.HasGluing` are the same property, so the impossibility below is about the
adopted development's own object and not a lookalike. -/
theorem crossoverClosed_iff_hasGluing (observed : Set (Fin 2 × Fin 2)) :
    CrossoverClosed observed ↔ (trivialOverlapPanel observed).HasGluing := by
  constructor
  · intro hclosed pair hpair
    rw [observedSections_trivialOverlapPanel]
    obtain ⟨⟨first, hfirst, hleft⟩, ⟨second, hsecond, hright⟩⟩ :=
      (mem_matchingClosure_trivialOverlapPanel observed pair).mp hpair
    have hcrossover := hclosed first hfirst second hsecond
    rwa [hleft, hright] at hcrossover
  · intro hgluing first hfirst second hsecond
    have hmatching : (first.1, second.2) ∈ (trivialOverlapPanel observed).matchingClosure :=
      (mem_matchingClosure_trivialOverlapPanel observed (first.1, second.2)).mpr
        ⟨⟨first, hfirst, rfl⟩, ⟨second, hsecond, rfl⟩⟩
    have := hgluing hmatching
    rwa [observedSections_trivialOverlapPanel] at this

/-- **What marginal data reports**: which allele was seen at the left site and which at the
right site, with no record of which were seen together. -/
def chartMarginals (observed : Set (Fin 2 × Fin 2)) : Set (Fin 2) × Set (Fin 2) :=
  (Prod.fst '' observed, Prod.snd '' observed)

/-- The two chromosomes `00` and `11`: both alleles appear at both sites, and no chromosome
carries the `01` combination. -/
def couplingPanel : Set (Fin 2 × Fin 2) := {haplotype | haplotype.1 = haplotype.2}

/-- All four haplotypes. -/
def saturatedPanel : Set (Fin 2 × Fin 2) := Set.univ

/-- Both alleles are seen at both sites in the coupling panel, so its marginals are full. -/
theorem chartMarginals_couplingPanel : chartMarginals couplingPanel = (Set.univ, Set.univ) := by
  refine Prod.ext ?_ ?_ <;> ext allele <;>
    exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨(allele, allele), rfl, rfl⟩⟩

/-- The saturated panel has full marginals too — the same ones. -/
theorem chartMarginals_saturatedPanel :
    chartMarginals saturatedPanel = (Set.univ, Set.univ) := by
  refine Prod.ext ?_ ?_ <;> ext allele <;>
    exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨(allele, allele), trivial, rfl⟩⟩

/-- The saturated panel glues: everything is observed, so nothing is missing. -/
theorem crossoverClosed_saturatedPanel : CrossoverClosed saturatedPanel :=
  fun _first _hfirst _second _hsecond ↦ trivial

/-- The coupling panel does not glue: `0` on the left and `1` on the right are each
observed, and their crossover is the phantom recombinant. -/
theorem not_crossoverClosed_couplingPanel : ¬ CrossoverClosed couplingPanel := by
  intro hclosed
  have hcrossover : (0 : Fin 2) = 1 := hclosed (0, 0) rfl (1, 1) rfl
  exact absurd hcrossover (by decide)

/-- **Marginal frequencies cannot decide gluing.** Two panels with identical marginal data,
one closed under crossover and one carrying a phantom recombinant. By
`ProbeBlindness.no_criterion_of_factors`, no statistic computed from marginals — of any
logical complexity, deterministic or randomized — decides whether phantom recombinants
exist. -/
def marginals_probeBlindness : ProbeBlindness chartMarginals CrossoverClosed where
  positive := saturatedPanel
  negative := couplingPanel
  same_data := by
    rw [chartMarginals_saturatedPanel, chartMarginals_couplingPanel]
  holds := crossoverClosed_saturatedPanel
  fails := not_crossoverClosed_couplingPanel

/-- **The impossibility, stated.** No predicate on marginal data decides crossover closure,
hence none decides whether the gluing defect of `Descent.Pangenome.HaplotypeGluing` is
empty. -/
theorem no_marginal_criterion_for_gluing :
    ¬ ∃ decideValue : Set (Fin 2) × Set (Fin 2) → Prop,
      ∀ observed : Set (Fin 2 × Fin 2),
        CrossoverClosed observed ↔ decideValue (chartMarginals observed) :=
  marginals_probeBlindness.no_criterion

/-- **The same impossibility against the adopted vocabulary.** Read through
`crossoverClosed_iff_hasGluing`, no marginal statistic decides `HasGluing` for the panel a
set of haplotypes carries — which is the epistemic content of the gluing defect. -/
theorem no_marginal_criterion_for_hasGluing :
    ¬ ∃ decideValue : Set (Fin 2) × Set (Fin 2) → Prop,
      ∀ observed : Set (Fin 2 × Fin 2),
        (trivialOverlapPanel observed).HasGluing ↔ decideValue (chartMarginals observed) := by
  rintro ⟨decideValue, hdecide⟩
  exact no_marginal_criterion_for_gluing
    ⟨decideValue, fun observed ↦
      (crossoverClosed_iff_hasGluing observed).trans (hdecide observed)⟩

end Descent.Blindness

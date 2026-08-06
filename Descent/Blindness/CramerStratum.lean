/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

noncomputable section

open scoped BigOperators

/-!
# The Cramér stratum, and why atomic laws are outside it

Several results in this development are proved only for coordinate laws satisfying
**Cramér's condition (C)** — the Edgeworth machinery behind the Insertion Lemma needs
it, and the blindness statement it supports is scoped to laws that have it. This file
records what that condition excludes, because the exclusion decides which genotype
data types the surrounding theory may be applied to and the answer is not the one a
casual reading gives.

## The condition

For a coordinate law with characteristic function `φ`, Cramér's condition is

  `limsup_{|t| → ∞} |φ(t)| < 1`.

It says the characteristic function is eventually bounded away from modulus one. A law
with a density has it; a law that returns to modulus one at arbitrarily large
frequencies does not.

We work with `|φ(t)|²` rather than `|φ(t)|`, and write it without complex numbers as

  `charFnSq w a t = ∑_u ∑_v w_u w_v cos(t (a_u - a_v))`,

which is exactly `|φ(t)|²` for the law placing weight `w_v` at value `a_v`. The two
formulations of (C) agree, since `|φ| < 1` iff `|φ|² < 1`, and the real form keeps the
proofs elementary.

## The result, and how much of it is proved here

**Every finitely supported law violates Cramér's condition — lattice or not.** The
characteristic function of a finite atomic measure is a finite exponential sum, hence
Bohr almost periodic, hence *recurrent*: it returns arbitrarily close to `φ(0) = 1` at
arbitrarily large `|t|`. So `limsup |φ| = 1`, and (C), which demands strictly less than
one, fails. The lattice/nonlattice distinction is irrelevant to this — a nonlattice
atomic law fails by recurrence rather than by periodicity, but it fails.

Two halves, with different status here:

* **Lattice atoms: proved outright.** If all gaps lie in `h ℤ` then `charFnSq` is
  *exactly* one at every `t = 2πn/h` (`charFnSq_eq_one_of_lattice`), so (C) fails with no analytic
  input at all (`not_cramer_of_lattice`). This is not a toy case: it is the
  sharpest instance the corpus has, since
  `Descent.PolygenicSpectroscopy.hardCall_arithmeticProgression_at_critical_maf`
  proves that at `q* = (2 - √2)/4` the three values of `log x²` for a hard-called
  Hardy-Weinberg locus form an exact arithmetic progression. That instance is now a
  *consumer* of this file rather than a remark about it:
  `Descent.PolygenicSpectroscopy.hardCall_not_cramer_at_critical_maf` is
  `not_cramer_of_lattice` applied to the genotype coordinate, and it is not provable in
  that file without this one — the return of `|φ|²` to one at the frequencies `2πn/h`
  has no counterpart in the spectroscopy machinery.
* **General atomic: not yet formalized.** The nonlattice atomic case needs
  Kronecker's theorem on *simultaneous* Diophantine approximation — for gaps `1` and
  `√2` one needs `t ≈ 2πm` and `t√2 ≈ 2πn` at once — and mathlib carries only the
  one-dimensional statement (`denseRange_zsmul_iff` and the `AddCircle` ergodic
  results); every `Kronecker` in mathlib is the matrix product. There is no elementary
  shortcut: the mean-value route gives
  `lim (1/2T) ∫_{-T}^{T} |φ|² = ∑_v w_v²`, which is bounded away from one and so says
  nothing about the limsup.  The repository therefore makes no general nonlattice-atomic
  theorem until the simultaneous-approximation proof is formalized; it does not accept
  recurrence as a caller-supplied theorem.

## Why this matters for genotypes

A standardized diallelic genotype takes three values, so `x²` takes three values and
`log x²` is supported on three points. The coordinate law of a hard-called locus is
therefore atomic, and by the above it is **outside the Cramér stratum at every allele
frequency** — not only at the lattice frequency where the failure is provable here.

The consequence is a scope statement, and it is the useful output of this file:
results proved on the Cramér stratum transfer to **imputed dosages**, which are
continuous per locus and so have absolutely continuous coordinate laws, and do **not**
transfer to hard calls.

Two routes that look like they should repair this do not.

* *Orientation randomization* — mixing a locus with its complementary-frequency
  reflection — is a per-coordinate operation and it does restore reflection symmetry.
  But it acts only on signs: `Descent.EpistaticChaos.reflect_standardizedGenotype`
  gives `x_reflect = -(x ∘ flip)`, so the modulus law is exactly invariant and the
  coordinate stays three-atom in `|x|`. Cramér is a condition on the modulus alone, so
  this move provably cannot touch it.
* *Mixing over an allele-frequency spectrum* does smooth the modulus, but only for the
  law of a **randomly chosen** locus. Conditional on a realized marker panel — which is
  what every estimator conditions on — each coordinate is still three-atom. The
  Edgeworth machinery acts per coordinate, so the smoothness is an averaging artifact
  across coordinates rather than a property of any coordinate.
-/

section Definition

variable {V : Type*} [Fintype V]

/-- `|φ(t)|²` for the finitely supported law placing weight `w v` at value `a v`,
written without complex numbers:
`∑_u ∑_v w_u w_v cos(t (a_u - a_v))`.

Expanding `|∑_v w_v e^{i t a_v}|²` and pairing conjugate terms gives exactly this, with the
imaginary parts cancelling because the sum is over ordered pairs both ways.

Empirical status: DERIVED. This is an algebraic identity for the squared modulus of a
characteristic function, not a modelling choice; it has no free parameter. -/
def charFnSq (w a : V → ℝ) (t : ℝ) : ℝ :=
  ∑ u, ∑ v, w u * w v * Real.cos (t * (a u - a v))

/-- **Cramér's condition (C)**, in the squared form: the squared modulus of the
characteristic function is eventually bounded away from one.

`∃ c < 1, ∃ T, ∀ |t| ≥ T, |φ(t)|² ≤ c` is the elementary rendering of
`limsup_{|t| → ∞} |φ(t)| < 1`.

Empirical status: DERIVED. A restatement of the standard analytic condition, with no
modelling content and no free parameter. -/
def CramerCondition (w a : V → ℝ) : Prop :=
  ∃ c T : ℝ, c < 1 ∧ ∀ t : ℝ, T ≤ |t| → charFnSq w a t ≤ c

/-- At `t = 0` the squared modulus is one, for any probability weighting. This is the
value the recurrence returns to. -/
theorem charFnSq_zero (w a : V → ℝ) (hw : ∑ v, w v = 1) : charFnSq w a 0 = 1 := by
  unfold charFnSq
  have hterm : ∀ u v : V, Real.cos (0 * (a u - a v)) = 1 := by
    intro u v
    rw [zero_mul, Real.cos_zero]
  simp_rw [hterm, mul_one]
  have hstep : ∀ u : V, ∑ v : V, w u * w v = w u := by
    intro u
    rw [← Finset.mul_sum, hw, mul_one]
  simp_rw [hstep]
  exact hw

end Definition

section Lattice

variable {V : Type*} [Fintype V]

/-- **A lattice law returns to modulus one at every lattice frequency.**

If every gap `a_u - a_v` lies in `h ℤ`, then at `t = 2πn/h` every cosine is one, so the
double sum collapses to `(∑ w)² = 1`. No analytic input: the whole proof is that
`cos(2πk) = 1` for integer `k`. -/
theorem charFnSq_eq_one_of_lattice (w a : V → ℝ) (hw : ∑ v, w v = 1)
    (h : ℝ) (hh : 0 < h) (hlat : ∀ u v : V, ∃ k : ℤ, a u - a v = h * k) (n : ℕ) :
    charFnSq w a (2 * Real.pi * n / h) = 1 := by
  unfold charFnSq
  have hne : h ≠ 0 := ne_of_gt hh
  have hterm : ∀ u v : V,
      Real.cos (2 * Real.pi * (n : ℝ) / h * (a u - a v)) = 1 := by
    intro u v
    obtain ⟨k, hk⟩ := hlat u v
    rw [hk]
    have hrw : 2 * Real.pi * (n : ℝ) / h * (h * (k : ℝ))
        = (((n : ℤ) * k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      field_simp
    rw [hrw]
    exact Real.cos_int_mul_two_pi _
  simp_rw [hterm, mul_one]
  have hstep : ∀ u : V, ∑ v : V, w u * w v = w u := by
    intro u
    rw [← Finset.mul_sum, hw, mul_one]
  simp_rw [hstep]
  exact hw

/-- **A lattice law violates Cramér's condition.**

The lattice frequencies `2πn/h` run off to infinity while `charFnSq` sits at exactly
one, so no eventual bound below one can hold. Proved outright, with no Diophantine
input. -/
theorem not_cramer_of_lattice (w a : V → ℝ) (hw : ∑ v, w v = 1)
    (h : ℝ) (hh : 0 < h) (hlat : ∀ u v : V, ∃ k : ℤ, a u - a v = h * k) :
    ¬ CramerCondition w a := by
  rintro ⟨c, T, hc, hbound⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  obtain ⟨n, hn⟩ := exists_nat_gt (T * h / (2 * Real.pi))
  have hlarge : T ≤ 2 * Real.pi * (n : ℝ) / h := by
    rw [le_div_iff₀ hh]
    rw [div_lt_iff₀ hpi] at hn
    linarith
  have hnonneg : (0 : ℝ) ≤ 2 * Real.pi * (n : ℝ) / h := by positivity
  have habs : T ≤ |2 * Real.pi * (n : ℝ) / h| := by
    rw [abs_of_nonneg hnonneg]
    exact hlarge
  have hone := charFnSq_eq_one_of_lattice w a hw h hh hlat n
  have hle := hbound _ habs
  rw [hone] at hle
  linarith

end Lattice

section HardCalls

/-- **A Hardy-Weinberg locus whose coordinate values are equally spaced is outside the
Cramér stratum.**

The weights are the genotype probabilities, so this is the three-point law of an actual
locus rather than an abstract atomic law. `hlat` is the lattice hypothesis in abstract
form: all gaps between coordinate values lie in `h ℤ`.

Deriving `hlat` for the specific coordinate `log x²` at the critical frequency
`q* = (2 - √2)/4` is *not* done here, and cannot be: what
`Descent.PolygenicSpectroscopy.hardCall_arithmeticProgression_at_critical_maf`
proves is the arithmetic-progression identity on the three squared standardized values;
turning that into the gap condition below requires the three logarithms, which this file
does not compute.

**It is discharged there instead, and this file is imported for that purpose.**
`Descent.PolygenicSpectroscopy.hardCall_logSquare_lattice_at_critical_maf` supplies
`hlat` for `a = log x²` with span `hardCallLatticeSpan = log ((1 - q*) / q*)`, and
`Descent.PolygenicSpectroscopy.hardCall_not_cramer_at_critical_maf` is this theorem
applied to it. So the dependency runs `PolygenicSpectroscopy → CramerStratum`, not the
other way, and the arrow above stays a citation on purpose: reversing it would be a
cycle. Do not add an import of `PolygenicSpectroscopy` here.

The general statement — that a hard call is outside the stratum at *every* polymorphic
frequency, not only where the values happen to be equally spaced — remains unformalized
until the required simultaneous-approximation theorem is proved from Mathlib primitives. -/
theorem hwe_not_cramer_of_lattice (hwe : Foundations.HardyWeinbergModel)
    (a : Foundations.DiploidGenotype → ℝ)
    (h : ℝ) (hh : 0 < h) (hlat : ∀ u v : Foundations.DiploidGenotype, ∃ k : ℤ, a u - a v = h * k) :
    ¬ CramerCondition hwe.genotypeProb a :=
  not_cramer_of_lattice _ a hwe.genotypeProb_sum h hh hlat

end HardCalls

end

end Descent.Blindness

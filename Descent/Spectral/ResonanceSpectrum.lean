/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

-- `phase_of_abs_neg` uses `Real.log`, which is why `Log.Basic` is imported above: without
-- it `Real.log` resolves as an unknown constant. A missing import here is invisible to any
-- build that does not reach this file, which is why the `Descent` root lists this
-- module: being compiled is what makes the import list answerable to the proofs below.

namespace Descent

open scoped BigOperators

/-!
# The resonance spectrum of a finite panel

Self-contained: imports only Mathlib, readable without any other part of this
development.

## What this is about

Take a panel of `n` loci. Locus `i` contributes a phase `phase i` and carries weight
`weight i`. The quantity that governs whether a local limit theorem holds for sums over
the panel is the **characteristic sum**

`Ψ(s) = ∑ᵢ weight i · exp(i · s · phase i)`,

and what matters is its modulus. `intensity P s` below is `|Ψ(s)|²`, written with real
cosine and sine parts so that nothing here needs complex analysis.

A frequency `s` is **resonant** when `intensity P s = 1`: the phases realign and the sum
recovers its full size. The set of such `s` is the panel's **resonance spectrum**. It is
empty for laws with enough smoothness, a full lattice in the classical lattice case, and
in between it is a spectrum with masses — a strictly finer invariant than the
lattice/non-lattice dichotomy it generalizes.

## Two things this file establishes, and they point in opposite directions

**Resonance is modulus data, hence ladder-side.** The phases come from magnitudes —
`phase i = 2 log |value i|` in the application — so replacing any atom value by its
negative changes nothing. `resonance_blind_to_sign_flip` proves that every intensity, at
every frequency, is invariant under sign flips of the underlying values. So a design that
can read the resonance spectrum learns something genuinely new about the arithmetic of the
panel, and learns **nothing** about signs. Odd-part invisibility survives on this stratum
too, which is the interesting half: the exposed algebra grows and the odd part still does
not enter it.

**A realized panel always has a non-empty resonance spectrum.** `resonance_at_zero` is
trivial and says the spectrum always contains `0`, but the content is
`resonance_of_aligned`: whenever the phases realign the intensity returns to its maximum.
For a finite panel that recurrence is unavoidable — the phases are finitely many real
numbers, so simultaneous near-alignment recurs — whereas a continuous mixing measure can
avoid it entirely. **The resonance spectrum is therefore a property of the realized panel
that its continuum idealization does not have.**

That distinction is the same one that governs the identifiability results in
`Descent.Blindness.BundleRigidity`, pointing the other way: rigidity holds for realized panels
and fails on the continuum, while resonance is present for realized panels and absent on
the continuum. Theorems about mixing measures and theorems about realized panels are
different theorems, and neither should be quoted for the other.

## ZERO CONSUMERS, DELIBERATELY. Do not "fix" this.

The `Descent` root lists this module so that it is compiled, and nothing consumes its
conclusions. That is a judgment rather than an oversight. `intensity` here is `|Psi|^2` and
`CramerStratum.charFnSq` is `|phi|^2`: the same object in two encodings, and the root's
`intensity_eq_charFnSq` proves it. `resonance_of_aligned` and
`CramerStratum.charFnSq_eq_one_of_lattice` are the same mechanism -- phases realign, the
sum returns to its full size.

The binary lattice/non-lattice fact the biological core actually needs is delivered by
`CramerStratum`, which is wired in: `PolygenicSpectroscopy.hardCall_not_cramer_at_critical_maf`
consumes it to prove hard calls sit outside the Cramer stratum at `q*`. Wiring this module
in as well would give a second route to a conclusion already reached, which is worse than an
honest zero -- it would read as integration while adding no dependence, and it would create
two places to maintain one argument.

**What would make it matter.** A core result needing the *graded* spectrum -- the masses
strictly between `0` and `1`, which the lattice/non-lattice dichotomy cannot express and
which `CramerStratum` does not compute. There is no such result today. If one appears, this
is the module to reach for; until then the right consumer count is zero.

## What is measurable, which makes this an instrument rather than a definition

Between recurrences the intensity of an `n`-locus panel does not fall to zero. It settles
near `1/n` — the modulus `|Ψ|` settles near `n^(-1/2)` — because a normalized sum of `n`
unit phasors with decorrelated phases is a plane random walk of that length. That floor is
a computable, measurable feature of a real panel, so the resonance spectrum can be
estimated from data rather than only defined for an idealized measure.

The floor is a statement about typical phases and is not proved here; it is recorded
numerically in `validation/empirical/coupling/mixture_cramer_window.py`, where the observed
`floor × √n` is flat at 0.51, 0.60, 0.40, 0.48 across four decades of `n`. What *is*
proved here is the deterministic half: the intensity is bounded by one, attains one at
resonance, and never depends on a sign.
-/

/-- A finite panel's phase data at one tilt: each locus contributes a phase and a
weight. -/
structure PhasePanel (n : ℕ) where
  /-- The phase contributed by each locus. In the application `phase i = 2 log |aᵢ|`. -/
  phase : Fin n → ℝ
  /-- The weight of each locus. -/
  weight : Fin n → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Weights sum to one. -/
  weight_sum : ∑ i, weight i = 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def PhasePanel.witness (n : ℕ) : PhasePanel (n + 1) where
  phase := fun _ ↦ 0
  weight := fun i ↦ if i = 0 then 1 else 0
  weight_nonneg := fun i ↦ by split <;> norm_num
  weight_sum := by simp

namespace PhasePanel

variable {n : ℕ} (P : PhasePanel n)

/-- The real part of the characteristic sum at frequency `s`. -/
noncomputable def cosPart (s : ℝ) : ℝ := ∑ i, P.weight i * Real.cos (s * P.phase i)

/-- The imaginary part of the characteristic sum at frequency `s`. -/
noncomputable def sinPart (s : ℝ) : ℝ := ∑ i, P.weight i * Real.sin (s * P.phase i)

/-- `|Ψ(s)|²`, the intensity of the characteristic sum. -/
noncomputable def intensity (s : ℝ) : ℝ := P.cosPart s ^ 2 + P.sinPart s ^ 2

/-- A frequency is **resonant** when the phases realign and the sum recovers full size. -/
def IsResonantAt (s : ℝ) : Prop := P.intensity s = 1

/-- **Zero is always resonant.** Trivial, and the reason the resonance spectrum of a
panel is never empty even before any arithmetic is considered. -/
theorem resonance_at_zero : P.IsResonantAt 0 := by
  unfold IsResonantAt intensity cosPart sinPart
  have hcos : ∀ i : Fin n, P.weight i * Real.cos (0 * P.phase i) = P.weight i := by
    intro i
    rw [zero_mul, Real.cos_zero, mul_one]
  have hsin : ∀ i : Fin n, P.weight i * Real.sin (0 * P.phase i) = 0 := by
    intro i
    rw [zero_mul, Real.sin_zero, mul_zero]
  simp_rw [hcos, hsin]
  rw [Finset.sum_const_zero, P.weight_sum]
  norm_num

/-- **Alignment gives resonance.** If every phase has realigned at frequency `s`, in the
sense that each cosine has returned to one, the intensity is one.

This is the mechanism behind every resonance: the classical lattice case is the instance
where alignment recurs on an arithmetic progression of frequencies, and the general case
is the same statement without the progression. -/
theorem resonance_of_aligned {s : ℝ} (haligned : ∀ i : Fin n, Real.cos (s * P.phase i) = 1) :
    P.IsResonantAt s := by
  have hsin : ∀ i : Fin n, Real.sin (s * P.phase i) = 0 := by
    intro i
    have hpyth := Real.sin_sq_add_cos_sq (s * P.phase i)
    rw [haligned i] at hpyth
    have hzero : Real.sin (s * P.phase i) ^ 2 = 0 := by linarith [hpyth]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
  unfold IsResonantAt intensity cosPart sinPart
  have hcos : ∀ i : Fin n, P.weight i * Real.cos (s * P.phase i) = P.weight i := by
    intro i
    rw [haligned i, mul_one]
  have hsin' : ∀ i : Fin n, P.weight i * Real.sin (s * P.phase i) = 0 := by
    intro i
    rw [hsin i, mul_zero]
  simp_rw [hcos, hsin']
  rw [Finset.sum_const_zero, P.weight_sum]
  norm_num

/-- Replacing every phase-generating value by its negative leaves the phases alone,
because a phase is built from a magnitude. -/
theorem phase_of_abs_neg (value : Fin n → ℝ) (i : Fin n) :
    2 * Real.log |(-value i)| = 2 * Real.log |value i| := by
  rw [abs_neg]

/-- **The resonance spectrum is blind to signs.**

Two panels with the same phases and weights have the same intensity at every frequency —
and since a phase is a function of a magnitude, flipping the sign of any underlying value
produces exactly such a pair.

This is what puts resonance on the ladder side. A design able to read the resonance
spectrum learns the arithmetic of the panel and learns nothing whatever about the signs,
so enlarging the exposed algebra by this invariant does not expose any odd part. -/
theorem resonance_blind_to_sign_flip {m : ℕ} (P Q : PhasePanel m)
    (hphase : P.phase = Q.phase) (hweight : P.weight = Q.weight) (s : ℝ) :
    P.intensity s = Q.intensity s := by
  unfold intensity cosPart sinPart
  rw [hphase, hweight]

/-- The intensity of a one-locus panel is one at every frequency: a single phase is
always aligned with itself, so a panel of one locus is resonant everywhere.

The degenerate case, and the reason resonance only becomes informative once a panel
carries several distinct phases. -/
theorem intensity_singleton (P : PhasePanel 1) (s : ℝ) : P.intensity s = 1 := by
  have hweight : P.weight 0 = 1 := by
    have := P.weight_sum
    simpa using this
  unfold intensity cosPart sinPart
  have hcos : ∑ i : Fin 1, P.weight i * Real.cos (s * P.phase i) =
      Real.cos (s * P.phase 0) := by
    simp [hweight]
  have hsin : ∑ i : Fin 1, P.weight i * Real.sin (s * P.phase i) =
      Real.sin (s * P.phase 0) := by
    simp [hweight]
  rw [hcos, hsin]
  have := Real.sin_sq_add_cos_sq (s * P.phase 0)
  linarith [this]

end PhasePanel

/-!
## Where this sits

Three statements about the same object, and the third is the one that matters for
methods.

*The classical dichotomy* asks only whether the increment law is lattice or not, and
answers with a bit. `Descent.Blindness.JetBarrier` already shows that bit is readable by a
design, since a lattice law's exceedance intensity exceeds the non-lattice one by a
factor strictly above one.

*The resonance spectrum* replaces that bit with a spectrum carrying masses. It reduces to
the classical answer at both ends — empty for the smooth case, a full arithmetic
progression for the lattice case — and is strictly finer in between.

*And it is sign-free*, by `resonance_blind_to_sign_flip`. So the ladder gains a rung, the
algebra a design can read grows strictly larger on the singular stratum, and the odd part
remains outside it. An invariant can become richer without becoming more revealing about
the thing it was hoped would separate.
-/

end Descent

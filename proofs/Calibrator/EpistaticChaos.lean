/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.ImitationRigidity

namespace Calibrator

noncomputable section

/-!
# Epistatic chaos: no jumps, and what erases signs

A phenotype built from interactions is a multilinear form in standardized
genotypes: `f = ∑_S c_S ∏_{i ∈ S} x_i`, with `∑_S c_S² = 1` fixing the scale.
Two questions decide whether the Gaussian surrogate used throughout PGS theory
is legitimate at high interaction order, and they have different answers.

**Can one interaction term dominate?** No. If every monomial obeys the tilted
tail bound — the size-biased walk's concentration bound, which supplies
`P((x^S)² > T) ≤ C / (T √|S|)` — then a union bound over the whole design gives
`P(some term exceeds τ) ≤ C / (τ² √m_min)`, which vanishes as the minimum
interaction order grows. High-order epistasis produces no macroscopic
single-combination effects, for any design and any coding: there are no
epistatic outliers to find, and a search for them is a search for something
that cannot exist.

**Do overlapping interaction terms decouple at second order?** Only when the
coding is sign-symmetric. The Sign-Erasure Lemma below is exact and finite: if
the coordinate law is invariant under a value-negating relabelling and the
truncation depends only on magnitudes, then every truncated cross-moment between
two distinct monomials vanishes identically.

Second order is as far as that goes, and the qualifier is load-bearing. Sign
erasure does **not** license the conclusion that overlapping designs collapse
onto their disjoint skeletons and so inherit the independent limit theory. That
conclusion is false, and §`OverlapSpectrum` below refutes it inside the
symmetric class: the two-pool interaction statistic
`T₁ * T₂` has vanishing truncated cross-moments under any symmetric law, and a
limiting fourth cumulant of `6`, whereas every disjoint design's limit has
fourth cumulant `0` (`sign_symmetry_does_not_license_disjoint_reduction`). What
actually licenses the independent limit theory is *disjointness of the tested
locus-sets*, and nothing weaker.

The genetics is decided by where hard-called diploid dosage sits with respect
to that symmetry, and the answer is that it never sits inside: away from
frequency one half the coding is skewed, and at one half the squared coding
takes only two values, so its logarithm is confined to a single point. Both
failures are proved below. The consequence is not that the Gaussian surrogate
is wrong — no jumps means no gross failure — but that its justification cannot
come from a universality argument about the coding, and must come from the
bounded-degree invariance principle or from the Mellin data of
`Calibrator.PolygenicSpectroscopy` instead.

## Applicability record for the genotype instantiation

Because the symmetry hypothesis is a *hypothesis*, every result that carries it
is true as stated and says nothing about genotypes until the hypothesis is
discharged for genotypes. `hwe_symmetricCoding_iff_half` and
`standardizedGenotype_symmetric_iff` discharge it, and the answer is a single
point: **a Hardy-Weinberg locus is sign-symmetric if and only if its allele
frequency is exactly one half**, for the centered dosage and equally for the
standardized coordinate `x = (dosage - 2q) / sqrt (2 q (1 - q))`, since
rescaling by a constant cannot create or destroy a value-negating relabelling
(`SymmetricCoding.scale`).

So the licensing statement, which should be read into every symmetry-carrying
theorem below. The stronger `ChaosSpectroscopy` completeness result formerly in
`Calibrator.JetBarrier` has been removed. The surviving licensing statement is:

> the genotype instantiation of any sign-symmetry result is licensed only at
> `q = 1/2`.

And `q = 1/2` is the frequency at which the theory's other quantitative input
degenerates: `Calibrator.PolygenicSpectroscopy.hweMellinJetVariance_half` gives
`v(1/2) = 0`, and `centeredDosageSquare_two_valued_at_half` below is the same
degeneracy read off the coding. The one frequency where the symmetry hypothesis
holds is the one frequency where the size-biased increment carries no variance
at all, so the symmetric-law branch of the theory is, for genotypes, supported
on a point where the second observable is empty.

Two things this record is *not*. It is not a claim that the drift is degenerate
at `q = 1/2`: the size-biased drift there is `c(1/2) = log 2 = 0.6931...`
(`hweMellinDrift_half`), not zero, because the standardized coordinate at a
balanced locus takes the values `-sqrt 2, 0, sqrt 2` — it is *not* Rademacher,
and `x ^ 2` is not identically one. It is also not a caveat on the
condensation/drift arc: the direct quantities in `Calibrator.Condensation` require no
symmetry field, so the drift-separation and critical-degree results apply at
every allele frequency. What is symmetry-gated is the sign-erasure lemma here —
the vanishing of truncated cross-moments — and the completeness statements built
on it. §`OverlapSpectrum` is gated on something else entirely, disjointness of
the tested locus-sets, and is licensed at every allele frequency.
-/

section NoJump

/-!
## No interaction term is macroscopic

`jumpProbability s` is the probability that monomial `s` alone exceeds the
threshold. The tilted tail bound enters as a hypothesis, one monomial at a
time; everything else is a union bound and the unit-variance normalization.
-/

variable {S : Type*} [Fintype S]

/-- **The no-jump bound.** For a unit-variance multilinear design whose
monomials each obey the tilted tail bound, the chance that *any* interaction
term is individually macroscopic is at most `C / (τ² √m_min)`. The design may be
arbitrary: overlapping windows, whole-genome interaction scans, anything with
`∑ c_S² = 1`.

Empirical status: DERIVED. The per-monomial tail bound is a hypothesis, not a
claim about genotypes; what is proved here is that it propagates from one
monomial to a whole design without any loss beyond the minimum order. -/
theorem no_macroscopic_interaction_term
    (coefficient jumpProbability : S → ℝ) (interactionOrder : S → ℕ)
    (tiltConstant threshold : ℝ) (minimumOrder : ℕ)
    (hthreshold : 0 < threshold)
    (hminimum : 1 ≤ minimumOrder)
    (horder : ∀ s, minimumOrder ≤ interactionOrder s)
    (hnorm : ∑ s, coefficient s ^ 2 = 1)
    (htail : ∀ s, jumpProbability s ≤
      tiltConstant * coefficient s ^ 2 /
        (threshold ^ 2 * Real.sqrt (interactionOrder s)))
    (htilt : 0 ≤ tiltConstant) :
    ∑ s, jumpProbability s ≤
      tiltConstant / (threshold ^ 2 * Real.sqrt minimumOrder) := by
  have hminpos : (0 : ℝ) < Real.sqrt minimumOrder := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hminimum
  have hthresh2 : (0 : ℝ) < threshold ^ 2 := by positivity
  have hstep : ∀ s, jumpProbability s ≤
      tiltConstant * coefficient s ^ 2 / (threshold ^ 2 * Real.sqrt minimumOrder) := by
    intro s
    refine le_trans (htail s) ?_
    have hsqrt : Real.sqrt minimumOrder ≤ Real.sqrt (interactionOrder s) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast horder s
    have hden : 0 < threshold ^ 2 * Real.sqrt minimumOrder := by positivity
    apply div_le_div_of_nonneg_left (by positivity) hden
    exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt hthresh2)
  refine le_trans (Finset.sum_le_sum (fun s _ ↦ hstep s)) ?_
  have hfactor : ∀ s : S,
      tiltConstant * coefficient s ^ 2 / (threshold ^ 2 * Real.sqrt minimumOrder) =
        (tiltConstant / (threshold ^ 2 * Real.sqrt minimumOrder)) * coefficient s ^ 2 := by
    intro s; ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, hnorm, mul_one]

/-- The no-jump bound vanishes as the minimum interaction order grows: at high
epistatic order the design has no jump part at all, whatever the coding. -/
theorem no_macroscopic_interaction_limit
    (tiltConstant threshold : ℝ) (hthreshold : threshold ≠ 0) :
    Filter.Tendsto
      (fun minimumOrder : ℕ ↦
        tiltConstant / (threshold ^ 2 * Real.sqrt minimumOrder))
      Filter.atTop (nhds 0) := by
  have hpos : (0 : ℝ) < threshold ^ 2 := by positivity
  have hsqrt : Filter.Tendsto (fun m : ℕ ↦ Real.sqrt m) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 (fun b ↦ ⟨⌈b ^ 2⌉₊, fun m hm ↦ ?_⟩)
    have hb : b ^ 2 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hb
  have hscaled : Filter.Tendsto
      (fun m : ℕ ↦ threshold ^ 2 * Real.sqrt m) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hpos hsqrt
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hscaled

end NoJump

section SignErasure

/-!
## Sign erasure

A coding is *sign-symmetric* when relabelling the coordinate values by a
bijection negates every value and leaves every probability alone. For diploid
genotypes this is a finite condition on three numbers, decided below.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- A finite coordinate law together with a value-negating relabelling: the
exact finite-sample form of the symmetry hypothesis. -/
structure SymmetricCoding (V : Type*) [Fintype V] where
  /-- Probability of each coded value. -/
  weight : V → ℝ
  /-- The standardized numeric value of each code. -/
  value : V → ℝ
  /-- The relabelling that negates values. -/
  flip : V ≃ V
  /-- Relabelling does not change probabilities. -/
  weight_flip : ∀ v, weight (flip v) = weight v
  /-- Relabelling negates values. -/
  value_flip : ∀ v, value (flip v) = -value v

/-- **The class is inhabited.**  Without a term of this type every theorem quantified
over it is a true statement about an empty class: kernel-checked, clean axiom report,
and no content.  See `scripts/check-laundering.py` family F4. -/
noncomputable def SymmetricCoding.witness (V : Type*) [Fintype V] : SymmetricCoding V where
  weight := fun _ ↦ 0
  value := fun _ ↦ 0
  flip := Equiv.refl V
  weight_flip := fun _ ↦ rfl
  value_flip := fun _ ↦ by norm_num

/-- Probability of a genotype configuration under independence across loci. -/
def configurationWeight (coding : SymmetricCoding V) (x : Fin n → V) : ℝ :=
  ∏ i, coding.weight (x i)

/-- The interaction monomial `∏_{i ∈ S} x_i` of a configuration. -/
def interactionMonomial (coding : SymmetricCoding V) (locusSet : Finset (Fin n))
    (x : Fin n → V) : ℝ :=
  ∏ i ∈ locusSet, coding.value (x i)

/-- Flip the coding of one locus, leaving every other locus alone. -/
def flipLocus (coding : SymmetricCoding V) (i : Fin n) :
    (Fin n → V) ≃ (Fin n → V) where
  toFun x := Function.update x i (coding.flip (x i))
  invFun x := Function.update x i (coding.flip.symm (x i))
  left_inv x := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  right_inv x := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]

/-- A product over a set containing `i`, of a function evaluated at a
one-coordinate update, splits off the updated factor. -/
private theorem prod_update_split {β : Type*} [CommMonoid β] (f : V → β)
    (x : Fin n → V) (i : Fin n) (v : V) (s : Finset (Fin n)) (hi : i ∈ s) :
    (∏ j ∈ s, f (Function.update x i v j)) = f v * ∏ j ∈ s \ {i}, f (x j) := by
  rw [Finset.prod_eq_mul_prod_diff_singleton hi]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl (fun j hj ↦ ?_)
    have hne : j ≠ i := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hj).2
    rw [Function.update_of_ne hne]

theorem configurationWeight_flipLocus (coding : SymmetricCoding V) (i : Fin n)
    (x : Fin n → V) :
    configurationWeight coding (flipLocus coding i x) = configurationWeight coding x := by
  unfold configurationWeight flipLocus
  simp only [Equiv.coe_fn_mk]
  rw [prod_update_split coding.weight x i (coding.flip (x i)) Finset.univ
      (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)
      (fun j ↦ coding.weight (x j)),
    coding.weight_flip]

theorem interactionMonomial_flipLocus_mem (coding : SymmetricCoding V)
    {i : Fin n} {locusSet : Finset (Fin n)} (hi : i ∈ locusSet) (x : Fin n → V) :
    interactionMonomial coding locusSet (flipLocus coding i x) =
      -interactionMonomial coding locusSet x := by
  unfold interactionMonomial flipLocus
  simp only [Equiv.coe_fn_mk]
  rw [prod_update_split coding.value x i (coding.flip (x i)) locusSet hi,
    Finset.prod_eq_mul_prod_diff_singleton hi (fun j ↦ coding.value (x j)),
    coding.value_flip]
  ring

theorem interactionMonomial_flipLocus_not_mem (coding : SymmetricCoding V)
    {i : Fin n} {locusSet : Finset (Fin n)} (hi : i ∉ locusSet) (x : Fin n → V) :
    interactionMonomial coding locusSet (flipLocus coding i x) =
      interactionMonomial coding locusSet x := by
  unfold interactionMonomial flipLocus
  simp only [Equiv.coe_fn_mk]
  refine Finset.prod_congr rfl (fun j hj ↦ ?_)
  have hne : j ≠ i := by rintro rfl; exact hi hj
  rw [Function.update_of_ne hne]

/-- **Sign-Erasure Lemma.** For a sign-symmetric coding and any truncation that
depends only on magnitudes, the truncated cross-moment of two interaction
monomials vanishes exactly whenever some locus lies in one and not the other.
No asymptotics, no tuning, no moment conditions: one relabelling of one locus
does it.

The consequence for epistasis is that overlapping interaction terms — sliding
windows along a chromosome, nested gene sets — have the truncated
*second-moment* structure of disjoint ones.

**It does not follow that their limit theory is the independent one**, and the
inference is blocked by an explicit counterexample in §`OverlapSpectrum`:
`sign_symmetry_does_not_license_disjoint_reduction`. Second-order decoupling is
compatible with a non-Gaussian limit, because the limit law of an overlapping
design is a spectral invariant of the overlap structure and no second-order
functional determines it. The disjoint limit theory needs
`GenotypeDesign.VariantDisjoint`, which sign symmetry does not supply.

**Genotype applicability.** The `SymmetricCoding` argument is a hypothesis, and
for a Hardy-Weinberg locus it is satisfied at exactly one allele frequency:
`q = 1/2` (`hwe_symmetricCoding_iff_half`, and
`standardizedGenotype_symmetric_iff` for the standardized coordinate). At every
other frequency the third central moment is `2q(1-q)(1-2q) ≠ 0`
(`hweThirdCentralMoment_eq`), no value-negating relabelling exists, and this
lemma says nothing about the locus: overlapping interaction terms are **not**
licensed to collapse onto their disjoint skeletons. That is the whole content
of the restriction — the lemma is exact and correct, but for real allele
frequency spectra it is a statement about a measure-zero point. -/
theorem sign_erasure (coding : SymmetricCoding V)
    (firstSet secondSet : Finset (Fin n)) (truncation : (Fin n → V) → ℝ)
    {i : Fin n} (hfirst : i ∈ firstSet) (hsecond : i ∉ secondSet)
    (htruncation : ∀ x, truncation (flipLocus coding i x) = truncation x) :
    ∑ x : Fin n → V,
        configurationWeight coding x * interactionMonomial coding firstSet x *
          interactionMonomial coding secondSet x * truncation x = 0 := by
  set F : (Fin n → V) → ℝ := fun x ↦
    configurationWeight coding x * interactionMonomial coding firstSet x *
      interactionMonomial coding secondSet x * truncation x with hF
  have hflip : ∀ x, F (flipLocus coding i x) = -F x := by
    intro x
    simp only [hF, configurationWeight_flipLocus,
      interactionMonomial_flipLocus_mem coding hfirst,
      interactionMonomial_flipLocus_not_mem coding hsecond, htruncation]
    ring
  have hsum : ∑ x, F x = ∑ x, F (flipLocus coding i x) :=
    (Fintype.sum_equiv (flipLocus coding i) (fun x ↦ F (flipLocus coding i x)) F
      (fun _ ↦ rfl)).symm
  have hneg : ∑ x, F x = -∑ x, F x := by
    conv_lhs => rw [hsum]
    simp_rw [hflip]
    rw [Finset.sum_neg_distrib]
  linarith [hneg]

/-- **Symmetry is scale-invariant.** Rescaling every coded value by a constant
keeps the same relabelling working, because negation commutes with scaling.

This is what lets a symmetry verdict for the centered dosage be transported to
the standardized coordinate `x = (dosage - 2q) / sqrt (2 q (1 - q))` without
recomputing anything: see `standardizedGenotype_symmetric_iff`.

Empirical status: DERIVED. Pure algebra on the structure fields; no modelling
content and no free parameter. -/
def SymmetricCoding.scale (coding : SymmetricCoding V) (a : ℝ) :
    SymmetricCoding V where
  weight := coding.weight
  value := fun v ↦ a * coding.value v
  flip := coding.flip
  weight_flip := coding.weight_flip
  value_flip v := by
    show a * coding.value (coding.flip v) = -(a * coding.value v)
    rw [coding.value_flip]
    ring

/-- A sign-symmetric coding has no odd moments. This is the finite-sample
handle used below to decide which genotype codings are symmetric.

**Genotype applicability.** Contrapositively this is the *detector*: a coding
with a nonzero third moment admits no value-negating relabelling. Applied to
Hardy-Weinberg dosage it yields `hwe_symmetricCoding_forces_half`, and hence
the licensing restriction to `q = 1/2` recorded in the module docstring. -/
theorem symmetricCoding_third_moment_zero (coding : SymmetricCoding V) :
    ∑ v, coding.weight v * coding.value v ^ 3 = 0 := by
  have hswap : ∑ v, coding.weight v * coding.value v ^ 3 =
      ∑ v, coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3 :=
    (Fintype.sum_equiv coding.flip
      (fun v ↦ coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3)
      (fun v ↦ coding.weight v * coding.value v ^ 3) (fun _ ↦ rfl)).symm
  have hterm : ∀ v : V,
      coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3 =
        -(coding.weight v * coding.value v ^ 3) := by
    intro v
    rw [coding.weight_flip, coding.value_flip]
    ring
  have hneg : ∑ v, coding.weight v * coding.value v ^ 3 =
      -∑ v, coding.weight v * coding.value v ^ 3 := by
    conv_lhs => rw [hswap]
    simp_rw [hterm]
    rw [Finset.sum_neg_distrib]
  linarith [hneg]

end SignErasure

section GenotypeCoding

/-!
## Where diploid dosage sits

Two obstructions, at complementary frequencies. Away from `q = 1/2` the coding
is skewed and admits no value-negating relabelling at all; at `q = 1/2` it does
admit one — `hwe_symmetricCoding_iff_half` proves both directions — but there
the squared coding takes only two values, so `log x ^ 2` sits on a single point.

Together they say that no allele frequency puts a hard call in the stratum the
symmetric-law theory needs: symmetric *and* nondegenerate in `log x ^ 2`. The
frequency-by-frequency applicability verdict is recorded in the module docstring
and repeated on each symmetry-carrying theorem.
-/

/-- Third central moment of the hard-called dosage at a Hardy–Weinberg locus.

Empirical status: DERIVED from `HardyWeinbergModel.genotypeProb` and
`HardyWeinbergModel.centeredAltAlleleCount`; the closed form is
`hweThirdCentralMoment_eq`. -/
def hweThirdCentralMoment (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredAltAlleleCount g ^ 3

/-- **The skewness of dosage.** `E[(g - 2q)³] = 2q(1-q)(1-2q)`: zero exactly at
the monomorphic points and at frequency one half. -/
theorem hweThirdCentralMoment_eq (h : HardyWeinbergModel) :
    hweThirdCentralMoment h =
      2 * h.altFreq * (1 - h.altFreq) * (1 - 2 * h.altFreq) := by
  unfold hweThirdCentralMoment
  rw [sum_over_genotypes]
  simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
    HardyWeinbergModel.centeredAltAlleleCount, HardyWeinbergModel.expectedAltAlleleCount_eq,
    altAlleleCount]
  ring

/-- **Dosage coding is sign-symmetric only at frequency one half.** If the
genotype law admits a value-negating relabelling, its third central moment
vanishes, which at a polymorphic locus forces `q = 1/2`. Away from that
frequency the Sign-Erasure Lemma does not apply, overlapping interaction terms
do not decouple, and the truncated sign couplings that survive are exactly the
skewness of the dosage. -/
theorem hwe_symmetricCoding_forces_half
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (coding : SymmetricCoding DiploidGenotype)
    (hweight : ∀ g, coding.weight g = h.genotypeProb g)
    (hvalue : ∀ g, coding.value g = h.centeredAltAlleleCount g) :
    h.altFreq = 1 / 2 := by
  have hzero : hweThirdCentralMoment h = 0 := by
    unfold hweThirdCentralMoment
    have hrewrite : ∀ g : DiploidGenotype,
        h.genotypeProb g * h.centeredAltAlleleCount g ^ 3 =
          coding.weight g * coding.value g ^ 3 := by
      intro g; rw [hweight, hvalue]
    simp_rw [hrewrite]
    exact symmetricCoding_third_moment_zero coding
  rw [hweThirdCentralMoment_eq] at hzero
  have hne : h.altFreq * (1 - h.altFreq) ≠ 0 := by
    have : 0 < h.altFreq * (1 - h.altFreq) := by
      apply mul_pos hq0
      linarith
    exact ne_of_gt this
  have hfactor : 1 - 2 * h.altFreq = 0 := by
    rcases mul_eq_zero.mp (by linarith [hzero] : (2 * (h.altFreq * (1 - h.altFreq))) *
        (1 - 2 * h.altFreq) = 0) with hleft | hright
    · exact absurd (by linarith [hleft] : h.altFreq * (1 - h.altFreq) = 0) hne
    · exact hright
  linarith

/-- The only candidate value-negating relabelling of diploid genotypes: swap the
two homozygotes and fix the heterozygote.

It is forced. A relabelling that negates centered dosages must send the unique
genotype whose centered dosage is its own negative — the heterozygote, at
`q = 1/2` — to itself, and must exchange the other two.

Empirical status: DERIVED. A permutation of a three-element type; no modelling
content and no free parameter. -/
def genotypeFlip : DiploidGenotype ≃ DiploidGenotype where
  toFun
    | .homRef => .homAlt
    | .het => .het
    | .homAlt => .homRef
  invFun
    | .homRef => .homAlt
    | .het => .het
    | .homAlt => .homRef
  left_inv g := by cases g <;> rfl
  right_inv g := by cases g <;> rfl

@[simp] theorem genotypeFlip_homRef :
    genotypeFlip DiploidGenotype.homRef = DiploidGenotype.homAlt := rfl

@[simp] theorem genotypeFlip_het :
    genotypeFlip DiploidGenotype.het = DiploidGenotype.het := rfl

@[simp] theorem genotypeFlip_homAlt :
    genotypeFlip DiploidGenotype.homAlt = DiploidGenotype.homRef := rfl

/-- **The balanced locus really is sign-symmetric: the converse direction.**

At `q = 1/2` the homozygote swap preserves every Hardy-Weinberg probability
(both homozygotes have probability `1/4`) and negates every centered dosage
(`-1, 0, 1` goes to `1, 0, -1`), so a value-negating relabelling exists. With
`hwe_symmetricCoding_forces_half` this closes the characterization: symmetry
holds at `q = 1/2` and nowhere else in the polymorphic range.

Empirical status: DERIVED from `HardyWeinbergModel.genotypeProb` and
`HardyWeinbergModel.centeredAltAlleleCount` evaluated at `q = 1/2`; no free
parameter and nothing fitted. -/
def equalFrequencyGenotypeCoding (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2) :
    SymmetricCoding DiploidGenotype where
  weight := h.genotypeProb
  value := h.centeredAltAlleleCount
  flip := genotypeFlip
  weight_flip g := by
    cases g <;>
      simp only [genotypeFlip_homRef, genotypeFlip_het, genotypeFlip_homAlt,
          HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq, hhalf] <;>
      norm_num
  value_flip g := by
    cases g <;>
      simp only [genotypeFlip_homRef, genotypeFlip_het, genotypeFlip_homAlt,
          HardyWeinbergModel.centeredAltAlleleCount,
          HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount, hhalf] <;>
      norm_num

/-- **The symmetry characterization for hard-called dosage.** A polymorphic
Hardy-Weinberg locus admits a value-negating relabelling of its centered dosage
**if and only if** the allele frequency is exactly one half.

This is the applicability record for every sign-symmetry result in this file and
for any future symmetric-law completeness theorem. The current corpus exports no such
`ChaosSpectroscopy` result. -/
theorem hwe_symmetricCoding_iff_half
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.centeredAltAlleleCount g)) ↔ h.altFreq = 1 / 2 := by
  constructor
  · rintro ⟨coding, hweight, hvalue⟩
    exact hwe_symmetricCoding_forces_half h hq0 hq1 coding hweight hvalue
  · intro hhalf
    exact ⟨equalFrequencyGenotypeCoding h hhalf, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The standardized genotype coordinate `x = (dosage - 2q) / sqrt (2 q (1 - q))`.

This is the coordinate the chaos theory is stated for: centered and, at a
polymorphic locus, of unit variance. Its square is
`Calibrator.PolygenicSpectroscopy.HardyWeinbergModel.standardizedSquare`; this
definition supplies the *signed* value, which is what a symmetry question needs.

At `q = 1/2` its three values are `-sqrt 2, 0, sqrt 2` — note that this is not a
Rademacher coordinate, and `x ^ 2` is not identically one.

Empirical status: DERIVED from `HardyWeinbergModel.centeredAltAlleleCount` and
`HardyWeinbergModel.genotypeVariance`; it is the standard normalization, with no
free parameter. -/
noncomputable def HardyWeinbergModel.standardizedGenotype
    (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  h.centeredAltAlleleCount g / Real.sqrt h.genotypeVariance

/-- **The symmetry characterization for the standardized coordinate.**

Identical verdict, because `SymmetricCoding.scale` shows a value-negating
relabelling survives any rescaling: the standardized genotype law is symmetric
if and only if `q = 1/2`.

Stating it in the standardized coordinate matters because that is the coordinate
the proposed abstract theory would quantify over symmetric unit-variance laws, so this is
the form in which that hypothesis would be discharged, or (at `q ≠ 1/2`) refuted. -/
theorem standardizedGenotype_symmetric_iff
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.standardizedGenotype g)) ↔ h.altFreq = 1 / 2 := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hs : 0 < Real.sqrt h.genotypeVariance := Real.sqrt_pos.mpr hvar
  have hsne : Real.sqrt h.genotypeVariance ≠ 0 := ne_of_gt hs
  constructor
  · rintro ⟨coding, hweight, hvalue⟩
    refine hwe_symmetricCoding_forces_half h hq0 hq1
      (coding.scale (Real.sqrt h.genotypeVariance)) (fun g ↦ hweight g) ?_
    intro g
    show Real.sqrt h.genotypeVariance * coding.value g = h.centeredAltAlleleCount g
    rw [hvalue g]
    unfold HardyWeinbergModel.standardizedGenotype
    field_simp
  · intro hhalf
    refine ⟨(equalFrequencyGenotypeCoding h hhalf).scale (1 / Real.sqrt h.genotypeVariance),
      fun _ ↦ rfl, ?_⟩
    intro g
    show (1 / Real.sqrt h.genotypeVariance) * h.centeredAltAlleleCount g =
      h.standardizedGenotype g
    unfold HardyWeinbergModel.standardizedGenotype
    ring

/-- **At frequency one half the squared dosage takes only two values.** The
centered dosage is `-1, 0, 1`, so its square is `1, 0, 1`: after the
deterministic variance rescaling that produces the standardized square of
`Calibrator.PolygenicSpectroscopy`, `log x²` is supported on a single point and
lies inside every lattice. The one frequency at which dosage coding is
sign-symmetric is the frequency at which it is maximally lattice. -/
theorem centeredDosageSquare_two_valued_at_half
    (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2) :
    h.centeredAltAlleleCount DiploidGenotype.homRef ^ 2 = 1 ∧
      h.centeredAltAlleleCount DiploidGenotype.het ^ 2 = 0 ∧
      h.centeredAltAlleleCount DiploidGenotype.homAlt ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [HardyWeinbergModel.centeredAltAlleleCount,
        HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount, hhalf]
      norm_num

/-- **The dichotomy for hard-called genotypes.** At a polymorphic locus, either
the frequency is one half — and then the coding is sign-symmetric but its
squared values collapse to two points — or it is not, and then the third
central moment is nonzero and no value-negating relabelling exists. There is no
allele frequency at which a hard-called diploid locus is both sign-symmetric
and spread out in `log x²`, so the universality stratum that would justify a
Gaussian surrogate by symmetry alone contains no genotype coding. -/
theorem hardCall_coding_dichotomy
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (h.altFreq = 1 / 2 ∧
        h.centeredAltAlleleCount DiploidGenotype.homRef ^ 2 = 1 ∧
        h.centeredAltAlleleCount DiploidGenotype.het ^ 2 = 0 ∧
        h.centeredAltAlleleCount DiploidGenotype.homAlt ^ 2 = 1) ∨
      hweThirdCentralMoment h ≠ 0 := by
  by_cases hhalf : h.altFreq = 1 / 2
  · exact Or.inl ⟨hhalf, centeredDosageSquare_two_valued_at_half h hhalf⟩
  · refine Or.inr ?_
    rw [hweThirdCentralMoment_eq]
    have hskew : 1 - 2 * h.altFreq ≠ 0 := by
      intro hcontra
      exact hhalf (by linarith)
    intro hzero
    rcases mul_eq_zero.mp hzero with hleft | hright
    · rcases mul_eq_zero.mp hleft with h2 | hone
      · rcases mul_eq_zero.mp h2 with htwo | hq0'
        · norm_num at htwo
        · exact absurd hq0' (ne_of_gt hq0)
      · exact absurd hone (by intro hc; linarith)
    · exact hskew hright

end GenotypeCoding

section OverlapSpectrum

/-!
## Disjoint locus-sets versus overlapping ones: a licence and a prohibition

Everything above concerns one interaction term at a time (no jumps) or two terms
at a time (sign erasure). Neither settles the question a practitioner faces,
which is about a whole *design* at once: given the collection of locus-sets a
set-based or interaction study tests over a panel of Hardy-Weinberg loci, what
null distributions can the test statistic have?

Two results answer it, and they answer in opposite directions according to a
single structural property — whether the tested locus-sets share variants. Neither
is carried as a field of an assumption-packaging interface such as
`GenotypeChaosLimits`, because a hypothesis held as a field cannot be contradicted.
Everything is stated over
`GenotypeDesign`, whose coordinates are the standardized Hardy-Weinberg genotypes
`HardyWeinbergModel.standardizedGenotype` of a stated allele-frequency family, so
that the statements can be contradicted by the rest of the corpus.

Call a design admissible when the minimum interaction order grows, the influence
of each locus (`GenotypeDesign.locusInfluence`, the share of the statistic's
energy carried by that variant) vanishes, and the statistic has unit variance.

* **Theorem D (the licence).** For a design whose tested locus-sets are pairwise
  *disjoint*, over polymorphic loci in linkage equilibrium, the achievable limits
  are the one-parameter Gaussian segment `{N(0, s²) : 0 ≤ s² ≤ 1}`. Only the
  variance is free, so a Gaussian or chi-square calibration is justified by the
  asymptotics. Gene-based burden or kernel tests in which each variant is
  assigned to one gene are in this case: `geneBurdenDesign_variantDisjoint`.

* **Theorem S (the prohibition).** With disjointness dropped, and at *any*
  prescribed polymorphic allele-frequency family, the achievable limits are
  weakly dense in the entire moment body: every centered law with second moment
  at most one. Sliding windows are in this case
  (`slidingWindowDesign_not_variantDisjoint`), as are overlapping pathway panels
  and any pleiotropic variant recurring across tested sets.

Theorem S is strictly stronger than the folklore. Folklore puts the effect of
overlap at a variance-mixture component in the limit. A variance mixture of
centered Gaussians is symmetric, unimodal and has non-negative fourth cumulant,
and the moment body contains laws that are none of those.


### Does the licence need sign symmetry? No, and this matters

`standardizedGenotype_symmetric_iff` proves that a standardized Hardy-Weinberg
coordinate is sign-symmetric only at `q = 1/2`, so any result needing symmetry is
licensed for genotypes at one frequency. The disjoint licence does **not** need
it, and the reason is visible in the inputs its proof route uses:

1. each coordinate is centered with unit variance — proved for the standardized
   genotype at every polymorphic frequency below, without symmetry, in
   `standardizedGenotype_expectation_zero` and
   `standardizedGenotype_second_moment_one`;
2. the coordinates are independent across loci — the linkage-equilibrium
   hypothesis `GenotypeDesign.InLinkageEquilibrium`, an argument of the licence,
   not an assumption about the coding;
3. no monomial is macroscopic — `no_macroscopic_interaction_term` of §`NoJump`,
   which carries no symmetry hypothesis and holds for any design and any coding.

Sign symmetry belongs to the *other* route, the one that tries to reduce
overlapping designs to disjoint skeletons by killing cross-moments. That route
fails for a reason unrelated to genotypes, and
`sign_symmetry_does_not_license_disjoint_reduction` below exhibits the failure
inside the symmetric class. So the honest division is: the licence is
frequency-free and needs linkage equilibrium; the sign-erasure reduction is
frequency-gated and does not deliver the licence anyway.
-/

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-! ### The coordinate: what a standardized genotype contributes -/

/-- **The standardized genotype is centered**, at every allele frequency and with
no symmetry hypothesis: `E[(g - 2q) / sqrt (2q(1-q))] = 0`.

This is the first of the two coordinate-level inputs the disjoint licence needs,
and it is the reason that licence is not frequency-gated. -/
theorem standardizedGenotype_expectation_zero (h : HardyWeinbergModel) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g = 0 := by
  have hfactor : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedGenotype g =
        h.genotypeProb g * h.centeredAltAlleleCount g / Real.sqrt h.genotypeVariance := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    ring
  have hnum : ∑ g : DiploidGenotype,
      h.genotypeProb g * h.centeredAltAlleleCount g = 0 := by
    rw [sum_over_genotypes]
    simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
      HardyWeinbergModel.centeredAltAlleleCount,
      HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount]
    ring
  simp_rw [hfactor]
  rw [← Finset.sum_div, hnum, zero_div]

/-- **The standardized genotype has unit second moment** at every polymorphic
allele frequency, again with no symmetry hypothesis: the normalization divides by
`sqrt` of exactly the variance `HardyWeinbergModel.genotypeVariance` is defined
to be.

This is the second coordinate-level input of the disjoint licence. Together with
`standardizedGenotype_expectation_zero` it says the genotype coordinate meets the
hypotheses of the chaos theory at every frequency in `(0, 1)` — which is why
Theorem D, unlike everything in §`SignErasure`, is not restricted to `q = 1/2`. -/
theorem standardizedGenotype_second_moment_one (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 2 = 1 := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hsq : Real.sqrt h.genotypeVariance ^ 2 = h.genotypeVariance :=
    Real.sq_sqrt hvar.le
  have hfactor : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedGenotype g ^ 2 =
        h.genotypeProb g * h.centeredAltAlleleCount g ^ 2 / h.genotypeVariance := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    rw [div_pow, hsq]
    ring
  have hnum : ∑ g : DiploidGenotype,
      h.genotypeProb g * h.centeredAltAlleleCount g ^ 2 = h.genotypeVariance := rfl
  simp_rw [hfactor]
  rw [← Finset.sum_div, hnum]
  exact div_self (ne_of_gt hvar)

/-- **The fourth moment of the standardized genotype is the reciprocal of the
genotype variance**: `E[x⁴] = 1 / (2q(1-q))`.

The computation is exact and needs no new machinery. The fourth central moment of
a `Binomial(2, q)` dosage is `2q(1-q)` — the general binomial fourth central
moment `n q (1-q) (1 + 3 (n - 2) q (1-q))` has its correction term vanish at
`n = 2`, which is special to diploidy — so dividing by `Var² = (2q(1-q))²` leaves
`1 / (2q(1-q))`.

This is the fourth channel of the observable algebra, and unlike the drift and the
jet variance it is a rational function of a quantity the corpus already owns:
`Calibrator.CondensationUnification.hweStandardizedFourthMoment_eq_inv_hweGenotypeVariance`
states it against `hweGenotypeVariance` itself. It diverges as the allele
frequency goes to zero, so rare variants have heavy-tailed standardized
coordinates in the precise sense that the fourth channel is large. -/
theorem standardizedGenotype_fourth_moment (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 =
      1 / h.genotypeVariance := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hsq : Real.sqrt h.genotypeVariance ^ 2 = h.genotypeVariance :=
    Real.sq_sqrt hvar.le
  have hquart : Real.sqrt h.genotypeVariance ^ 4 = h.genotypeVariance ^ 2 := by
    have hrewrite : Real.sqrt h.genotypeVariance ^ 4 =
        (Real.sqrt h.genotypeVariance ^ 2) ^ 2 := by ring
    rw [hrewrite, hsq]
  have hfactor : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedGenotype g ^ 4 =
        h.genotypeProb g * h.centeredAltAlleleCount g ^ 4 / h.genotypeVariance ^ 2 := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    rw [div_pow, hquart]
    ring
  have hnum : ∑ g : DiploidGenotype,
      h.genotypeProb g * h.centeredAltAlleleCount g ^ 4 = h.genotypeVariance := by
    rw [h.genotypeVariance_eq, sum_over_genotypes]
    simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
      HardyWeinbergModel.centeredAltAlleleCount,
      HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount]
    ring
  simp_rw [hfactor]
  rw [← Finset.sum_div, hnum, pow_two, ← div_div, div_self (ne_of_gt hvar)]

/-- **The second cumulant of the squared standardized genotype**, `κ₂(x²) = E[x⁴] - 1`,
in closed form: `(1 - 2q(1-q)) / (2q(1-q))`.

This is the variance of the level-two coordinate, which is why it is the one
square-cumulant that a design can expose: it is a *variance*, and variances are
what the second floor of the observable tower reads. It diverges as the allele
frequency goes to zero. -/
theorem standardizedSquare_second_cumulant (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.genotypeVariance *
        ((∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) - 1) =
      1 - h.genotypeVariance := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  rw [standardizedGenotype_fourth_moment h hq0 hq1, mul_sub, mul_one_div,
    div_self (ne_of_gt hvar), mul_one]

/-!
### Floor two of the observable tower, and the trap beside it

The observable algebra does not stop at the two-jet, the arithmetic type, the
symmetry verdict and `E[x⁴]`. There is a second floor, carrying the Mellin jet of
the **centered** square `u = x² - 1` — fourth-through-eighth-moment logarithmic
data that no floor-one channel sees — and the full object is a tower, one floor
per iterated centered squaring, with universality holding exactly when the whole
tower matches the Gaussian's.

**The trap, encoded rather than described.** Tuning the *uncentered* products of
shared cores does not produce a new floor, and it looks like it does. The reason
is `uncentered_square_log_additive` below: the logarithm of a product of squares
is the sum of the level-one increments, so its condensation re-exposes floor-one
data wearing different clothes. The genuine second floor runs on the centered
square, whose logarithm is *not* a sum of level-one increments — `u` takes both
signs (`centeredSquare_negative_at_half`), while `x²` never does.

Whatever is built on top of this must keep the two apart, which is why the
additive identity is stated as a theorem here rather than left as a remark.
-/

/-- **The centered square** `u = x² - 1`: the coordinate of floor two.

Empirical status: DERIVED from `HardyWeinbergModel.standardizedGenotype`; the
centering constant is forced by `standardizedGenotype_second_moment_one`, which
proves `E[x²] = 1`, so there is no free parameter. -/
noncomputable def HardyWeinbergModel.centeredSquare
    (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  h.standardizedGenotype g ^ 2 - 1

/-- Floor two's coordinate is centered: `E[u] = 0`, because `E[x²] = 1`. -/
theorem centeredSquare_expectation_zero (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredSquare g = 0 := by
  have hterm : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.centeredSquare g =
        h.genotypeProb g * h.standardizedGenotype g ^ 2 - h.genotypeProb g := by
    intro g
    unfold HardyWeinbergModel.centeredSquare
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, standardizedGenotype_second_moment_one h hq0 hq1,
    h.genotypeProb_sum, sub_self]

/-- **The centered square takes both signs**, unlike `x²` which is non-negative.
At a balanced locus the standardized values are `-√2, 0, √2`, so `u` is `1, -1, 1`
and the heterozygote sits strictly below zero.

This is what makes floor two a genuinely new floor: `log u²` is not a sum of
level-one increments, because `u` is not a product of squares. Contrast
`uncentered_square_log_additive`. -/
theorem centeredSquare_negative_at_half (h : HardyWeinbergModel)
    (hhalf : h.altFreq = 1 / 2) :
    h.centeredSquare DiploidGenotype.het = -1 := by
  have hvar : h.genotypeVariance = 1 / 2 := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    rw [hhalf]
    norm_num
  have hcentered : h.centeredAltAlleleCount DiploidGenotype.het = 0 := by
    unfold HardyWeinbergModel.centeredAltAlleleCount
    rw [h.expectedAltAlleleCount_eq, hhalf]
    simp only [altAlleleCount]
    norm_num
  unfold HardyWeinbergModel.centeredSquare HardyWeinbergModel.standardizedGenotype
  rw [hcentered, hvar]
  norm_num

/-- **The trap.** The logarithm of a product of squared coordinates is the *sum*
of the level-one increments `log x²`. So a design that tunes uncentered products
of shared cores is running the same walk as floor one, and its condensation
re-exposes floor-one data rather than opening a floor.

Stated for two coordinates, which is enough: the general case is this identity
iterated, and the point is the additivity, not the arity. -/
theorem uncentered_square_log_additive (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x ^ 2 * y ^ 2) = Real.log (x ^ 2) + Real.log (y ^ 2) := by
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  exact Real.log_mul hx2 hy2

/-- The third moment of the centered square, in terms of the plain moments:
`E[u³] = E[x⁶] - 3 E[x⁴] + 2`, using `E[x²] = 1`.

This is the first floor-two datum that floor one does not already fix, and the
one a panel-level construction should target. -/
theorem centeredSquare_third_moment_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredSquare g ^ 3 =
      (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 6) -
        3 * (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) +
        (3 * (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 2) -
          ∑ g : DiploidGenotype, h.genotypeProb g) := by
  have hterm : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.centeredSquare g ^ 3 =
        h.genotypeProb g * h.standardizedGenotype g ^ 6 -
          3 * (h.genotypeProb g * h.standardizedGenotype g ^ 4) +
          (3 * (h.genotypeProb g * h.standardizedGenotype g ^ 2) - h.genotypeProb g) := by
    intro g
    unfold HardyWeinbergModel.centeredSquare
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The sixth central moment of the dosage**, in closed form:
`E[(G - 2q)⁶] = V + 10V² - 20V³` with `V = 2q(1-q)`.

A three-term computation like the fourth, and the input to the sixth standardized
moment below. -/
theorem hweCenteredSixthMoment_eq (h : HardyWeinbergModel) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredAltAlleleCount g ^ 6 =
      h.genotypeVariance + 10 * h.genotypeVariance ^ 2 - 20 * h.genotypeVariance ^ 3 := by
  rw [h.genotypeVariance_eq, sum_over_genotypes]
  simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
    HardyWeinbergModel.centeredAltAlleleCount,
    HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount]
  ring

/-- **The sixth moment of the standardized genotype is a quadratic in the fourth.**

`E[x⁶] = (E[x⁴])² + 10 E[x⁴] - 20`, since `E[x⁶] = 1/V² + 10/V - 20` and
`E[x⁴] = 1/V`.

For a single locus this is the collapse made quantitative: floor two's data is a
*function* of floor one's, with no freedom left. For a panel it is the opposite —
the mixture average of a quadratic is not the quadratic of the mixture average,
and the gap is exactly the across-locus dispersion of `E[x⁴]`. That gap is the
panel's floor-two datum, and it is what
`Calibrator.CondensationUnification.MafSpectrum.fourthMomentDispersion` names. -/
theorem standardizedGenotype_sixth_moment (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 6 =
      (1 / h.genotypeVariance) ^ 2 + 10 * (1 / h.genotypeVariance) - 20 := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hne : h.genotypeVariance ≠ 0 := ne_of_gt hvar
  have hsq : Real.sqrt h.genotypeVariance ^ 2 = h.genotypeVariance :=
    Real.sq_sqrt hvar.le
  have hsix : Real.sqrt h.genotypeVariance ^ 6 = h.genotypeVariance ^ 3 := by
    have hrewrite : Real.sqrt h.genotypeVariance ^ 6 =
        (Real.sqrt h.genotypeVariance ^ 2) ^ 3 := by ring
    rw [hrewrite, hsq]
  have hfactor : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedGenotype g ^ 6 =
        h.genotypeProb g * h.centeredAltAlleleCount g ^ 6 / h.genotypeVariance ^ 3 := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    rw [div_pow, hsix]
    ring
  have hsum : ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 6 =
      (h.genotypeVariance + 10 * h.genotypeVariance ^ 2 - 20 * h.genotypeVariance ^ 3) /
        h.genotypeVariance ^ 3 := by
    simp_rw [hfactor]
    rw [← Finset.sum_div, hweCenteredSixthMoment_eq]
  have hinv : (1 / h.genotypeVariance) * h.genotypeVariance = 1 := by
    rw [one_div, inv_mul_cancel₀ hne]
  have hcancel : (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 6) *
      h.genotypeVariance ^ 3 =
        h.genotypeVariance + 10 * h.genotypeVariance ^ 2 - 20 * h.genotypeVariance ^ 3 := by
    rw [hsum, div_mul_cancel₀ _ (pow_ne_zero 3 hne)]
  refine mul_right_cancel₀ (pow_ne_zero 3 hne) ?_
  rw [hcancel]
  symm
  calc ((1 / h.genotypeVariance) ^ 2 + 10 * (1 / h.genotypeVariance) - 20) *
        h.genotypeVariance ^ 3
      = ((1 / h.genotypeVariance) * h.genotypeVariance) ^ 2 * h.genotypeVariance +
          10 * ((1 / h.genotypeVariance) * h.genotypeVariance) * h.genotypeVariance ^ 2 -
          20 * h.genotypeVariance ^ 3 := by ring
    _ = h.genotypeVariance + 10 * h.genotypeVariance ^ 2 - 20 * h.genotypeVariance ^ 3 := by
        rw [hinv]
        ring

/-- **The three values of the centered square at a balanced locus**: `1, -1, 1`.

At `q = 1/2` the standardized coordinate takes `-√2, 0, √2`, so `x²` takes `2, 0, 2` and
`u = x² - 1` takes `1, -1, 1`. Note `σ₁² = E[x⁴] - 1 = 1` there, so the unnormalized and
normalized floor-two coordinates coincide at this frequency. -/
theorem centeredSquare_values_at_half (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2) :
    h.centeredSquare DiploidGenotype.homRef = 1 ∧
      h.centeredSquare DiploidGenotype.het = -1 ∧
      h.centeredSquare DiploidGenotype.homAlt = 1 := by
  have hvar : h.genotypeVariance = 1 / 2 := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    rw [hhalf]
    norm_num
  have hsqrt : Real.sqrt h.genotypeVariance ^ 2 = h.genotypeVariance :=
    Real.sq_sqrt (by rw [hvar]; norm_num)
  refine ⟨?_, centeredSquare_negative_at_half h hhalf, ?_⟩ <;>
    · unfold HardyWeinbergModel.centeredSquare HardyWeinbergModel.standardizedGenotype
      rw [div_pow, hsqrt, hvar]
      unfold HardyWeinbergModel.centeredAltAlleleCount
      rw [h.expectedAltAlleleCount_eq, hhalf]
      simp only [altAlleleCount]
      norm_num

/-- **The floor-two coordinate is Rademacher at the balanced locus, hence symmetric.**

`u` takes `+1` on the two homozygotes, of total probability `1/2`, and `-1` on the
heterozygote, of probability `1/2`. So the law of `u` puts equal mass on `+1` and `-1`.

Do not read the non-negativity of the *uncentered* square as asymmetry here. The
uncentered square is never symmetric, but the tower's floor-two coordinate is the
*centered* square, and at `q = 1/2` that is symmetric. The balanced locus is therefore
degenerate at both floors.

**A subtlety worth recording.** The law of `u` is symmetric here, but no
`SymmetricCoding DiploidGenotype` realizes it: a value-negating relabelling would have to
send the heterozygote, of weight `1/2`, to a genotype of weight `1/2` carrying value `+1`,
and the `+1` mass is split between two atoms of weight `1/4`. So `SymmetricCoding` is
strictly stronger than symmetry of the law, and the coding-level detector used by
`sign_erasure` cannot settle floor-two questions. The moment detector below is what
settles them. -/
theorem centeredSquare_rademacher_at_half (h : HardyWeinbergModel)
    (hhalf : h.altFreq = 1 / 2) :
    h.genotypeProb DiploidGenotype.homRef + h.genotypeProb DiploidGenotype.homAlt = 1 / 2 ∧
      h.genotypeProb DiploidGenotype.het = 1 / 2 := by
  constructor <;>
    · simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq, hhalf]
      norm_num

/-- **The floor-two odd part in closed form**: `E[u³] = (E[x⁴] + 9)(E[x⁴] - 2)`.

Chaining the expansion `E[u³] = E[x⁶] - 3E[x⁴] + 2` with the closed forms
`E[x⁶] = (E[x⁴])² + 10E[x⁴] - 20` and `E[x²] = 1` gives `E[u³] = m₄² + 7m₄ - 18`, which
factors.

The factorization is the content: the floor-two odd part vanishes exactly when
`E[x⁴] = 2`, which is the kurtosis phase boundary, which is the balanced locus. One
quantity, three descriptions. -/
theorem centeredSquare_third_moment_factored (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredSquare g ^ 3 =
      (1 / h.genotypeVariance + 9) * (1 / h.genotypeVariance - 2) := by
  rw [centeredSquare_third_moment_eq h hq0 hq1,
    standardizedGenotype_sixth_moment h hq0 hq1,
    standardizedGenotype_fourth_moment h hq0 hq1,
    standardizedGenotype_second_moment_one h hq0 hq1, h.genotypeProb_sum]
  ring

/-- **The floor-two odd part vanishes exactly at the balanced locus.**

`E[x⁴] ≥ 2` always, so the factor `E[x⁴] + 9` is positive and the product vanishes iff
`E[x⁴] = 2` iff `q = 1/2`. Away from the balanced locus the odd part is strictly positive
and grows without bound as the variant gets rarer, since `E[x⁴] = 1/(2q(1-q))` diverges.

This is the level-two symmetry verdict, and it matches the level-one one: *both* floors are
symmetric at `q = 1/2` and at no other polymorphic frequency. -/
theorem centeredSquare_third_moment_zero_iff_balanced (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∑ g : DiploidGenotype, h.genotypeProb g * h.centeredSquare g ^ 3) = 0 ↔
      1 / h.genotypeVariance = 2 := by
  rw [centeredSquare_third_moment_factored h hq0 hq1]
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hinvpos : 0 < 1 / h.genotypeVariance := by positivity
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hleft | hright
    · linarith [hinvpos, hleft]
    · linarith [hright]
  · intro htwo
    rw [htwo]
    norm_num

/-- **Every even moment, at every order, in cleared form.**

`E[x^(2m)] · V^m = E[(g - 2q)^(2m)]`: the standardization contributes exactly `V^m`
whatever the order, because `(√V)^(2m) = V^m`. This is the general-`m` statement that
the three computed orders are instances of, and it needs no case analysis.

Verified symbolically for `m = 1..5` against the three-point law by
`proofs/validation/coupling/ladder_moments.py`, which reproduces the corpus's closed
forms at `m = 1, 2, 3` as its positive control. -/
theorem standardizedGenotype_even_moment_mul (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (m : ℕ) :
    (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ (2 * m)) *
        h.genotypeVariance ^ m =
      ∑ g : DiploidGenotype, h.genotypeProb g * h.centeredAltAlleleCount g ^ (2 * m) := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hpow : Real.sqrt h.genotypeVariance ^ (2 * m) = h.genotypeVariance ^ m := by
    rw [pow_mul, Real.sq_sqrt hvar.le]
  have hterm : ∀ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedGenotype g ^ (2 * m) =
        h.genotypeProb g * h.centeredAltAlleleCount g ^ (2 * m) /
          h.genotypeVariance ^ m := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    rw [div_pow, hpow]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, div_mul_cancel₀ _ (ne_of_gt (pow_pos hvar m))]

/-- **The even moments diverge at least like `V^(1-m)`.**

Keeping only the heterozygote term of the three gives
`E[x^(2m)] · V^m ≥ V · (1-2q)^(2m)`, that is `E[x^(2m)] ≥ (1-2q)^(2m) / V^(m-1)`. The
other two terms are non-negative, being even powers weighted by probabilities, so
dropping them is legitimate at every order.

This is what turns the ladder's growth claim from a pattern into a theorem. It is a
lower bound rather than the full asymptotic law — the symbolic check finds
`V^(m-1) E[x^(2m)] → 1` at every order through `m = 5`, and `V` divides the numerator
exactly, so that quantity is a polynomial in `q` taking the value `1` at `q = 0` — but
the bound is what the divergence needs, and it holds at every `m` by proof rather than
by inspection of finitely many orders. -/
theorem standardizedGenotype_even_moment_lower_bound (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (m : ℕ) :
    h.genotypeVariance * (1 - 2 * h.altFreq) ^ (2 * m) ≤
      (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ (2 * m)) *
        h.genotypeVariance ^ m := by
  rw [standardizedGenotype_even_moment_mul h hq0 hq1 m]
  have hpow_nonneg : ∀ g : DiploidGenotype,
      0 ≤ h.centeredAltAlleleCount g ^ (2 * m) := by
    intro g
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) m
  have hhet : h.genotypeProb DiploidGenotype.het *
      h.centeredAltAlleleCount DiploidGenotype.het ^ (2 * m) =
        h.genotypeVariance * (1 - 2 * h.altFreq) ^ (2 * m) := by
    have hcentered : h.centeredAltAlleleCount DiploidGenotype.het =
        1 - 2 * h.altFreq := by
      unfold HardyWeinbergModel.centeredAltAlleleCount
      rw [h.expectedAltAlleleCount_eq]
      simp only [altAlleleCount]
    rw [hcentered, h.genotypeVariance_eq]
    simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq]
    ring
  calc h.genotypeVariance * (1 - 2 * h.altFreq) ^ (2 * m)
      = h.genotypeProb DiploidGenotype.het *
          h.centeredAltAlleleCount DiploidGenotype.het ^ (2 * m) := hhet.symm
    _ ≤ ∑ g : DiploidGenotype,
          h.genotypeProb g * h.centeredAltAlleleCount g ^ (2 * m) :=
        Finset.single_le_sum
          (fun g _ ↦ mul_nonneg (h.genotypeProb_nonneg g) (hpow_nonneg g))
          (Finset.mem_univ _)

/-!
### The sign bias of a genotype coordinate, and what is open about it

The Sign-Erasure Lemma kills cross-terms when the coordinate law is symmetric. The
quantity that measures how far a law is from that, and so what survives when it is
not, is the conditional sign bias `b = E[x |x|] / E[x²]` — at unit variance simply
`E[x |x|]`, the mean of the signed square.

For a Hardy-Weinberg coordinate this has a closed form, `b = (1 - 2q)²` below
frequency one half, proved below. It vanishes exactly at `q = 1/2`, which is where
the coding is symmetric, so the Sign-Erasure Lemma is the zero fibre of `b` rather
than a separate phenomenon.

**What is open, and what is ruled out.** `b` does **not** govern a *separate* coupling
channel, and no sliding design carries a tuned-sector variance inflation `2b²/(1 - b²)`.
The vanishing-first-order argument for such a channel uses a `θ = 1/2` weight, which
mixes a level-two normalization into a level-one computation. At the correct weights the
solo-factor mean is `E[(x² - 1) x²] = σ₁² = 2` rather than zero. The first-order cross
term exposes `Λ(2)` data, that is `E[x⁴]`, which the hub channel already exposes. The
term is therefore **hub-redundant, not a new channel**. See
`Calibrator.CondensationUnification` §5j for the full record.

`b` itself is untouched: it is well defined, it vanishes exactly on symmetric laws,
and for genotypes it is `(1 - 2q)²`. What is **open** is whether any admissible design
exposes it at all. Nothing below should be read as asserting that one does. -/

/-- **The sign bias of the standardized genotype at tilt one**: `E[x |x|]`, the mean signed
square. It is the numerator of `b = E[x|x|]/E[x²]`, and the denominator is `1` because the
coordinate is standardized (`standardizedGenotype_second_moment_one`).

Empirical status: DERIVED from `HardyWeinbergModel.standardizedGenotype`; closed form
`(1 - 2q)²` at or below frequency one half (`hweSignBias_eq`), with no free parameter. -/
noncomputable def HardyWeinbergModel.signBias (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * (h.standardizedGenotype g * |h.standardizedGenotype g|)

/-- **The sign bias in closed form: `b = (1 - 2q)²`.**

The three signed squares are `-2q(1-q)`, `(1-2q)²` and `+2q(1-q)`, weighted by the
Hardy-Weinberg probabilities; the two homozygote contributions cancel exactly and the
heterozygote term is what remains.

Stated for `q ≤ 1/2` so the signs of the three centered dosages are determined, which is
the minor-allele convention. It vanishes iff `q = 1/2` and rises to `1` as the variant
becomes rare.

This is arithmetic about the genotype law and stands on its own; it does not depend on
any claim about what a design can see. -/
theorem hweSignBias_eq (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq)
    (hhalf : h.altFreq ≤ 1 / 2) : h.signBias = (1 - 2 * h.altFreq) ^ 2 := by
  have hq1 : h.altFreq < 1 := by linarith
  have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    nlinarith [hq0, hcomp]
  have hs : 0 < Real.sqrt h.genotypeVariance := Real.sqrt_pos.mpr hvar
  have hss : Real.sqrt h.genotypeVariance * Real.sqrt h.genotypeVariance =
      h.genotypeVariance := Real.mul_self_sqrt hvar.le
  have hsigned : ∀ g : DiploidGenotype,
      h.genotypeProb g * (h.standardizedGenotype g * |h.standardizedGenotype g|) =
        h.genotypeProb g *
          (h.centeredAltAlleleCount g * |h.centeredAltAlleleCount g|) / h.genotypeVariance := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype
    rw [abs_div, abs_of_pos hs, div_mul_div_comm, hss]
    ring
  have hcref : h.centeredAltAlleleCount DiploidGenotype.homRef = -(2 * h.altFreq) := by
    unfold HardyWeinbergModel.centeredAltAlleleCount
    rw [h.expectedAltAlleleCount_eq]
    simp only [altAlleleCount]
    ring
  have hchet : h.centeredAltAlleleCount DiploidGenotype.het = 1 - 2 * h.altFreq := by
    unfold HardyWeinbergModel.centeredAltAlleleCount
    rw [h.expectedAltAlleleCount_eq]
    simp only [altAlleleCount]
  have hcalt : h.centeredAltAlleleCount DiploidGenotype.homAlt = 2 - 2 * h.altFreq := by
    unfold HardyWeinbergModel.centeredAltAlleleCount
    rw [h.expectedAltAlleleCount_eq]
    simp only [altAlleleCount]
  unfold HardyWeinbergModel.signBias
  simp_rw [hsigned]
  rw [← Finset.sum_div, sum_over_genotypes, hcref, hchet, hcalt,
    abs_of_nonpos (by linarith : -(2 * h.altFreq) ≤ 0),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * h.altFreq),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - 2 * h.altFreq),
    div_eq_iff (ne_of_gt hvar), h.genotypeVariance_eq]
  simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq]
  ring

/-- **The sign bias vanishes exactly at the balanced locus**, where the coding is
symmetric. So the Sign-Erasure Lemma is the zero fibre of `b` rather than an
independent phenomenon.

This is the whole of what `b` is currently known to do for genotypes. Whether any
admissible design exposes `b` is open; the mechanism this file once asserted for that
was retracted, and no replacement has been supplied. -/
theorem hweSignBias_zero_iff_balanced (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq)
    (hhalf : h.altFreq ≤ 1 / 2) : h.signBias = 0 ↔ h.altFreq = 1 / 2 := by
  rw [hweSignBias_eq h hq0 hhalf]
  constructor
  · intro hzero
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    linarith [this]
  · intro hbal
    rw [hbal]
    norm_num

/-!
### The single-locus collapse

For one locus the tower adds nothing, and the reason is that a standardized
Hardy-Weinberg coordinate has a one-parameter law. Floor one already pins it:
`E[x⁴] = 1/(2q(1-q))` determines the variance, hence the unordered pair
`{q, 1-q}`, and the two members of that pair give laws that differ only by a sign
flip — the coordinate at `1-q` is the negative in distribution of the coordinate
at `q`, since the genotype values reverse while the probabilities swap.

So every even moment agrees across the pair, and floor two is built entirely from
even data: it is the law of `x²`, which is invariant under the flip. The tower
collapses to floor one for a single locus. Panels are where it bites, and that is
`Calibrator.CondensationUnification`.
-/

/-- The reflected locus, at allele frequency `1 - q`. -/
def HardyWeinbergModel.reflect (h : HardyWeinbergModel) : HardyWeinbergModel where
  altFreq := 1 - h.altFreq
  altFreq_nonneg := by linarith [h.altFreq_le_one]
  altFreq_le_one := by linarith [h.altFreq_nonneg]

@[simp] theorem HardyWeinbergModel.reflect_altFreq (h : HardyWeinbergModel) :
    h.reflect.altFreq = 1 - h.altFreq := rfl

/-- Reflection swaps the two homozygote probabilities and fixes the heterozygote:
it is `genotypeFlip` on the probabilities. -/
theorem reflect_genotypeProb (h : HardyWeinbergModel) (g : DiploidGenotype) :
    h.reflect.genotypeProb g = h.genotypeProb (genotypeFlip g) := by
  cases g <;>
    simp only [genotypeFlip_homRef, genotypeFlip_het, genotypeFlip_homAlt,
      HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq,
      HardyWeinbergModel.reflect_altFreq] <;> ring

/-- Reflection preserves the genotype variance: `2(1-q)q = 2q(1-q)`. -/
theorem reflect_genotypeVariance (h : HardyWeinbergModel) :
    h.reflect.genotypeVariance = h.genotypeVariance := by
  rw [h.reflect.genotypeVariance_eq, h.genotypeVariance_eq]
  unfold HardyWeinbergModel.refFreq
  rw [HardyWeinbergModel.reflect_altFreq]
  ring

/-- Reflection negates the centered dosage, after the homozygote swap. -/
theorem reflect_centeredAltAlleleCount (h : HardyWeinbergModel) (g : DiploidGenotype) :
    h.reflect.centeredAltAlleleCount g = -h.centeredAltAlleleCount (genotypeFlip g) := by
  cases g <;>
    · simp only [genotypeFlip_homRef, genotypeFlip_het, genotypeFlip_homAlt,
        HardyWeinbergModel.centeredAltAlleleCount,
        HardyWeinbergModel.expectedAltAlleleCount_eq, altAlleleCount,
        HardyWeinbergModel.reflect_altFreq]
      ring

/-- **The reflected coordinate is the negative of the original.** This is the
whole content of the single-locus collapse: `q` and `1-q` give the same law up to
a sign. -/
theorem reflect_standardizedGenotype (h : HardyWeinbergModel) (g : DiploidGenotype) :
    h.reflect.standardizedGenotype g = -h.standardizedGenotype (genotypeFlip g) := by
  unfold HardyWeinbergModel.standardizedGenotype
  rw [reflect_centeredAltAlleleCount, reflect_genotypeVariance]
  ring

/-- Every moment of the reflected locus is the original's, up to the sign of the
order. -/
theorem reflect_moment (h : HardyWeinbergModel) (k : ℕ) :
    ∑ g : DiploidGenotype, h.reflect.genotypeProb g * h.reflect.standardizedGenotype g ^ k =
      (-1) ^ k * ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ k := by
  have hterm : ∀ g : DiploidGenotype,
      h.reflect.genotypeProb g * h.reflect.standardizedGenotype g ^ k =
        (-1) ^ k * (h.genotypeProb (genotypeFlip g) *
          h.standardizedGenotype (genotypeFlip g) ^ k) := by
    intro g
    rw [reflect_genotypeProb, reflect_standardizedGenotype, neg_pow]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv genotypeFlip
    (fun g ↦ h.genotypeProb (genotypeFlip g) * h.standardizedGenotype (genotypeFlip g) ^ k)
    (fun g ↦ h.genotypeProb g * h.standardizedGenotype g ^ k) (fun _ ↦ rfl)

/-- **Even moments are reflection-invariant.** Floor two is built from the law of
`x²`, which is even data, so it cannot separate `q` from `1-q`. -/
theorem reflect_even_moment (h : HardyWeinbergModel) (k : ℕ) :
    ∑ g : DiploidGenotype,
        h.reflect.genotypeProb g * h.reflect.standardizedGenotype g ^ (2 * k) =
      ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ (2 * k) := by
  rw [reflect_moment, pow_mul]
  norm_num

/-- Two loci with the same allele frequency have the same moments: everything in
sight is a function of `q`. -/
theorem moment_eq_of_altFreq_eq (h h' : HardyWeinbergModel)
    (hfreq : h.altFreq = h'.altFreq) (k : ℕ) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ k =
      ∑ g : DiploidGenotype, h'.genotypeProb g * h'.standardizedGenotype g ^ k := by
  have hprob : ∀ g : DiploidGenotype, h.genotypeProb g = h'.genotypeProb g := by
    intro g
    cases g <;>
      simp only [HardyWeinbergModel.genotypeProb, HardyWeinbergModel.refFreq, hfreq]
  have hstd : ∀ g : DiploidGenotype,
      h.standardizedGenotype g = h'.standardizedGenotype g := by
    intro g
    unfold HardyWeinbergModel.standardizedGenotype HardyWeinbergModel.centeredAltAlleleCount
    rw [h.expectedAltAlleleCount_eq, h'.expectedAltAlleleCount_eq,
      h.genotypeVariance_eq, h'.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    rw [hfreq]
  simp_rw [hprob, hstd]

/-- **The genotype variance determines the frequency pair.** `2q(1-q) = 2q'(1-q')`
forces `q' = q` or `q' = 1 - q`, which is the algebraic half of the collapse. -/
theorem genotypeVariance_determines_frequency_pair (h h' : HardyWeinbergModel)
    (hvar : h.genotypeVariance = h'.genotypeVariance) :
    h'.altFreq = h.altFreq ∨ h'.altFreq = 1 - h.altFreq := by
  rw [h.genotypeVariance_eq, h'.genotypeVariance_eq] at hvar
  unfold HardyWeinbergModel.refFreq at hvar
  have hfactor : (h'.altFreq - h.altFreq) * (h'.altFreq - (1 - h.altFreq)) = 0 := by
    linarith [hvar]
  rcases mul_eq_zero.mp hfactor with hleft | hright
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **The single-locus collapse.** For one Hardy-Weinberg locus the tower adds
nothing: two polymorphic loci with the same fourth moment — a floor-one datum —
have the same law at floor two, and indeed the same even moments of every order.

The proof is the collapse in three steps: equal fourth moments force equal
variance, equal variance forces `q' ∈ {q, 1-q}`, and the reflection identity makes
the second case agree with the first on all even data.

So the tower is not a refinement of single-locus genotype theory. Where it bites
is panels, whose effective coordinate law is a *mixture* over allele frequencies,
and mixtures are not determined by their low-order data. See
`Calibrator.CondensationUnification`. -/
theorem singleLocus_tower_collapses (h h' : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (hq0' : 0 < h'.altFreq) (hq1' : h'.altFreq < 1)
    (hfourth : (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) =
      ∑ g : DiploidGenotype, h'.genotypeProb g * h'.standardizedGenotype g ^ 4)
    (k : ℕ) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ (2 * k) =
      ∑ g : DiploidGenotype, h'.genotypeProb g * h'.standardizedGenotype g ^ (2 * k) := by
  rw [standardizedGenotype_fourth_moment h hq0 hq1,
    standardizedGenotype_fourth_moment h' hq0' hq1'] at hfourth
  have hvar : h.genotypeVariance = h'.genotypeVariance := by
    calc h.genotypeVariance = 1 / (1 / h.genotypeVariance) := (one_div_one_div _).symm
      _ = 1 / (1 / h'.genotypeVariance) := by rw [hfourth]
      _ = h'.genotypeVariance := one_div_one_div _
  rcases genotypeVariance_determines_frequency_pair h h' hvar with hsame | hrefl
  · exact moment_eq_of_altFreq_eq h h' hsame.symm (2 * k)
  · have hreflected : h.reflect.altFreq = h'.altFreq := hrefl.symm
    calc ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ (2 * k)
        = ∑ g : DiploidGenotype,
            h.reflect.genotypeProb g * h.reflect.standardizedGenotype g ^ (2 * k) :=
          (reflect_even_moment h k).symm
      _ = ∑ g : DiploidGenotype, h'.genotypeProb g * h'.standardizedGenotype g ^ (2 * k) :=
          moment_eq_of_altFreq_eq h.reflect h' hreflected (2 * k)

/-! ### The design: locus-sets over a Hardy-Weinberg panel -/

/-- A **design over a genotype panel**: the locus-sets a study tests, the
coefficient each contributes, the allele frequency of every locus, and the
population's joint genotype law over the panel.

The joint law is carried alongside the per-locus models so that linkage
equilibrium is a checkable relation between them
(`GenotypeDesign.InLinkageEquilibrium`) rather than a silent assumption; the
disjoint licence needs it, and a design whose tested sets sit inside one LD block
does not have it. -/
structure GenotypeDesign (n : ℕ) (ι : Type*) where
  /-- The Hardy-Weinberg model of each locus on the panel. -/
  model : Fin n → HardyWeinbergModel
  /-- The loci entering tested set `s`; its cardinality is the interaction order. -/
  locusSet : ι → Finset (Fin n)
  /-- The coefficient of the corresponding interaction monomial. -/
  coefficient : ι → ℝ
  /-- The population's joint genotype law over the panel. -/
  jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ

namespace GenotypeDesign

section Definitions

variable (design : GenotypeDesign n ι)

/-- The interaction order of a tested set: the number of loci in it.

Empirical status: UNTESTED. A cardinality read off the design; no free parameter
and nothing fitted. -/
def interactionOrder (s : ι) : ℕ := (design.locusSet s).card

/-- The test statistic: `∑_s c_s ∏_{i ∈ S_s} x_i` in the standardized genotypes
`HardyWeinbergModel.standardizedGenotype` of the panel's own allele frequencies.

Empirical status: UNTESTED. The multilinear statistic the chaos theory is about,
written in the corpus's standardized coordinate; no free parameter beyond the
design's own coefficients. -/
noncomputable def statistic (x : Fin n → DiploidGenotype) : ℝ :=
  ∑ s : ι, design.coefficient s *
    ∏ i ∈ design.locusSet s, (design.model i).standardizedGenotype (x i)

/-- **Linkage equilibrium across the tested panel**: the joint genotype law
factorizes into the per-locus Hardy-Weinberg laws. It is stated as the
factorization it is; the dynamics that drive a population towards it live in
`Calibrator.LDDecayTheory`.

This is an assumption about the population, not about the coding, and it is what
the disjoint licence needs in place of symmetry. A design whose tested sets sit
inside one LD block does not have it, which makes the licence's applicability
checkable on a study's own panel rather than on an idealized coordinate law.

Note for automated checking: this is a *predicate* on a design, not a stipulated
equilibrium quantity. There is no one-step map here and nothing for a
`_isFixedPoint` theorem to be about; the recombination dynamics that have a fixed
point live in `Calibrator.LDDecayTheory`.

Empirical status: UNTESTED. A factorization condition on the joint law; testable
directly as pairwise LD between panel loci. -/
def InLinkageEquilibrium : Prop :=
  ∀ x : Fin n → DiploidGenotype,
    design.jointGenotypeProb x = ∏ i, (design.model i).genotypeProb (x i)

/-- Every panel locus is polymorphic, so the standardized coordinate exists and
has unit variance.

Empirical status: UNTESTED. A range condition on the panel's allele frequencies. -/
def Polymorphic : Prop :=
  ∀ i : Fin n, 0 < (design.model i).altFreq ∧ (design.model i).altFreq < 1

/-- **The disjointness hypothesis, as a property of the design.** No variant
enters two tested sets.

This is what Theorem D needs and what Theorem S is the failure of. It is a named
predicate so that every result depending on it carries it as an argument rather
than in prose. Gene-based burden tests over non-overlapping genes have it
(`geneBurdenDesign_variantDisjoint`); sliding windows never do
(`slidingWindowDesign_not_variantDisjoint`); a pathway panel has it only if no
gene belongs to two pathways.

Empirical status: UNTESTED. A structural property of a study design, checkable by
inspection and requiring no measurement. -/
def VariantDisjoint : Prop :=
  ∀ s t : ι, s ≠ t → Disjoint (design.locusSet s) (design.locusSet t)

/-- **The variant-recurrence profile**: how many tested sets a variant enters.
This is the statistic permutation and resampling schemes preserve, and
`Calibrator.CondensationUnification` shows it does not fix the null.

Empirical status: UNTESTED. A count read off the design; no free parameter and
nothing fitted. -/
def variantRecurrence (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun s ↦ i ∈ design.locusSet s)).card

/-- **The influence of a variant**: the share of the statistic's energy carried
by locus `i`, namely the total squared coefficient of the tested sets containing
it. Admissibility asks that this vanish uniformly in `i`.

Empirical status: UNTESTED. An energy share read off the design's coefficients;
no free parameter and nothing fitted. -/
def locusInfluence (i : Fin n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s ↦ i ∈ design.locusSet s), design.coefficient s ^ 2

theorem locusInfluence_nonneg (i : Fin n) : 0 ≤ design.locusInfluence i :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- **Flip the orientation of one locus.** Choosing the other allele as reference
negates that coordinate, so every tested set containing the locus has its monomial
negated; the design absorbing that is the one with those coefficients negated.

Empirical status: DERIVED. A relabelling of the design's own coefficients, with no
modelling content and no free parameter. -/
def flipOrientation (locus : Fin n) : GenotypeDesign n ι where
  model := design.model
  locusSet := design.locusSet
  coefficient := fun s ↦
    if locus ∈ design.locusSet s then -design.coefficient s else design.coefficient s
  jointGenotypeProb := design.jointGenotypeProb

/-- **The two-pool interaction design**: two disjoint pools of loci, with the
tested sets being the cross-pool pairs and at least one tested set per pair.

This is the formal shape of a two-gene-set interaction test, and the design whose
limit is a product of two independent Gaussians.

Empirical status: UNTESTED. A study design, not a claim about data; it constrains
the locus-sets only, never the allele frequencies, which is what makes the
fourth-cumulant separation uniform over the frequency spectrum. -/
def IsTwoPoolInteraction (poolOne poolTwo : Finset (Fin n)) : Prop :=
  Disjoint poolOne poolTwo ∧ poolOne.Nonempty ∧ poolTwo.Nonempty ∧
    (∀ s : ι, ∃ i ∈ poolOne, ∃ j ∈ poolTwo, design.locusSet s = {i, j}) ∧
    (∀ i ∈ poolOne, ∀ j ∈ poolTwo, ∃ s : ι, design.locusSet s = {i, j})

end Definitions

/-!
### Orientation equivariance of the admissible class

Which allele is called "reference" is a **gauge choice**, and the question is whether
the admissible class is closed under changing it at one locus. It is, and the reason is
that every admissibility condition reads only `|coefficient|` and `locusSet`, both of
which a flip preserves.

**But closure of the class is not invariance of a design's limit**, and the gauge
objection lives in exactly that gap. Flipping locus `i` also flips its effect `β_i`, and
the phenotype `x_i β_i` is unchanged, so a design whose coefficients come from effect
estimates flips with the coordinate and the two flips cancel. The criterion is sharp:

> orientation randomization genuinely symmetrizes what a design sees **iff the design's
> coefficients are chosen independently of the orientation**.

A genotype-only interaction scan qualifies, and `GenotypeDesign` enforces it at the type
level: `coefficient` is a field that cannot depend on `model`. An effect-weighted
statistic does not qualify, and there the induced correlation between orientation and
`sign β_i` is precisely the joint law the objection points at. So the answer is not a
single verdict — it is yes for unweighted scans and no for effect-weighted ones.

Either way the randomization buys exactly one floor: squaring kills the sign, so floor
two is untouched and remains never symmetric away from `q = 1/2`
(`Calibrator.CondensationUnification.centeredSquare_third_moment_zero_iff_balanced`).
-/

/-- Flipping preserves the tested locus-sets, so interaction order, the recurrence
profile and disjointness are all untouched — each reads only `locusSet`. -/
theorem flipOrientation_locusSet {design : GenotypeDesign n ι} (locus : Fin n) (s : ι) :
    (design.flipOrientation locus).locusSet s = design.locusSet s := rfl

/-- Disjointness is orientation-invariant. -/
theorem flipOrientation_variantDisjoint_iff {design : GenotypeDesign n ι}
    (locus : Fin n) :
    (design.flipOrientation locus).VariantDisjoint ↔ design.VariantDisjoint := Iff.rfl

/-- The recurrence profile is orientation-invariant. -/
theorem flipOrientation_variantRecurrence {design : GenotypeDesign n ι}
    (locus i : Fin n) :
    (design.flipOrientation locus).variantRecurrence i = design.variantRecurrence i := rfl

/-- **Every influence is orientation-invariant**, since influence sums squared
coefficients and a flip only changes signs. -/
theorem flipOrientation_locusInfluence {design : GenotypeDesign n ι} (locus i : Fin n) :
    (design.flipOrientation locus).locusInfluence i = design.locusInfluence i := by
  have hdef : ∀ d : GenotypeDesign n ι, d.locusInfluence i =
      ∑ s ∈ Finset.univ.filter (fun s ↦ i ∈ d.locusSet s), d.coefficient s ^ 2 :=
    fun _ ↦ rfl
  rw [hdef, hdef]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  show (if locus ∈ design.locusSet s then -design.coefficient s
        else design.coefficient s) ^ 2 = design.coefficient s ^ 2
  by_cases hs : locus ∈ design.locusSet s
  · rw [if_pos hs, neg_sq]
  · rw [if_neg hs]

/-- **The total energy is orientation-invariant**, so the unit-variance normalization
survives a flip. With the three facts above, the admissible class — diverging minimum
order, vanishing influence, unit variance — is closed under per-coordinate sign flips. -/
theorem flipOrientation_energy {design : GenotypeDesign n ι} (locus : Fin n) :
    ∑ s : ι, (design.flipOrientation locus).coefficient s ^ 2 =
      ∑ s : ι, design.coefficient s ^ 2 := by
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  show (if locus ∈ design.locusSet s then -design.coefficient s
        else design.coefficient s) ^ 2 = design.coefficient s ^ 2
  by_cases hs : locus ∈ design.locusSet s
  · rw [if_pos hs, neg_sq]
  · rw [if_neg hs]

/-- Under disjointness a variant determines the tested set it belongs to. -/
theorem unique_set_of_variantDisjoint {design : GenotypeDesign n ι}
    (hdisjoint : design.VariantDisjoint)
    {i : Fin n} {s t : ι}
    (hs : i ∈ design.locusSet s) (ht : i ∈ design.locusSet t) : s = t := by
  by_contra hne
  exact (Finset.disjoint_left.mp (hdisjoint s t hne) hs) ht

/-- Disjointness is the statement that every variant is tested at most once,
which is how a practitioner would check it on a panel. -/
theorem variantRecurrence_le_one_of_disjoint {design : GenotypeDesign n ι}
    (hdisjoint : design.VariantDisjoint)
    (i : Fin n) : design.variantRecurrence i ≤ 1 := by
  have hdef : design.variantRecurrence i =
      (Finset.univ.filter (fun s ↦ i ∈ design.locusSet s)).card := rfl
  rw [hdef, Finset.card_le_one]
  intro s hs t ht
  exact unique_set_of_variantDisjoint hdisjoint
    (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2

/-- **A recurrent variant refutes disjointness.** If one variant enters two
distinct tested sets — one SNP in two sliding windows, one gene in two pathways,
one pleiotropic variant in two panels — the design is not disjoint and the
licence below does not apply to it. -/
theorem not_variantDisjoint_of_recurrent {design : GenotypeDesign n ι}
    {i : Fin n} {s t : ι} (hst : s ≠ t)
    (hs : i ∈ design.locusSet s) (ht : i ∈ design.locusSet t) :
    ¬ design.VariantDisjoint := by
  intro hdisjoint
  exact hst (unique_set_of_variantDisjoint hdisjoint hs ht)

/-- Under disjointness the influence of a variant is exactly the squared
coefficient of the single set that tests it, so influence control is a per-term
condition. Under overlap the influence aggregates across sets, which is how a
design can be admissible and maximally recurrent at once. -/
theorem locusInfluence_eq_of_disjoint {design : GenotypeDesign n ι}
    (hdisjoint : design.VariantDisjoint)
    {i : Fin n} {s : ι} (hi : i ∈ design.locusSet s) :
    design.locusInfluence i = design.coefficient s ^ 2 := by
  have hfilter : Finset.univ.filter (fun t ↦ i ∈ design.locusSet t) = {s} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hi⟩
    · intro t ht
      exact unique_set_of_variantDisjoint hdisjoint (Finset.mem_filter.mp ht).2 hi
  have hdef : design.locusInfluence i =
      ∑ t ∈ Finset.univ.filter (fun t ↦ i ∈ design.locusSet t),
        design.coefficient t ^ 2 := rfl
  rw [hdef, hfilter, Finset.sum_singleton]

end GenotypeDesign

/-! ### The two classes of set-based test, concretely -/

/-- **A gene-based burden or kernel design**: each panel variant is assigned to
one gene by `geneOf`, and the tested set of a gene is the variants assigned to
it.

Empirical status: UNTESTED. A study design, not a claim about data; it is the
formal shape of a gene-based burden or kernel scan over non-overlapping genes. -/
def geneBurdenDesign {γ : Type*} [DecidableEq γ] (model : Fin n → HardyWeinbergModel)
    (geneOf : Fin n → γ) (coeff : γ → ℝ)
    (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ) : GenotypeDesign n γ where
  model := model
  locusSet := fun g ↦ Finset.univ.filter (fun i ↦ geneOf i = g)
  coefficient := coeff
  jointGenotypeProb := jointGenotypeProb

/-- **Gene-based burden over non-overlapping genes is disjoint**, because each
variant has one gene. This is the hypothesis of the licence, discharged for the
first of the two classes. -/
theorem geneBurdenDesign_variantDisjoint {γ : Type*} [DecidableEq γ]
    (model : Fin n → HardyWeinbergModel) (geneOf : Fin n → γ) (coeff : γ → ℝ)
    (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ) :
    (geneBurdenDesign model geneOf coeff jointGenotypeProb).VariantDisjoint := by
  intro g g' hne
  rw [Finset.disjoint_left]
  intro i hi hi'
  have hig : i ∈ Finset.univ.filter (fun j ↦ geneOf j = g) := hi
  have hig' : i ∈ Finset.univ.filter (fun j ↦ geneOf j = g') := hi'
  exact hne (((Finset.mem_filter.mp hig).2).symm.trans (Finset.mem_filter.mp hig').2)

/-- **A sliding-window design**: the tested set at start `k` is the block of
`width` consecutive panel positions beginning at `k`.

Empirical status: UNTESTED. A study design, not a claim about data; it is the
formal shape of a sliding-window interaction or kernel scan. -/
def slidingWindowDesign (model : Fin n → HardyWeinbergModel) (width : ℕ)
    (coeff : Fin n → ℝ) (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ) :
    GenotypeDesign n (Fin n) where
  model := model
  locusSet := fun k ↦
    Finset.univ.filter (fun i : Fin n ↦ (k : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k : ℕ) + width)
  coefficient := coeff
  jointGenotypeProb := jointGenotypeProb

/-- **Sliding windows are never disjoint** once the window is wider than one
locus: consecutive windows share the variant at the later start position. The
licence below therefore does not apply to any sliding-window scan, and by
Theorem S its achievable nulls are the whole moment body. -/
theorem slidingWindowDesign_not_variantDisjoint
    (model : Fin n → HardyWeinbergModel) (width : ℕ)
    (coeff : Fin n → ℝ) (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ)
    (hwidth : 2 ≤ width) (k k' j : Fin n)
    (hstep : (k : ℕ) + 1 = (k' : ℕ)) (hj : (j : ℕ) = (k' : ℕ)) :
    ¬ (slidingWindowDesign model width coeff jointGenotypeProb).VariantDisjoint := by
  have hne : k ≠ k' := by
    intro hEq
    rw [hEq] at hstep
    omega
  have hmem : j ∈ (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k := by
    have hset : (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k =
        Finset.univ.filter
          (fun i : Fin n ↦ (k : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k : ℕ) + width) := rfl
    rw [hset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by omega, by omega⟩
  have hmem' : j ∈ (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k' := by
    have hset : (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k' =
        Finset.univ.filter
          (fun i : Fin n ↦ (k' : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k' : ℕ) + width) := rfl
    rw [hset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by omega, by omega⟩
  exact GenotypeDesign.not_variantDisjoint_of_recurrent hne hmem hmem'

/-! The Gaussian-segment and maximal-spectrum claims formerly appeared as theorem-valued
fields of `GenotypeChaosLimits`.  That interface and its projection theorems are removed;
the finite genotype-design algebra below is retained. -/

/-!
### The two-pool interaction statistic, and what is actually proved about it

Split the panel into two pools of loci with no variant in common, let `T₁` and
`T₂` be the standardized sums over each pool, and test the two-way interaction
statistic `f = T₁ * T₂` — the plainest thing written down when asking whether two
gene sets interact. Its tested sets are the cross-pool pairs `{i, j}`, so it is an
interaction design of order two with equal coefficients.

The informal reading is that each pool sum is asymptotically standard Gaussian
and the two are independent under linkage equilibrium, so the limit is a product
of two independent standard Gaussians, whose fourth cumulant is
`E[(Z₁Z₂)⁴] - 3 (E[(Z₁Z₂)²])² = 9 - 3 = 6`, away from the `0` that a Gaussian
limit would give.

**That reading is not what this section proves, and none of it is formalized
here.** There is no central limit theorem, no independence hypothesis, and no
asymptotic statement anywhere below. What is proved is:

* `twoPool_expansion` — the product of the two pool sums is the sum of the
  cross-pool terms. Finite algebra.
* `twoPool_pairs_overlap`, `twoPool_not_variantDisjoint` — the design is not
  variant-disjoint once the second pool holds two loci, so the licence of
  Theorem D does not cover it.
* `fourthCumulantFromMoments_gaussian` — Gaussian moments give fourth cumulant
  `0`.
* `fourthCumulantFromMoments_of_squared_standard_moments` — *if* the product law's second and
  fourth moments are `1 * 1` and `3 * 3`, its fourth cumulant is `6`. The
  hypotheses supply those moments; the multiplicativity that a real independence
  argument would have to establish is written into the statement rather than
  derived, and no allele frequency appears in it, so this is arithmetic on
  assumed moments and not a uniformity result over frequency spectra.

Everything asymptotic in the paragraph above is a claim about the intended
model, carried in prose, not a theorem of this file.
-/

/-- The statistic written out: the product of the two pool sums is the sum of the
cross-pool interaction terms, one per tested set. -/
theorem twoPool_expansion (x : Fin n → ℝ) (poolOne poolTwo : Finset (Fin n)) :
    (∑ i ∈ poolOne, x i) * (∑ j ∈ poolTwo, x j) =
      ∑ i ∈ poolOne, ∑ j ∈ poolTwo, x i * x j := by
  rw [Finset.sum_mul_sum]

/-- Two cross-pool pairs sharing their first locus are distinct sets that are not
disjoint. -/
theorem twoPool_pairs_overlap {poolOne poolTwo : Finset (Fin n)}
    (hpools : Disjoint poolOne poolTwo) {i j k : Fin n}
    (hi : i ∈ poolOne) (hj : j ∈ poolTwo) (hjk : j ≠ k) :
    ({i, j} : Finset (Fin n)) ≠ ({i, k} : Finset (Fin n)) ∧
      ¬ Disjoint ({i, j} : Finset (Fin n)) ({i, k} : Finset (Fin n)) := by
  have hji : j ≠ i := by
    intro hcontra
    subst hcontra
    exact (Finset.disjoint_left.mp hpools hi) hj
  constructor
  · intro hEq
    have hmemj : j ∈ ({i, j} : Finset (Fin n)) := by simp
    rw [hEq] at hmemj
    rcases Finset.mem_insert.mp hmemj with hleft | hright
    · exact hji hleft
    · exact hjk (Finset.mem_singleton.mp hright)
  · refine Finset.not_disjoint_iff.mpr ⟨i, ?_, ?_⟩ <;> simp

/-- **The witness design is not disjoint**, as soon as the second pool holds two
loci: the two cross-pairs at a fixed first locus are distinct tested sets sharing
that locus. So the witness is an admissible design outside the reach of the
licence — which is what makes it a witness rather than a counterexample to
Theorem D. -/
theorem twoPool_not_variantDisjoint {design : GenotypeDesign n ι}
    {poolOne poolTwo : Finset (Fin n)}
    (hwitness : design.IsTwoPoolInteraction poolOne poolTwo)
    {i j k : Fin n} (hi : i ∈ poolOne) (hj : j ∈ poolTwo) (hk : k ∈ poolTwo)
    (hjk : j ≠ k) : ¬ design.VariantDisjoint := by
  obtain ⟨hpools, _, _, _, hcover⟩ := hwitness
  obtain ⟨s, hs⟩ := hcover i hi j hj
  obtain ⟨t, ht⟩ := hcover i hi k hk
  obtain ⟨hsetne, _⟩ := twoPool_pairs_overlap hpools hi hj hjk
  have hst : s ≠ t := by
    intro hEq
    rw [hEq, ht] at hs
    exact hsetne hs.symm
  have hmem : i ∈ design.locusSet s := by
    rw [hs]
    simp
  have hmem' : i ∈ design.locusSet t := by
    rw [ht]
    simp
  exact GenotypeDesign.not_variantDisjoint_of_recurrent hst hmem hmem'

/-- Fourth cumulant of a centered law in terms of its second and fourth moments,
`κ₄ = m₄ - 3 m₂²`.

Empirical status: UNTESTED as a claim about any particular statistic; as an
identity it is the definition of the fourth cumulant of a centered law, with no
free parameter. -/
def fourthCumulantFromMoments (secondMoment fourthMoment : ℝ) : ℝ :=
  fourthMoment - 3 * secondMoment ^ 2

/-- A centered Gaussian has vanishing fourth cumulant whatever its variance: the
order-four content of Theorem D's segment. -/
theorem fourthCumulantFromMoments_gaussian (s2 : ℝ) :
    fourthCumulantFromMoments s2 (3 * s2 ^ 2) = 0 := by
  unfold fourthCumulantFromMoments
  ring

/-- **The moment arithmetic.** Given a second moment of `1` and a fourth moment of `3` —
the standard-law values a central limit theorem would supply, assumed here rather than
proved — the products `1 * 1` and `3 * 3` have fourth cumulant `6`.

The name used to be `twoPool_interaction_fourthCumulant`, which asserted a two-pool
epistatic interaction for a statement containing no pool and no interaction. The prose
below always said so; the name did not, and a name is what gets cited. It now describes
the arithmetic it performs.

What the statement does *not* contain: any pool, any genotype, any allele
frequency, any independence hypothesis, and any limit. Writing the product law's
moments as `m₂ * m₂` and `m₄ * m₄` is the independence assumption, applied in the
statement rather than derived from a joint distribution. Because no frequency
appears, the absence of frequencies here is not a uniformity theorem over the
frequency spectrum; it is the absence of the model. -/
theorem fourthCumulantFromMoments_of_squared_standard_moments
    (poolSecondMoment poolFourthMoment : ℝ)
    (hsecond : poolSecondMoment = 1) (hfourth : poolFourthMoment = 3) :
    fourthCumulantFromMoments (poolSecondMoment * poolSecondMoment)
      (poolFourthMoment * poolFourthMoment) = 6 := by
  subst hsecond
  subst hfourth
  unfold fourthCumulantFromMoments
  norm_num

/-- Six is not zero. Recorded so that the gap from the Gaussian value `0` of
`fourthCumulantFromMoments_gaussian` is stated rather than left to the reader.
The name records where the fact is used; the content is arithmetic on two
numerals and carries no genetics. -/
theorem twoPool_fourthCumulant_ne_zero : (6 : ℝ) ≠ 0 := by norm_num

/-!
### Spectral, not profile: the null is not a function of the overlap counts

The limit law of an overlapping design is a *spectral* invariant of its overlap
structure. Two designs on the same panel can agree in every profile functional —
hub energies at every order and size, coefficient-magnitude multisets, supports
up to relabelling, truncated variances, and the variant-recurrence profile
`GenotypeDesign.variantRecurrence` — and still have different nulls, because
those functionals do not determine the spectrum.

The witness is a pair of `8 × 8` circulant matrices with palindromic offset
vectors `(0,1,2,0,0,0,2,1)` and `(0,2,1,0,0,0,1,2)`, lifted over eight pools of
loci as `f = ∑_{i ≠ j} A_ij T_i T_j`. Each matrix has the same entry multiset
`{0,0,0,0,1,1,2,2}` in every row and the same row sum `6`, so every profile
functional agrees; the limits are `∑_k λ_k (W_k² - 1)` in the circulant
eigenvalues, and the eigenvalue multisets differ.

A circulant with offsets `a` has eigenvalues `λ_k = ∑_r a_r ω^{kr}` at the eighth
roots of unity. Both offset vectors are palindromic, so the imaginary parts cancel
and `λ_k` is real; writing `θ = 2πk/8` and `c = cos θ`, and using
`cos 2θ = 2c² - 1`, the eigenvalue functions are the quadratics below. Their
ranges differ, and that is proved.

**What the circulant hypothesis is and is not doing here.** It is a *computing*
device: circulant structure is what diagonalizes the overlap operator in closed
form, so the two spectra can be written down and separated by hand. It is not
supplying a rigidity, identifiability or detectability conclusion, and no theorem
in this file infers "nothing can imitate this design" from circulant, Toeplitz,
stationary or exchangeable structure. The distinction matters because
`BackgroundClass.not_isNull_spiked_of_active` of
`Calibrator.PCCorrectability.ImitationCapacity` shows
that resistance to imitation is a normal-cone condition — an active constraint
with positive load on the spike direction — and needs no transitive symmetry at
all, so a symmetry hypothesis carried for *that* purpose would be removable.
Here there is nothing to remove: the methodological conclusion,
`Calibrator.CondensationUnification.recurrence_preserving_resampling_is_not_a_calibration`,
carries no symmetry hypothesis of any kind. It takes the change of null under
resampling as an argument, and the circulant pair is one way to discharge that
argument; any other pair of designs with equal recurrence profile and different
overlap spectra discharges it equally.
-/

/-- Eigenvalue of the circulant with offsets `(0,1,2,0,0,0,2,1)` as a polynomial
in `c = cos θ`, from `λ = 2 cos θ + 4 cos 2θ`.

Empirical status: UNTESTED. Algebra on one fixed integer matrix; no modelling
content and no free parameter. -/
def circulantSpectrumA (c : ℝ) : ℝ := 8 * c ^ 2 + 2 * c - 4

/-- Eigenvalue of the circulant with offsets `(0,2,1,0,0,0,1,2)` as a polynomial
in `c = cos θ`, from `λ = 4 cos θ + 2 cos 2θ`.

Empirical status: UNTESTED. As for `circulantSpectrumA`: algebra on one fixed
integer matrix, no free parameter. -/
def circulantSpectrumB (c : ℝ) : ℝ := 4 * c ^ 2 + 4 * c - 2

/-- The reduction to a quadratic in `cos θ` for the first circulant. -/
theorem circulantSpectrumA_eq_cos (θ : ℝ) :
    2 * Real.cos θ + 4 * Real.cos (2 * θ) = circulantSpectrumA (Real.cos θ) := by
  rw [Real.cos_two_mul]
  unfold circulantSpectrumA
  ring

/-- The reduction to a quadratic in `cos θ` for the second circulant. -/
theorem circulantSpectrumB_eq_cos (θ : ℝ) :
    4 * Real.cos θ + 2 * Real.cos (2 * θ) = circulantSpectrumB (Real.cos θ) := by
  rw [Real.cos_two_mul]
  unfold circulantSpectrumB
  ring

/-- The first circulant has eigenvalue `-4`, at the quarter turn `θ = π/2` where
`cos θ = 0`, that is at `k = 2`. -/
theorem circulantSpectrumA_at_quarter_turn : circulantSpectrumA 0 = -4 := by
  unfold circulantSpectrumA
  norm_num

/-- The second circulant never attains `-4`, at any angle: completing the square,
`λ + 4 = (2c + 1)² + 1 ≥ 1`. This is stronger than needed — it rules `-4` out over
all real `c`, not only at the eighth roots of unity. -/
theorem circulantSpectrumB_ne_neg_four (c : ℝ) : circulantSpectrumB c ≠ -4 := by
  intro hcontra
  unfold circulantSpectrumB at hcontra
  nlinarith [sq_nonneg (2 * c + 1)]

/-- **The spectra differ.** An eigenvalue of the first palindromic circulant is
attained by the second at no angle. Since the limit is determined by the
eigenvalue multiset and the profile functionals are not, the null is not a
function of the profile. -/
theorem palindromic_circulant_spectra_differ :
    ∃ c : ℝ, ∀ c' : ℝ, circulantSpectrumA c ≠ circulantSpectrumB c' := by
  refine ⟨0, fun c' hcontra ↦ ?_⟩
  rw [circulantSpectrumA_at_quarter_turn] at hcontra
  exact circulantSpectrumB_ne_neg_four c' hcontra.symm

end OverlapSpectrum

section StarVersusCycle

/-!
## Star statistics versus cycle statistics, and the tempered regime

The overlap results above leave a practical gap: they say a checklist of design
summaries cannot certify a null, but not what would. The gap closes with a
diagnosis of *why* each failed summary failed.

Every invariant that turned out not to determine the limit — coefficient
profiles, column masses, signed hub energies, and the variant-recurrence profile
`GenotypeDesign.variantRecurrence` — is a **star** density: a sum over walks
leaving a single tested set and returning nowhere. The limit law lives in
**cycle** densities: sums over closed walks in the overlap structure. A star
density cannot see a cycle, which is why no amount of recurrence matching pins
the null, and why the diagram family does pin it — it contains the cycles.

`GenotypeDesign.overlapMatrix` is the overlap structure of a design: entry
`(s, t)` is the number of variants tested by both sets. Its `p`-th cycle density
is `trace (A ^ p)`, and `overlap_row_sum_eq_recurrence` below proves the
diagnosis in the one case that matters operationally: the recurrence profile is
exactly the row-sum functional of `A`, a star density, and row sums do not
determine the spectrum.

The prescription follows: a resampling or permutation scheme must preserve the
**cycle densities**, and in the quadratic sector the first one that bites is the
fourth, `trace (A ^ 4)`. The palindromic-circulant witness separates precisely
there — equal second cycle densities, forced by the equal entry multiset, and
fourth densities `1840` against `1600`.

The last ingredient is a regime condition, and it is checkable on a panel.
A design is **tempered** when its cycle densities grow at most exponentially in
the diagram size; on that class one truncation level determines the limit, and
moment matching is a valid calibration strategy. Off it there is a divergence
phase in which no finite family of numerical densities determines the limit at
any truncation, and the invariant becomes law-valued. Temperedness fails through
hub energy: a lead variant entering every window of a dense scan, or a
pleiotropic variant recurring across a whole phenotype panel, drives the
recurrence of one variant up with the number of tested sets
(`ubiquitous_variant_forces_hub_bound`). For such designs no moment-matching
calibration can be correct, however many moments are matched.
-/

variable {ιx : Type*} [Fintype ιx] [DecidableEq ιx] {nx : ℕ}

namespace GenotypeDesign

/-- **The overlap structure of a design.** Entry `(s, t)` counts the variants
tested by both set `s` and set `t`; the diagonal is the interaction order. This
is the object whose spectrum the limit law is a function of, and whose row sums
are the recurrence profile.

Empirical status: UNTESTED. A count matrix read off the design; no free parameter
and nothing fitted. -/
def overlapMatrix (design : GenotypeDesign nx ιx) : Matrix ιx ιx ℝ :=
  fun s t ↦ ((design.locusSet s ∩ design.locusSet t).card : ℝ)

/-- The overlap structure is symmetric: sharing is a symmetric relation. -/
theorem overlapMatrix_symm (design : GenotypeDesign nx ιx) (s t : ιx) :
    design.overlapMatrix s t = design.overlapMatrix t s := by
  have hdef : ∀ u v : ιx, design.overlapMatrix u v =
      ((design.locusSet u ∩ design.locusSet v).card : ℝ) := fun _ _ ↦ rfl
  rw [hdef, hdef, Finset.inter_comm]

/-- **The `p`-th cycle density**: `trace (A ^ p)`, the total weight of closed
walks of length `p` in the overlap structure. For `p = 2` it is the squared
Frobenius norm and for `p = 4` the fourth spectral moment.

These are the invariants the limit law is a function of, in contrast to the star
densities of `variantRecurrence`.

Empirical status: UNTESTED. A trace of a power of the overlap count matrix; no
free parameter and nothing fitted. -/
def cycleDensity (design : GenotypeDesign nx ιx) (p : ℕ) : ℝ :=
  Matrix.trace (design.overlapMatrix ^ p)

/-- **Recurrence is a star density.** The row sum of the overlap structure at a
tested set is the total recurrence of the variants in it. So the
variant-recurrence profile is a functional of the row sums of `A` — a sum over
walks out of one vertex — and row sums do not determine the spectrum of a
symmetric matrix.

This is the diagnosis, in the one case a practitioner acts on: matching
recurrence matches a star density and leaves every cycle density free. -/
theorem overlap_row_sum_eq_recurrence (design : GenotypeDesign nx ιx) (s : ιx) :
    ∑ t : ιx, ((design.locusSet s ∩ design.locusSet t).card : ℕ) =
      ∑ i ∈ design.locusSet s, design.variantRecurrence i := by
  have hinter : ∀ t : ιx, design.locusSet s ∩ design.locusSet t =
      (design.locusSet s).filter (fun i ↦ i ∈ design.locusSet t) := by
    intro t
    exact Finset.filter_mem_eq_inter.symm
  have hcard : ∀ t : ιx, (design.locusSet s ∩ design.locusSet t).card =
      ∑ i ∈ design.locusSet s, if i ∈ design.locusSet t then 1 else 0 := by
    intro t
    rw [hinter t, Finset.card_filter]
  have hrec : ∀ i : Fin nx, design.variantRecurrence i =
      ∑ t : ιx, if i ∈ design.locusSet t then 1 else 0 := by
    intro i
    have hdef : design.variantRecurrence i =
        (Finset.univ.filter (fun t ↦ i ∈ design.locusSet t)).card := rfl
    rw [hdef, Finset.card_filter]
  simp_rw [hcard, hrec]
  exact Finset.sum_comm

/-- **The tempered regime.** The cycle densities grow at most exponentially in
the diagram size, so a single truncation level determines the limit law and
moment matching is a valid calibration strategy.

Empirical status: UNTESTED. A growth condition on the design's own cycle
densities; checkable on a panel by computing the overlap structure, with no free
parameter beyond the declared rate. -/
def Tempered (design : GenotypeDesign nx ιx) (rate : ℝ) : Prop :=
  ∀ p : ℕ, |design.cycleDensity p| ≤ rate ^ p

/-- **Bounded hub energy**, in its operational form: no variant is tested more
than `bound` times. This is what fails for a lead variant in a dense sliding
scan, or for a pleiotropic variant across a phenotype panel.

Empirical status: UNTESTED. A bound on the design's own recurrence profile;
checkable by inspection. -/
def BoundedHubRecurrence (design : GenotypeDesign nx ιx) (bound : ℕ) : Prop :=
  ∀ i : Fin nx, design.variantRecurrence i ≤ bound

/-- Every design has bounded hub recurrence at the number of tested sets, since a
    variant cannot be tested more often than there are tests.

    This is the trivial bound and it is stated as such: it inhabits the class so
    the theorem assuming `BoundedHubRecurrence` is not vacuous, while making
    plain that the hypothesis carries no information until `bound` is taken
    strictly below `Fintype.card ιx`. That is exactly the regime the docstring
    describes as failing for a lead variant in a dense sliding scan, where
    recurrence reaches the ceiling `variantRecurrence_eq_card_of_ubiquitous`
    computes. -/
theorem boundedHubRecurrence_card (design : GenotypeDesign nx ιx) :
    BoundedHubRecurrence design (Fintype.card ιx) := fun i ↦ by
  simpa [GenotypeDesign.variantRecurrence, Finset.card_univ] using
    Finset.card_filter_le (Finset.univ : Finset ιx) (fun s ↦ i ∈ design.locusSet s)

/-- A variant entering *every* tested set has recurrence equal to the number of
tested sets. -/
theorem variantRecurrence_eq_card_of_ubiquitous (design : GenotypeDesign nx ιx)
    (i : Fin nx) (hall : ∀ s : ιx, i ∈ design.locusSet s) :
    design.variantRecurrence i = Fintype.card ιx := by
  have hdef : design.variantRecurrence i =
      (Finset.univ.filter (fun s ↦ i ∈ design.locusSet s)).card := rfl
  have hfilter : Finset.univ.filter (fun s ↦ i ∈ design.locusSet s) = Finset.univ :=
    Finset.filter_true_of_mem (fun s _ ↦ hall s)
  rw [hdef, hfilter, Finset.card_univ]

/-- **A ubiquitous variant forces the hub bound up with the number of tested
sets.** A lead variant present in every window of a dense scan, or a pleiotropic
variant in every panel of a phenome-wide scan, makes any hub bound at least as
large as the design itself — so along a family of scans with more and more tested
sets there is no bound uniform in panel size, and temperedness is lost. -/
theorem ubiquitous_variant_forces_hub_bound (design : GenotypeDesign nx ιx)
    (i : Fin nx) (hall : ∀ s : ιx, i ∈ design.locusSet s) (bound : ℕ)
    (hhub : design.BoundedHubRecurrence bound) : Fintype.card ιx ≤ bound := by
  have hrec := design.variantRecurrence_eq_card_of_ubiquitous i hall
  have hle := hhub i
  rw [hrec] at hle
  exact hle

end GenotypeDesign

/-! Cycle determinacy remains a target theorem.  The former theorem-valued record and its
projection consequences are removed; only the directly proved finite cycle-density
computations below remain. -/

/-!
### The witness, in cycle densities

The two palindromic circulants of the previous section, read as overlap
structures. Their eigenvalues are the values of `circulantSpectrumA` and
`circulantSpectrumB` at the eight cosines `cos (2πk/8)`, which take the five
values `1`, `s/2`, `0`, `-s/2`, `-1` with multiplicities `1, 2, 2, 2, 1`, where
`s` is a square root of two. Cycle densities are then power sums of eigenvalues,
which is how `trace (A ^ p)` is computed for a circulant.

The second densities agree, at `80` — forced, since both matrices have the same
entry multiset and the second density is the squared Frobenius norm. The fourth
densities are `1840` and `1600`. So the pair is separated by the first cycle
density that the shared profile does not already fix, and a scheme matching only
the recurrence profile is matching star densities while this quantity moves.
-/

/-- The eigenvalue at `cos 0 = 1`. -/
theorem circulantSpectrumA_at_one : circulantSpectrumA 1 = 6 := by
  unfold circulantSpectrumA
  norm_num

/-- The eigenvalue at `cos π = -1`. -/
theorem circulantSpectrumA_at_neg_one : circulantSpectrumA (-1) = 2 := by
  unfold circulantSpectrumA
  norm_num

/-- The eigenvalue at `cos (π/4) = s/2` with `s² = 2`. -/
theorem circulantSpectrumA_at_root (s : ℝ) (hs : s ^ 2 = 2) :
    circulantSpectrumA (s / 2) = s := by
  unfold circulantSpectrumA
  linarith [hs]

/-- The eigenvalue at `cos (3π/4) = -s/2`. -/
theorem circulantSpectrumA_at_neg_root (s : ℝ) (hs : s ^ 2 = 2) :
    circulantSpectrumA (-(s / 2)) = -s := by
  unfold circulantSpectrumA
  linarith [hs]

/-- The eigenvalue at `cos 0 = 1`, second circulant. -/
theorem circulantSpectrumB_at_one : circulantSpectrumB 1 = 6 := by
  unfold circulantSpectrumB
  norm_num

/-- The eigenvalue at `cos π = -1`, second circulant. -/
theorem circulantSpectrumB_at_neg_one : circulantSpectrumB (-1) = -2 := by
  unfold circulantSpectrumB
  norm_num

/-- The eigenvalue at `cos (π/2) = 0`, second circulant. -/
theorem circulantSpectrumB_at_zero : circulantSpectrumB 0 = -2 := by
  unfold circulantSpectrumB
  norm_num

/-- The eigenvalue at `cos (π/4) = s/2`, second circulant. -/
theorem circulantSpectrumB_at_root (s : ℝ) (hs : s ^ 2 = 2) :
    circulantSpectrumB (s / 2) = 2 * s := by
  unfold circulantSpectrumB
  linarith [hs]

/-- The eigenvalue at `cos (3π/4) = -s/2`, second circulant. -/
theorem circulantSpectrumB_at_neg_root (s : ℝ) (hs : s ^ 2 = 2) :
    circulantSpectrumB (-(s / 2)) = -(2 * s) := by
  unfold circulantSpectrumB
  linarith [hs]

/-- Power sum of the first circulant's eigenvalues, with their multiplicities:
the `p`-th cycle density of that overlap structure.

Empirical status: UNTESTED. A power sum of the eigenvalues of one fixed integer
matrix; no modelling content and no free parameter. -/
def palindromicCycleDensityA (s : ℝ) (p : ℕ) : ℝ :=
  circulantSpectrumA 1 ^ p + 2 * circulantSpectrumA (s / 2) ^ p +
    2 * circulantSpectrumA 0 ^ p + 2 * circulantSpectrumA (-(s / 2)) ^ p +
    circulantSpectrumA (-1) ^ p

/-- Power sum of the second circulant's eigenvalues, with their multiplicities.

Empirical status: UNTESTED. As for `palindromicCycleDensityA`: a power sum for
one fixed integer matrix, no free parameter. -/
def palindromicCycleDensityB (s : ℝ) (p : ℕ) : ℝ :=
  circulantSpectrumB 1 ^ p + 2 * circulantSpectrumB (s / 2) ^ p +
    2 * circulantSpectrumB 0 ^ p + 2 * circulantSpectrumB (-(s / 2)) ^ p +
    circulantSpectrumB (-1) ^ p

/-- Second cycle density of the first structure: `80`. -/
theorem palindromicCycleDensityA_two (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityA s 2 = 80 := by
  unfold palindromicCycleDensityA
  rw [circulantSpectrumA_at_one, circulantSpectrumA_at_neg_one,
    circulantSpectrumA_at_quarter_turn, circulantSpectrumA_at_root s hs,
    circulantSpectrumA_at_neg_root s hs]
  have hsq : (-s) ^ 2 = s ^ 2 := by ring
  rw [hsq, hs]
  norm_num

/-- Second cycle density of the second structure: also `80`. The agreement is
forced by the shared entry multiset, since the second density is the squared
Frobenius norm. -/
theorem palindromicCycleDensityB_two (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityB s 2 = 80 := by
  unfold palindromicCycleDensityB
  rw [circulantSpectrumB_at_one, circulantSpectrumB_at_neg_one,
    circulantSpectrumB_at_zero, circulantSpectrumB_at_root s hs,
    circulantSpectrumB_at_neg_root s hs]
  have hsq : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
  have hsqneg : (-(2 * s)) ^ 2 = 4 * s ^ 2 := by ring
  rw [hsq, hsqneg, hs]
  norm_num

/-- **The second cycle densities agree.** -/
theorem palindromic_second_cycle_densities_equal (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityA s 2 = palindromicCycleDensityB s 2 := by
  rw [palindromicCycleDensityA_two s hs, palindromicCycleDensityB_two s hs]

/-- Fourth cycle density of the first structure: `1840`. -/
theorem palindromicCycleDensityA_four (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityA s 4 = 1840 := by
  have hfour : s ^ 4 = 4 := by
    have hrewrite : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [hrewrite, hs]
    norm_num
  unfold palindromicCycleDensityA
  rw [circulantSpectrumA_at_one, circulantSpectrumA_at_neg_one,
    circulantSpectrumA_at_quarter_turn, circulantSpectrumA_at_root s hs,
    circulantSpectrumA_at_neg_root s hs]
  have hneg : (-s) ^ 4 = s ^ 4 := by ring
  rw [hneg, hfour]
  norm_num

/-- Fourth cycle density of the second structure: `1600`. -/
theorem palindromicCycleDensityB_four (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityB s 4 = 1600 := by
  have hfour : s ^ 4 = 4 := by
    have hrewrite : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [hrewrite, hs]
    norm_num
  unfold palindromicCycleDensityB
  rw [circulantSpectrumB_at_one, circulantSpectrumB_at_neg_one,
    circulantSpectrumB_at_zero, circulantSpectrumB_at_root s hs,
    circulantSpectrumB_at_neg_root s hs]
  have hpos : (2 * s) ^ 4 = 16 * s ^ 4 := by ring
  have hneg : (-(2 * s)) ^ 4 = 16 * s ^ 4 := by ring
  rw [hpos, hneg, hfour]
  norm_num

/-- **The fourth cycle densities differ.** `1840` against `1600`: the witness
pair is separated by the fourth spectral moment of the overlap structure, the
first cycle density their shared profile does not fix. -/
theorem palindromic_fourth_cycle_densities_differ (s : ℝ) (hs : s ^ 2 = 2) :
    palindromicCycleDensityA s 4 ≠ palindromicCycleDensityB s 4 := by
  rw [palindromicCycleDensityA_four s hs, palindromicCycleDensityB_four s hs]
  norm_num

/-- **Matching the recurrence profile leaves the fourth cycle density free.**

Two designs whose overlap structures are the two palindromic circulants have
equal second cycle densities and unequal fourth ones. The hypothesis
`hrecurrence` — that the two agree in the whole variant-recurrence profile — is
an argument of the theorem and is *never used in the proof*. That is the content:
recurrence is a star density, it is compatible with either value of the fourth
cycle density, and a scheme that preserves it has preserved nothing the limit law
depends on.

The prescription is `CycleDeterminacy.cycle_preserving_resampling_is_a_calibration`:
preserve the cycle densities, of which the fourth is the first that bites in the
quadratic sector. -/
theorem recurrence_matching_leaves_fourth_cycle_density_free
    (design resampled : GenotypeDesign nx ιx) (s : ℝ) (hs : s ^ 2 = 2)
    (_hrecurrence : ∀ i : Fin nx,
      resampled.variantRecurrence i = design.variantRecurrence i)
    (hdesign : design.cycleDensity 4 = palindromicCycleDensityA s 4)
    (hresampled : resampled.cycleDensity 4 = palindromicCycleDensityB s 4) :
    design.cycleDensity 4 ≠ resampled.cycleDensity 4 := by
  rw [hdesign, hresampled]
  exact palindromic_fourth_cycle_densities_differ s hs

end StarVersusCycle

end

end Calibrator

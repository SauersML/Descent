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

**Do overlapping interaction terms decouple?** Only when the coding is
sign-symmetric. The Sign-Erasure Lemma below is exact and finite: if the
coordinate law is invariant under a value-negating relabelling and the
truncation depends only on magnitudes, then every truncated cross-moment
between two distinct monomials vanishes identically, so overlapping designs
collapse onto their disjoint skeletons.

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
theorem below and into the `ChaosSpectroscopy` results of
`Calibrator.JetBarrier`, is:

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
condensation/drift arc: `Calibrator.Condensation`'s `MellinProfile` carries no
symmetry field, so the drift-separation and critical-degree results apply at
every allele frequency. What is symmetry-gated is the sign-erasure /
disjoint-skeleton reduction here, and the completeness statements built on it.
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
  refine le_trans (Finset.sum_le_sum (fun s _ => hstep s)) ?_
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
      (fun minimumOrder : ℕ =>
        tiltConstant / (threshold ^ 2 * Real.sqrt minimumOrder))
      Filter.atTop (nhds 0) := by
  have hpos : (0 : ℝ) < threshold ^ 2 := by positivity
  have hsqrt : Filter.Tendsto (fun m : ℕ => Real.sqrt m) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 (fun b => ⟨⌈b ^ 2⌉₊, fun m hm => ?_⟩)
    have hb : b ^ 2 ≤ (m : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hb
  have hscaled : Filter.Tendsto
      (fun m : ℕ => threshold ^ 2 * Real.sqrt m) Filter.atTop Filter.atTop :=
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
  · refine Finset.prod_congr rfl (fun j hj => ?_)
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
      (fun j => coding.weight (x j)),
    coding.weight_flip]

theorem interactionMonomial_flipLocus_mem (coding : SymmetricCoding V)
    {i : Fin n} {locusSet : Finset (Fin n)} (hi : i ∈ locusSet) (x : Fin n → V) :
    interactionMonomial coding locusSet (flipLocus coding i x) =
      -interactionMonomial coding locusSet x := by
  unfold interactionMonomial flipLocus
  simp only [Equiv.coe_fn_mk]
  rw [prod_update_split coding.value x i (coding.flip (x i)) locusSet hi,
    Finset.prod_eq_mul_prod_diff_singleton hi (fun j => coding.value (x j)),
    coding.value_flip]
  ring

theorem interactionMonomial_flipLocus_not_mem (coding : SymmetricCoding V)
    {i : Fin n} {locusSet : Finset (Fin n)} (hi : i ∉ locusSet) (x : Fin n → V) :
    interactionMonomial coding locusSet (flipLocus coding i x) =
      interactionMonomial coding locusSet x := by
  unfold interactionMonomial flipLocus
  simp only [Equiv.coe_fn_mk]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hne : j ≠ i := by rintro rfl; exact hi hj
  rw [Function.update_of_ne hne]

/-- **Sign-Erasure Lemma.** For a sign-symmetric coding and any truncation that
depends only on magnitudes, the truncated cross-moment of two interaction
monomials vanishes exactly whenever some locus lies in one and not the other.
No asymptotics, no tuning, no moment conditions: one relabelling of one locus
does it.

The consequence for epistasis is that overlapping interaction terms — sliding
windows along a chromosome, nested gene sets — have exactly the truncated
second-moment structure of disjoint ones, so their limit theory is the
independent one.

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
  set F : (Fin n → V) → ℝ := fun x =>
    configurationWeight coding x * interactionMonomial coding firstSet x *
      interactionMonomial coding secondSet x * truncation x with hF
  have hflip : ∀ x, F (flipLocus coding i x) = -F x := by
    intro x
    simp only [hF, configurationWeight_flipLocus,
      interactionMonomial_flipLocus_mem coding hfirst,
      interactionMonomial_flipLocus_not_mem coding hsecond, htruncation]
    ring
  have hsum : ∑ x, F x = ∑ x, F (flipLocus coding i x) :=
    (Fintype.sum_equiv (flipLocus coding i) (fun x => F (flipLocus coding i x)) F
      (fun _ => rfl)).symm
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
  value := fun v => a * coding.value v
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
      (fun v => coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3)
      (fun v => coding.weight v * coding.value v ^ 3) (fun _ => rfl)).symm
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

/-- Expand a sum over the three diploid genotypes. -/
private theorem sum_over_genotypes (f : DiploidGenotype → ℝ) :
    (∑ g : DiploidGenotype, f g) =
      f DiploidGenotype.homRef + f DiploidGenotype.het + f DiploidGenotype.homAlt := by
  have hrewrite :
      (∑ g : DiploidGenotype, f g) =
        ∑ i : Fin 3, f (DiploidGenotype.equivFin3.symm i) :=
    Fintype.sum_equiv DiploidGenotype.equivFin3 _ _ (by
      intro x
      rw [DiploidGenotype.equivFin3_symm_apply_apply])
  rw [hrewrite, Fin.sum_univ_three]
  rfl

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
def balancedGenotypeCoding (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2) :
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
for the `ChaosSpectroscopy` results of `Calibrator.JetBarrier`, whose `Law`
parameter ranges over symmetric laws: instantiating any of them at a genotype is
licensed at `q = 1/2` and at no other polymorphic frequency. -/
theorem hwe_symmetricCoding_iff_half
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.centeredAltAlleleCount g)) ↔ h.altFreq = 1 / 2 := by
  constructor
  · rintro ⟨coding, hweight, hvalue⟩
    exact hwe_symmetricCoding_forces_half h hq0 hq1 coding hweight hvalue
  · intro hhalf
    exact ⟨balancedGenotypeCoding h hhalf, fun _ => rfl, fun _ => rfl⟩

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
the abstract theory quantifies over — `ChaosSpectroscopy` ranges over *symmetric
unit-variance* laws — so this is the form in which the hypothesis is actually
discharged, or (at `q ≠ 1/2`) refuted. -/
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
      (coding.scale (Real.sqrt h.genotypeVariance)) (fun g => hweight g) ?_
    intro g
    show Real.sqrt h.genotypeVariance * coding.value g = h.centeredAltAlleleCount g
    rw [hvalue g]
    unfold HardyWeinbergModel.standardizedGenotype
    field_simp
  · intro hhalf
    refine ⟨(balancedGenotypeCoding h hhalf).scale (1 / Real.sqrt h.genotypeVariance),
      fun _ => rfl, ?_⟩
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

end

end Calibrator

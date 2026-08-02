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

Second order is as far as that goes, and the qualifier is load-bearing. An
earlier version of this docstring concluded from sign erasure that overlapping
designs "collapse onto their disjoint skeletons", so that their limit theory is
the independent one. That conclusion is false, and §`OverlapSpectrum` below
refutes it inside the symmetric class: the two-pool interaction statistic
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
    exact ⟨equalFrequencyGenotypeCoding h hhalf, fun _ => rfl, fun _ => rfl⟩

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
    refine ⟨(equalFrequencyGenotypeCoding h hhalf).scale (1 / Real.sqrt h.genotypeVariance),
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

section OverlapSpectrum

/-!
## Disjoint locus-sets versus overlapping ones: a licence and a prohibition

Everything above concerns one interaction term at a time (no jumps) or two terms
at a time (sign erasure). Neither settles the question a practitioner faces,
which is about a whole *design* at once: given the collection of locus-sets a
set-based or interaction study tests over a panel of Hardy-Weinberg loci, what
null distributions can the test statistic have?

Two results answer it, and they answer in opposite directions according to a
single structural property — whether the tested locus-sets share variants. Both
are carried as fields of `GenotypeChaosLimits`, in the convention of
`Calibrator.Identification`: the analytic input is visible at the type level, and
the consequences below are proved from it. Everything is stated over
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

Theorem S is strictly stronger than the folklore it replaces. The previously
recorded effect of overlap was a variance-mixture component in the limit; a
variance mixture of centered Gaussians is symmetric, unimodal, and has
non-negative fourth cumulant. The moment body contains laws that are none of
those.

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
   hypothesis `GenotypeDesign.LociIndependent`, an argument of the licence,
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

/-! ### The design: locus-sets over a Hardy-Weinberg panel -/

/-- A **design over a genotype panel**: the locus-sets a study tests, the
coefficient each contributes, the allele frequency of every locus, and the
population's joint genotype law over the panel.

The joint law is carried alongside the per-locus models so that linkage
equilibrium is a checkable relation between them
(`GenotypeDesign.LociIndependent`) rather than a silent assumption; the
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

/-- **The panel loci are independent**: the joint genotype law factorizes into
the per-locus Hardy-Weinberg laws. This is linkage equilibrium across the tested
panel, stated as the factorization it is; the dynamics that drive a population
towards it live in `Calibrator.LDDecayTheory`.

It is an assumption about the population, not about the coding, and it is what
the disjoint licence needs in place of symmetry. A design whose tested sets sit
inside one LD block does not have it.

Empirical status: UNTESTED. A factorization condition on the joint law; testable
directly as pairwise LD between panel loci. -/
def LociIndependent : Prop :=
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
  (Finset.univ.filter (fun s => i ∈ design.locusSet s)).card

/-- **The influence of a variant**: the share of the statistic's energy carried
by locus `i`, namely the total squared coefficient of the tested sets containing
it. Admissibility asks that this vanish uniformly in `i`.

Empirical status: UNTESTED. An energy share read off the design's coefficients;
no free parameter and nothing fitted. -/
def locusInfluence (i : Fin n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => i ∈ design.locusSet s), design.coefficient s ^ 2

theorem locusInfluence_nonneg (i : Fin n) : 0 ≤ design.locusInfluence i :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

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
      (Finset.univ.filter (fun s => i ∈ design.locusSet s)).card := rfl
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
  have hfilter : Finset.univ.filter (fun t => i ∈ design.locusSet t) = {s} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hi⟩
    · intro t ht
      exact unique_set_of_variantDisjoint hdisjoint (Finset.mem_filter.mp ht).2 hi
  have hdef : design.locusInfluence i =
      ∑ t ∈ Finset.univ.filter (fun t => i ∈ design.locusSet t),
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
  locusSet := fun g => Finset.univ.filter (fun i => geneOf i = g)
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
  have hig : i ∈ Finset.univ.filter (fun j => geneOf j = g) := hi
  have hig' : i ∈ Finset.univ.filter (fun j => geneOf j = g') := hi'
  exact hne (((Finset.mem_filter.mp hig).2).symm.trans (Finset.mem_filter.mp hig').2)

/-- **A sliding-window design**: the tested set at start `k` is the block of
`width` consecutive panel positions beginning at `k`.

Empirical status: UNTESTED. A study design, not a claim about data; it is the
formal shape of a sliding-window interaction or kernel scan. -/
def slidingWindowDesign (model : Fin n → HardyWeinbergModel) (width : ℕ)
    (coeff : Fin n → ℝ) (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ) :
    GenotypeDesign n (Fin n) where
  model := model
  locusSet := fun k =>
    Finset.univ.filter (fun i : Fin n => (k : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k : ℕ) + width)
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
          (fun i : Fin n => (k : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k : ℕ) + width) := rfl
    rw [hset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by omega, by omega⟩
  have hmem' : j ∈ (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k' := by
    have hset : (slidingWindowDesign model width coeff jointGenotypeProb).locusSet k' =
        Finset.univ.filter
          (fun i : Fin n => (k' : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (k' : ℕ) + width) := rfl
    rw [hset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by omega, by omega⟩
  exact GenotypeDesign.not_variantDisjoint_of_recurrent hne hmem hmem'

/-! ### The limit spectrum over a genotype panel -/

/-- The limit spectrum of admissible chaos designs over a Hardy-Weinberg panel,
packaged so that the analytic inputs are fields.

Only `Limit` is abstract, because weak limits of laws are not objects of this
corpus; the designs, the coordinates and the allele frequencies are the corpus's
own. `weakDistance` metrizes weak convergence, the topology the spectrum is
closed in, and `InMomentBody L` says `L` is centered with second moment at most
one.

No symmetry hypothesis appears anywhere, and none is needed: see the discussion
at the head of this section. -/
structure GenotypeChaosLimits (n : ℕ) (ι : Type*) (Limit : Type*) where
  /-- Minimum interaction order diverging, `locusInfluence` vanishing, unit variance. -/
  isAdmissible : GenotypeDesign n ι → Prop
  /-- The limit law of the design's statistic. -/
  limitLaw : GenotypeDesign n ι → Limit
  /-- `IsCenteredGaussian L s2` says `L` is `N(0, s2)`. -/
  IsCenteredGaussian : Limit → ℝ → Prop
  /-- The fourth cumulant of a limit law. -/
  fourthCumulant : Limit → ℝ
  /-- A metric for weak convergence. -/
  weakDistance : Limit → Limit → ℝ
  /-- Centered, with second moment at most one. -/
  InMomentBody : Limit → Prop
  /-- **Theorem D (analytic input).** A pairwise-disjoint admissible design over
  polymorphic loci in linkage equilibrium has a centered Gaussian limit with
  variance in `[0, 1]`. The route is infinite divisibility with vanishing Lévy
  measure, the vanishing supplied by `no_macroscopic_interaction_term`; the
  coordinate inputs are `standardizedGenotype_expectation_zero` and
  `standardizedGenotype_second_moment_one`, both frequency-free, so this field
  carries no symmetry hypothesis and is licensed at every polymorphic
  frequency. -/
  disjoint_segment : ∀ design : GenotypeDesign n ι, isAdmissible design →
    design.Polymorphic → design.LociIndependent → design.VariantDisjoint →
    ∃ s2 : ℝ, 0 ≤ s2 ∧ s2 ≤ 1 ∧ IsCenteredGaussian (limitLaw design) s2
  /-- The Gaussian moment identity `E[g⁴] = 3 (E[g²])²`, in cumulant form. -/
  gaussian_fourthCumulant : ∀ (L : Limit) (s2 : ℝ), IsCenteredGaussian L s2 →
    fourthCumulant L = 0
  /-- **Theorem S (analytic input).** At a *prescribed* polymorphic
  allele-frequency family, and still under linkage equilibrium, admissible
  designs on that panel realize every centered law with second moment at most one
  to arbitrary weak accuracy. The frequencies are fixed before the design is
  chosen, so this is not achieved by tuning the genotype distribution; and the
  designs produced are necessarily non-disjoint whenever the target is not
  Gaussian, since `disjoint_segment` forbids anything else. -/
  maximal_spectrum : ∀ model : Fin n → HardyWeinbergModel,
    (∀ i : Fin n, 0 < (model i).altFreq ∧ (model i).altFreq < 1) →
    ∀ target : Limit, InMomentBody target → ∀ ε : ℝ, 0 < ε →
      ∃ design : GenotypeDesign n ι, design.model = model ∧
        design.LociIndependent ∧ isAdmissible design ∧
        weakDistance (limitLaw design) target < ε
  /-- **The non-soficity witness (analytic input).** The two-pool interaction
  statistic has limiting fourth cumulant `6`, at every polymorphic
  allele-frequency family: each pool sum is asymptotically standard by the
  ordinary central limit theorem, which holds at every frequency, and the pools
  are independent under linkage equilibrium, so the limit is a product of two
  independent standard Gaussians. The arithmetic `9 - 3 = 6` is proved in
  `twoPool_interaction_fourthCumulant`. -/
  twoPool_witness : ∀ (design : GenotypeDesign n ι) (poolOne poolTwo : Finset (Fin n)),
    design.IsTwoPoolInteraction poolOne poolTwo → design.Polymorphic →
    design.LociIndependent → fourthCumulant (limitLaw design) = 6

namespace GenotypeChaosLimits

variable {Limit : Type*} (Sp : GenotypeChaosLimits n ι Limit)

/-- **The licence, with every hypothesis in the type.** A Gaussian null is
justified for an admissible design over polymorphic loci in linkage equilibrium
*provided the tested locus-sets are pairwise disjoint*, and then the variance is
the only free parameter.

`hdisjoint` is an argument precisely because dropping it is not a loss of
sharpness but a total loss of the conclusion
(`admissibility_alone_certifies_only_the_moment_body`). -/
theorem gaussian_null_licensed_of_disjoint (design : GenotypeDesign n ι)
    (hadmissible : Sp.isAdmissible design) (hpolymorphic : design.Polymorphic)
    (hequilibrium : design.LociIndependent)
    (hdisjoint : design.VariantDisjoint) :
    ∃ s2 : ℝ, 0 ≤ s2 ∧ s2 ≤ 1 ∧ Sp.IsCenteredGaussian (Sp.limitLaw design) s2 :=
  Sp.disjoint_segment design hadmissible hpolymorphic hequilibrium hdisjoint

/-- **The licence applies to gene-based burden and kernel tests.** With one gene
per variant, disjointness is discharged, so an admissible burden design over
polymorphic loci in linkage equilibrium has a Gaussian null whatever the allele
frequencies are.

This is one half of the practical dichotomy, and it is derived rather than
asserted. -/
theorem geneBurden_gaussian_null {γ : Type*} [DecidableEq γ]
    (Sp' : GenotypeChaosLimits n γ Limit)
    (model : Fin n → HardyWeinbergModel) (geneOf : Fin n → γ) (coeff : γ → ℝ)
    (jointGenotypeProb : (Fin n → DiploidGenotype) → ℝ)
    (hadmissible : Sp'.isAdmissible (geneBurdenDesign model geneOf coeff jointGenotypeProb))
    (hpolymorphic : (geneBurdenDesign model geneOf coeff jointGenotypeProb).Polymorphic)
    (hequilibrium :
      (geneBurdenDesign model geneOf coeff jointGenotypeProb).LociIndependent) :
    ∃ s2 : ℝ, 0 ≤ s2 ∧ s2 ≤ 1 ∧
      Sp'.IsCenteredGaussian
        (Sp'.limitLaw (geneBurdenDesign model geneOf coeff jointGenotypeProb)) s2 :=
  Sp'.disjoint_segment _ hadmissible hpolymorphic hequilibrium
    (geneBurdenDesign_variantDisjoint model geneOf coeff jointGenotypeProb)

/-- Every disjoint design's limit has vanishing fourth cumulant: the order-four
shadow of the licence, and the quantity the two-pool witness violates. -/
theorem disjoint_limit_fourthCumulant_zero (design : GenotypeDesign n ι)
    (hadmissible : Sp.isAdmissible design) (hpolymorphic : design.Polymorphic)
    (hequilibrium : design.LociIndependent)
    (hdisjoint : design.VariantDisjoint) :
    Sp.fourthCumulant (Sp.limitLaw design) = 0 := by
  obtain ⟨s2, _, _, hgauss⟩ :=
    Sp.disjoint_segment design hadmissible hpolymorphic hequilibrium hdisjoint
  exact Sp.gaussian_fourthCumulant _ s2 hgauss

/-- **The prohibition, in the form a calibration argument meets it.** Suppose a
criterion `accept` is sound for admissible designs on a given polymorphic panel —
it accepts the null of every admissible design there, which is what "our
statistic satisfies the standard regularity conditions" asserts. Then `accept`
holds arbitrarily weakly-close to *every* centered law with second moment at most
one.

So admissibility alone certifies nothing beyond centering and the variance bound,
at any allele-frequency spectrum. It does not certify Gaussianity, and a
calibration justified only by high interaction order and low per-variant
influence is unjustified as soon as the tested sets share variants. -/
theorem admissibility_alone_certifies_only_the_moment_body
    (model : Fin n → HardyWeinbergModel)
    (hpolymorphic : ∀ i : Fin n, 0 < (model i).altFreq ∧ (model i).altFreq < 1)
    (accept : Limit → Prop)
    (hsound : ∀ design : GenotypeDesign n ι, design.model = model →
      Sp.isAdmissible design → accept (Sp.limitLaw design))
    (target : Limit) (htarget : Sp.InMomentBody target)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : Limit, accept L ∧ Sp.weakDistance L target < ε := by
  obtain ⟨design, hmodel, _, hadmissible, hclose⟩ :=
    Sp.maximal_spectrum model hpolymorphic target htarget ε hε
  exact ⟨Sp.limitLaw design, hsound design hmodel hadmissible, hclose⟩

end GenotypeChaosLimits

/-!
### The non-soficity witness, in its genetic reading

Split the panel into two pools of loci with no variant in common, let `T₁` and
`T₂` be the standardized sums over each pool, and test the two-way interaction
statistic `f = T₁ * T₂` — the plainest thing written down when asking whether two
gene sets interact. Its tested sets are the cross-pool pairs `{i, j}`, so it is an
interaction design of order two with equal coefficients, and no single locus
carries a non-vanishing influence once both pools are large.

Each pool sum is asymptotically standard Gaussian by the ordinary central limit
theorem, which holds at *every* allele frequency, and the two are independent
under linkage equilibrium because the pools share no variant. So the limit is a
product of two independent standard Gaussians, with fourth cumulant
`E[(Z₁Z₂)⁴] - 3 (E[(Z₁Z₂)²])² = 9 - 3 = 6`.

No disjoint design matches that at order four, under any allele-frequency family.
The statistic is not asymptotically Gaussian at any allele frequency, and unlike
almost everything else here the claim needs no assumption about the genotype
distribution beyond polymorphism and linkage equilibrium.
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
  refine GenotypeDesign.not_variantDisjoint_of_recurrent hst ?_ ?_
  · rw [hs]; simp
  · rw [ht]; simp

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

/-- **The witness computation.** If each pool sum converges to a standard law —
second moment `1`, fourth moment `3`, which is the ordinary central limit theorem
for that pool and holds at every allele frequency — then the product statistic has
second moment `1 * 1` and fourth moment `3 * 3` by independence of the pools under
linkage equilibrium, hence fourth cumulant `6`.

Neither hypothesis mentions the allele frequencies, which is the uniformity
claim: the value `6` does not depend on the frequency spectrum, on which pool is
rarer, or on symmetry of the coding. -/
theorem twoPool_interaction_fourthCumulant
    (poolSecondMoment poolFourthMoment : ℝ)
    (hsecond : poolSecondMoment = 1) (hfourth : poolFourthMoment = 3) :
    fourthCumulantFromMoments (poolSecondMoment * poolSecondMoment)
      (poolFourthMoment * poolFourthMoment) = 6 := by
  subst hsecond
  subst hfourth
  unfold fourthCumulantFromMoments
  norm_num

/-- Six is not zero. Recorded separately because it is the whole separation. -/
theorem twoPool_fourthCumulant_ne_disjoint : (6 : ℝ) ≠ 0 := by norm_num

/-- **No disjoint design over the same panel reproduces the two-pool interaction
statistic**, even at order four, and at every polymorphic allele-frequency family.

The conclusion holds for every admissible disjoint design in linkage equilibrium,
so the failure is not a matter of choosing the disjoint comparator badly; and the
witness hypothesis constrains only the design's locus-sets, never its allele
frequencies, so the separation is uniform over the genotype distribution. -/
theorem twoPool_witness_not_a_disjoint_limit {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit)
    (witness : GenotypeDesign n ι) (poolOne poolTwo : Finset (Fin n))
    (hwitness : witness.IsTwoPoolInteraction poolOne poolTwo)
    (hwitnessPoly : witness.Polymorphic) (hwitnessLE : witness.LociIndependent)
    (design : GenotypeDesign n ι) (hadmissible : Sp.isAdmissible design)
    (hpolymorphic : design.Polymorphic) (hequilibrium : design.LociIndependent)
    (hdisjoint : design.VariantDisjoint) :
    Sp.limitLaw design ≠ Sp.limitLaw witness := by
  intro heq
  have hzero := Sp.disjoint_limit_fourthCumulant_zero design hadmissible hpolymorphic
    hequilibrium hdisjoint
  have hsix := Sp.twoPool_witness witness poolOne poolTwo hwitness hwitnessPoly hwitnessLE
  rw [heq, hsix] at hzero
  exact twoPool_fourthCumulant_ne_disjoint hzero

/-- **Sign symmetry does not license the disjoint reduction.**

`sign_erasure` shows that under a sign-symmetric coding every truncated
cross-moment between two distinct interaction monomials vanishes. It is tempting
to read that as "overlapping designs behave like disjoint ones". The reading is
false, and the two-pool witness is a counterexample *inside* the symmetric class:
its overlapping tested sets `{i, j}` and `{i, k}` have vanishing cross-moments
under any symmetric law — the odd factors kill them — while the limit still has
fourth cumulant `6`.

The hypothesis `hbalanced` puts every panel locus at frequency one half, which by
`standardizedGenotype_symmetric_iff` is exactly where the genotype coding is
sign-symmetric, and it is never used in the proof. That is the point: the one
frequency where symmetry is available is a frequency where the reduction still
fails, so disjointness cannot be traded for symmetry. -/
theorem sign_symmetry_does_not_license_disjoint_reduction {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit)
    (witness : GenotypeDesign n ι) (poolOne poolTwo : Finset (Fin n))
    (hwitness : witness.IsTwoPoolInteraction poolOne poolTwo)
    (hwitnessPoly : witness.Polymorphic) (hwitnessLE : witness.LociIndependent)
    (_hbalanced : ∀ i : Fin n, (witness.model i).altFreq = 1 / 2)
    (design : GenotypeDesign n ι) (hadmissible : Sp.isAdmissible design)
    (hpolymorphic : design.Polymorphic) (hequilibrium : design.LociIndependent)
    (hdisjoint : design.VariantDisjoint) :
    Sp.limitLaw design ≠ Sp.limitLaw witness :=
  twoPool_witness_not_a_disjoint_limit Sp witness poolOne poolTwo hwitness hwitnessPoly
    hwitnessLE design hadmissible hpolymorphic hequilibrium hdisjoint

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
  refine ⟨0, fun c' hcontra => ?_⟩
  rw [circulantSpectrumA_at_quarter_turn] at hcontra
  exact circulantSpectrumB_ne_neg_four c' hcontra.symm

end OverlapSpectrum

end

end Calibrator

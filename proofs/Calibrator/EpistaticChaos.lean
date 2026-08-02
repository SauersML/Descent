import Calibrator.Probability
import Calibrator.PolygenicSpectroscopy
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
theorem no_macroscopic_interaction_limit (tiltConstant threshold : ℝ) :
    Filter.Tendsto
      (fun minimumOrder : ℕ =>
        tiltConstant / (threshold ^ 2 * Real.sqrt minimumOrder))
      Filter.atTop (nhds 0) := by
  have hsqrt : Filter.Tendsto (fun m : ℕ => Real.sqrt m) Filter.atTop Filter.atTop :=
    Real.sqrt_atTop.comp tendsto_natCast_atTop_atTop
  by_cases hthreshold : threshold ^ 2 = 0
  · simp [hthreshold]
  · have hscaled : Filter.Tendsto
        (fun m : ℕ => threshold ^ 2 * Real.sqrt m) Filter.atTop Filter.atTop := by
      rcases lt_or_gt_of_ne hthreshold with hneg | hpos
      · exact absurd (sq_nonneg threshold) (not_le.mpr hneg)
      · exact Filter.Tendsto.const_mul_atTop hpos hsqrt
    exact hscaled.inv_tendsto_atTop.const_mul_nhds_zero _

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

theorem configurationWeight_flipLocus (coding : SymmetricCoding V) (i : Fin n)
    (x : Fin n → V) :
    configurationWeight coding (flipLocus coding i x) = configurationWeight coding x := by
  unfold configurationWeight flipLocus
  simp only [Equiv.coe_fn_mk]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [coding.weight_flip]

theorem interactionMonomial_flipLocus_mem (coding : SymmetricCoding V)
    {i : Fin n} {locusSet : Finset (Fin n)} (hi : i ∈ locusSet) (x : Fin n → V) :
    interactionMonomial coding locusSet (flipLocus coding i x) =
      -interactionMonomial coding locusSet x := by
  unfold interactionMonomial flipLocus
  simp only [Equiv.coe_fn_mk]
  rw [Finset.prod_update_of_mem hi, Finset.prod_update_of_mem hi, coding.value_flip]
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
independent one. -/
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
    rw [hsum]
    simp_rw [hflip]
    rw [Finset.sum_neg_distrib]
    congr 1
    exact hsum.symm
  linarith [hneg]

/-- A sign-symmetric coding has no odd moments. This is the finite-sample
handle used below to decide which genotype codings are symmetric. -/
theorem symmetricCoding_third_moment_zero (coding : SymmetricCoding V) :
    ∑ v, coding.weight v * coding.value v ^ 3 = 0 := by
  have hswap : ∑ v, coding.weight v * coding.value v ^ 3 =
      ∑ v, coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3 :=
    (Fintype.sum_equiv coding.flip
      (fun v => coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3)
      (fun v => coding.weight v * coding.value v ^ 3) (fun _ => rfl)).symm
  have hneg : ∑ v, coding.weight v * coding.value v ^ 3 =
      -∑ v, coding.weight v * coding.value v ^ 3 := by
    rw [hswap]
    have hterm : ∀ v : V,
        coding.weight (coding.flip v) * coding.value (coding.flip v) ^ 3 =
          -(coding.weight v * coding.value v ^ 3) := by
      intro v
      rw [coding.weight_flip, coding.value_flip]
      ring
    simp_rw [hterm]
    rw [Finset.sum_neg_distrib]
  linarith [hneg]

end SignErasure

section GenotypeCoding

/-!
## Where diploid dosage sits

Two obstructions, at complementary frequencies, and together they exclude
hard-called dosage from the sign-symmetric class at every allele frequency.
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
  rw [sum_diploidGenotype]
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

/-- **At frequency one half the squared coding takes only two values.** The
standardized square of `Calibrator.PolygenicSpectroscopy` is `2` on both
homozygotes and `0` on the heterozygote, so `log x²` is supported on a single
point and lies inside every lattice. The one frequency at which dosage coding
is sign-symmetric is therefore the frequency at which it is maximally lattice:
hard-called diploid dosage is outside the nonlattice class at every allele
frequency. -/
theorem standardizedSquare_two_valued_at_half
    (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2) :
    h.standardizedSquare DiploidGenotype.homRef = 2 ∧
      h.standardizedSquare DiploidGenotype.het = 0 ∧
      h.standardizedSquare DiploidGenotype.homAlt = 2 := by
  have hq0 : 0 < h.altFreq := by rw [hhalf]; norm_num
  have hq1 : h.altFreq < 1 := by rw [hhalf]; norm_num
  obtain ⟨hhomRef, hhet, hhomAlt⟩ := standardizedSquare_values h hq0 hq1
  refine ⟨?_, ?_, ?_⟩
  · rw [hhomRef, hhalf]; norm_num
  · rw [hhet, hhalf]; norm_num
  · rw [hhomAlt, hhalf]; norm_num

/-- **The dichotomy for hard-called genotypes.** At a polymorphic locus, either
the frequency is one half — and then the coding is sign-symmetric but its
squared values collapse to two points — or it is not, and then the third
central moment is nonzero and no value-negating relabelling exists. There is no
allele frequency at which a hard-called diploid locus is both sign-symmetric
and spread out in `log x²`. -/
theorem hardCall_coding_dichotomy
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (h.altFreq = 1 / 2 ∧
        h.standardizedSquare DiploidGenotype.homRef = 2 ∧
        h.standardizedSquare DiploidGenotype.het = 0 ∧
        h.standardizedSquare DiploidGenotype.homAlt = 2) ∨
      hweThirdCentralMoment h ≠ 0 := by
  by_cases hhalf : h.altFreq = 1 / 2
  · exact Or.inl ⟨hhalf, standardizedSquare_two_valued_at_half h hhalf⟩
  · refine Or.inr ?_
    rw [hweThirdCentralMoment_eq]
    have hq : h.altFreq * (1 - h.altFreq) > 0 := by
      apply mul_pos hq0; linarith
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

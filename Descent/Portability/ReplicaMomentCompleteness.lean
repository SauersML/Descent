/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin

assert_below Descent.Decision Descent.Program

/-!
# The replica family of a random probability vector determines its mixing law

This is the completeness half of NOTE2 Theorem 3. A random probability vector on an alphabet
of size `m` is a finite Borel measure on the compact simplex `stdSimplex ℝ (Fin m)`, and the
replica law of NOTE2 (11) sends a listing `z` of cohort slots to the probability
`∫ ∏ᵢ q (z i) dμ` that conditionally independent draws read out those letters. The theorem
proved here is `measure_eq_of_replicaLaw_eq`: two finite mixing laws with the same replica
laws at every cohort size are equal as measures.

The route is the one the note names. `exponentListing` turns an exponent vector `e` into a
cohort of `∑ e` slots that draws letter `a` exactly `e a` times, and
`replicaLaw_exponentListing` shows the corresponding replica probability *is* the monomial
moment `∫ ∏ᵢ qᵢ^{eᵢ} dμ`, so replica data and monomial-moment data are the same data. The
monomials span a subalgebra `replicaAlgebra` of `C(simplex, ℝ)`; it separates points because
the coordinate readouts are themselves monomials, so by Stone–Weierstrass
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`) it is uniformly
dense. Agreeing integrals pass to uniform limits because a finite measure turns a sup-norm
bound into an integral bound, and equal integrals of all bounded continuous functions force
equal measures by `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`.

Scope. The measures here are arbitrary finite Borel measures on the simplex, not only
finitely supported ones, so this is the general completeness statement. What is *not* proved
here is the necessity half at a fixed order, which lives in `ReplicaFiniteOrderNecessity`. The
joint source/target construction of NOTE2 §4 is represented by `taggedPair`, the embedding of
a pair of probability vectors on two alphabets into a single probability vector on their
disjoint union; it is proved to land in the simplex, to be injective and to be continuous,
which is what makes completeness for the pair a corollary of completeness for one alphabet.
The tagged mixture measure itself is not formed.

`simplexPoint` connects the construction to the corpus: a `FiniteReportLaw (Fin m)` is
exactly a point of this simplex, and the monomial readout at that point is the product of its
masses.

## Empirical status

None. The bodies here are algebra and measure theory: `replicaLaw` is a stipulated integral
of a stipulated product, and no statement below asserts that any measured quantity equals it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReplicaMomentCompleteness

open MeasureTheory

noncomputable section

/-! ### Monomial readouts of a probability vector -/

/-- The coordinate readout of a probability vector, as a continuous function on the simplex. -/
def coordinate (m : ℕ) (i : Fin m) : C(↥(stdSimplex ℝ (Fin m)), ℝ) where
  toFun q := (q : Fin m → ℝ) i
  continuous_toFun := (continuous_apply i).comp continuous_subtype_val

/-- The monomial readout `q ↦ ∏ᵢ qᵢ^{eᵢ}` of a probability vector. -/
def monomialMap (m : ℕ) (e : Fin m → ℕ) : C(↥(stdSimplex ℝ (Fin m)), ℝ) :=
  ∏ i, coordinate m i ^ e i

/-- The monomial readout evaluates to the corresponding product of coordinates. -/
theorem monomialMap_apply (m : ℕ) (e : Fin m → ℕ) (q : ↥(stdSimplex ℝ (Fin m))) :
    monomialMap m e q = ∏ i, (q : Fin m → ℝ) i ^ e i := by
  simp only [monomialMap, ContinuousMap.prod_apply, ContinuousMap.pow_apply]
  rfl

/-- The empty exponent vector gives the constant readout one. -/
theorem monomialMap_zero (m : ℕ) : monomialMap m 0 = 1 := by
  simp [monomialMap]

/-- Monomial readouts multiply by adding exponents. -/
theorem monomialMap_add (m : ℕ) (d e : Fin m → ℕ) :
    monomialMap m (d + e) = monomialMap m d * monomialMap m e := by
  simp only [monomialMap, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.add_apply, pow_add]

/-- The coordinate readout is the monomial readout of a one-hot exponent vector. -/
theorem monomialMap_indicator (m : ℕ) (i : Fin m) (q : ↥(stdSimplex ℝ (Fin m))) :
    monomialMap m (fun k ↦ if k = i then 1 else 0) q = (q : Fin m → ℝ) i := by
  rw [monomialMap_apply, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The monomial readouts form a multiplicative monoid. -/
def monomialMonoid (m : ℕ) : Submonoid C(↥(stdSimplex ℝ (Fin m)), ℝ) where
  carrier := Set.range (monomialMap m)
  mul_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨d + e, monomialMap_add m d e⟩
  one_mem' := ⟨0, monomialMap_zero m⟩

/-- The algebra of polynomial readouts of a probability vector. -/
def replicaAlgebra (m : ℕ) : Subalgebra ℝ C(↥(stdSimplex ℝ (Fin m)), ℝ) :=
  Algebra.adjoin ℝ (Set.range (monomialMap m))

/-- Every monomial readout belongs to the algebra it generates. -/
theorem monomialMap_mem (m : ℕ) (e : Fin m → ℕ) : monomialMap m e ∈ replicaAlgebra m :=
  Algebra.subset_adjoin ⟨e, rfl⟩

/-- Because monomials are closed under multiplication, the algebra they generate is already
their linear span. -/
theorem replicaAlgebra_toSubmodule (m : ℕ) :
    Subalgebra.toSubmodule (replicaAlgebra m) =
      Submodule.span ℝ (Set.range (monomialMap m)) := by
  refine Algebra.adjoin_eq_span_of_subset ℝ ?_
  intro f hf
  have hsub : Submonoid.closure (Set.range (monomialMap m)) ≤ monomialMonoid m :=
    Submonoid.closure_le.mpr fun g hg ↦ hg
  exact Submodule.subset_span (hsub hf)

/-- The polynomial readouts separate probability vectors, because two distinct probability
vectors differ in some coordinate and the coordinate readouts are monomials. -/
theorem replicaAlgebra_separatesPoints (m : ℕ) : (replicaAlgebra m).SeparatesPoints := by
  intro x y hxy
  have hex : ∃ i, (x : Fin m → ℝ) i ≠ (y : Fin m → ℝ) i := by
    by_contra hc
    push_neg at hc
    exact hxy (Subtype.ext (funext hc))
  obtain ⟨i, hi⟩ := hex
  refine ⟨_, ⟨monomialMap m (fun k ↦ if k = i then 1 else 0), monomialMap_mem m _, rfl⟩, ?_⟩
  simpa only [monomialMap_indicator] using hi

/-! ### Passing from monomial moments to the whole measure -/

/-- A continuous readout of a probability vector is integrable against any finite mixing
law, because the simplex is compact. -/
theorem integrable_readout (m : ℕ) (μ : Measure ↥(stdSimplex ℝ (Fin m)))
    [IsFiniteMeasure μ] (f : C(↥(stdSimplex ℝ (Fin m)), ℝ)) :
    Integrable (fun q ↦ f q) μ :=
  BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.mkOfCompact f)

/-- A sup-norm bound on the difference of two continuous readouts bounds the difference of
their expectations, with the total mass as the constant. -/
theorem abs_integral_readout_sub_le (m : ℕ) (μ : Measure ↥(stdSimplex ℝ (Fin m)))
    [IsFiniteMeasure μ] (f g : C(↥(stdSimplex ℝ (Fin m)), ℝ)) :
    |∫ q, f q ∂μ - ∫ q, g q ∂μ| ≤ μ.real Set.univ * ‖f - g‖ := by
  have hsub : ∫ q, f q ∂μ - ∫ q, g q ∂μ = ∫ q, (f - g) q ∂μ := by
    rw [← integral_sub (integrable_readout m μ f) (integrable_readout m μ g)]
    rfl
  have hbdd := BoundedContinuousFunction.norm_integral_le_mul_norm μ
    (BoundedContinuousFunction.mkOfCompact (f - g))
  rw [BoundedContinuousFunction.norm_mkOfCompact] at hbdd
  rw [hsub, ← Real.norm_eq_abs]
  exact hbdd

/-- Equal monomial moments force equal expectations of every polynomial readout. -/
theorem integral_eq_of_monomial_moments_eq (m : ℕ)
    (μ ν : Measure ↥(stdSimplex ℝ (Fin m))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmoment : ∀ e : Fin m → ℕ,
      ∫ q, monomialMap m e q ∂μ = ∫ q, monomialMap m e q ∂ν)
    (f : C(↥(stdSimplex ℝ (Fin m)), ℝ)) (hf : f ∈ replicaAlgebra m) :
    ∫ q, f q ∂μ = ∫ q, f q ∂ν := by
  have hspan : f ∈ Submodule.span ℝ (Set.range (monomialMap m)) := by
    rw [← replicaAlgebra_toSubmodule m]
    exact hf
  refine Submodule.span_induction
    (p := fun g _ ↦ ∫ q, g q ∂μ = ∫ q, g q ∂ν) ?_ ?_ ?_ ?_ hspan
  · rintro g ⟨e, rfl⟩
    exact hmoment e
  · simp
  · intro g h _ _ ihg ihh
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_readout m μ g) (integrable_readout m μ h),
      integral_add (integrable_readout m ν g) (integrable_readout m ν h), ihg, ihh]
  · intro c g _ ih
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, ih]

/-- **NOTE2 Theorem 3, monomial form.** Two finite mixing laws on the simplex with the same
monomial moments of every order are equal. -/
theorem measure_eq_of_monomial_moments_eq (m : ℕ)
    (μ ν : Measure ↥(stdSimplex ℝ (Fin m))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmoment : ∀ e : Fin m → ℕ,
      ∫ q, monomialMap m e q ∂μ = ∫ q, monomialMap m e q ∂ν) :
    μ = ν := by
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun bounded ↦ ?_
  set g : C(↥(stdSimplex ℝ (Fin m)), ℝ) := bounded.toContinuousMap with hgdef
  have hC : 0 < μ.real Set.univ + ν.real Set.univ + 1 := by
    have h1 : (0 : ℝ) ≤ μ.real Set.univ := measureReal_nonneg
    have h2 : (0 : ℝ) ≤ ν.real Set.univ := measureReal_nonneg
    linarith
  have hzero : |∫ q, g q ∂μ - ∫ q, g q ∂ν| = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨near, hnear⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
        (replicaAlgebra m) (replicaAlgebra_separatesPoints m) g
        (ε / (μ.real Set.univ + ν.real Set.univ + 1)) (div_pos hε hC)
    set nc : C(↥(stdSimplex ℝ (Fin m)), ℝ) := (near : C(↥(stdSimplex ℝ (Fin m)), ℝ)) with hnc
    have hmid : ∫ q, nc q ∂μ = ∫ q, nc q ∂ν :=
      integral_eq_of_monomial_moments_eq m μ ν hmoment _ near.2
    have h1 := abs_integral_readout_sub_le m μ nc g
    have h2 := abs_integral_readout_sub_le m ν nc g
    have hμ : (0 : ℝ) ≤ μ.real Set.univ := measureReal_nonneg
    have hν : (0 : ℝ) ≤ ν.real Set.univ := measureReal_nonneg
    have hA : |∫ q, g q ∂μ - ∫ q, nc q ∂μ| ≤ μ.real Set.univ * ‖nc - g‖ := by
      rw [abs_sub_comm]
      exact h1
    have hstep : |∫ q, g q ∂μ - ∫ q, g q ∂ν| ≤
        |∫ q, g q ∂μ - ∫ q, nc q ∂μ| + |∫ q, nc q ∂ν - ∫ q, g q ∂ν| :=
      calc |∫ q, g q ∂μ - ∫ q, g q ∂ν|
          ≤ |∫ q, g q ∂μ - ∫ q, nc q ∂μ| + |∫ q, nc q ∂μ - ∫ q, g q ∂ν| :=
            abs_sub_le _ _ _
        _ = |∫ q, g q ∂μ - ∫ q, nc q ∂μ| + |∫ q, nc q ∂ν - ∫ q, g q ∂ν| := by rw [hmid]
    have hmulμ : μ.real Set.univ * ‖nc - g‖ ≤
        μ.real Set.univ * (ε / (μ.real Set.univ + ν.real Set.univ + 1)) :=
      mul_le_mul_of_nonneg_left hnear.le hμ
    have hmulν : ν.real Set.univ * ‖nc - g‖ ≤
        ν.real Set.univ * (ε / (μ.real Set.univ + ν.real Set.univ + 1)) :=
      mul_le_mul_of_nonneg_left hnear.le hν
    have hDeq : (μ.real Set.univ + ν.real Set.univ + 1) *
        (ε / (μ.real Set.univ + ν.real Set.univ + 1)) = ε := by
      field_simp
    have hfinal : μ.real Set.univ * (ε / (μ.real Set.univ + ν.real Set.univ + 1)) +
        ν.real Set.univ * (ε / (μ.real Set.univ + ν.real Set.univ + 1)) ≤ 0 + ε := by
      rw [zero_add, ← add_mul]
      calc (μ.real Set.univ + ν.real Set.univ) *
            (ε / (μ.real Set.univ + ν.real Set.univ + 1))
          ≤ (μ.real Set.univ + ν.real Set.univ + 1) *
              (ε / (μ.real Set.univ + ν.real Set.univ + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε := hDeq
    linarith
  have := sub_eq_zero.mp (abs_eq_zero.mp hzero)
  exact this

/-! ### Replica laws -/

/-- **NOTE2 (11).** The replica law of a random probability vector: the probability that a
cohort of conditionally independent draws, indexed by `slots`, reads out the letters `z`. -/
def replicaLaw (m : ℕ) (μ : Measure ↥(stdSimplex ℝ (Fin m))) {slots : Type}
    [Fintype slots] (z : slots → Fin m) : ℝ :=
  ∫ q, ∏ i, (q : Fin m → ℝ) (z i) ∂μ

/-- The cohort of `∑ e` slots that draws letter `a` exactly `e a` times. -/
def exponentListing (m : ℕ) (e : Fin m → ℕ) : Fin (∑ a, e a) → Fin m :=
  fun k ↦ (finSigmaFinEquiv.symm k).1

/-- That cohort reads out exactly the monomial of exponent vector `e`. -/
theorem prod_exponentListing (m : ℕ) (e : Fin m → ℕ) (q : ↥(stdSimplex ℝ (Fin m))) :
    ∏ k, (q : Fin m → ℝ) (exponentListing m e k) = monomialMap m e q := by
  rw [monomialMap_apply,
    ← Equiv.prod_comp (finSigmaFinEquiv (n := e))
      fun k ↦ (q : Fin m → ℝ) (exponentListing m e k)]
  simp only [exponentListing, Equiv.symm_apply_apply]
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun a _ ↦ by simp

/-- **Every monomial moment is a replica probability.** This is what makes the replica family
of NOTE2 (11) the same data as the monomial moments. -/
theorem replicaLaw_exponentListing (m : ℕ) (μ : Measure ↥(stdSimplex ℝ (Fin m)))
    (e : Fin m → ℕ) :
    replicaLaw m μ (exponentListing m e) = ∫ q, monomialMap m e q ∂μ := by
  simp only [replicaLaw, prod_exponentListing]

/-- **NOTE2 Theorem 3, completeness half.** Two finite mixing laws on the simplex whose
replica laws agree at every cohort size and every letter listing are equal as measures. The
law of a single observation is the case `n = 1`, and the theorem says exactly that the whole
family, not any one member of it, pins the mixing law down. -/
theorem measure_eq_of_replicaLaw_eq (m : ℕ)
    (μ ν : Measure ↥(stdSimplex ℝ (Fin m))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hreplica : ∀ (n : ℕ) (z : Fin n → Fin m), replicaLaw m μ z = replicaLaw m ν z) :
    μ = ν := by
  refine measure_eq_of_monomial_moments_eq m μ ν fun e ↦ ?_
  rw [← replicaLaw_exponentListing, ← replicaLaw_exponentListing]
  exact hreplica _ (exponentListing m e)

/-! ### The corpus report law as a point of the simplex -/

/-- A finite report law on the alphabet is exactly a point of the simplex. -/
def simplexPoint (m : ℕ) (law : FiniteReportLaw (Fin m)) : ↥(stdSimplex ℝ (Fin m)) :=
  ⟨law.mass, law.mass_nonneg, law.mass_sum⟩

/-- The monomial readout at the point of a finite report law is the product of its masses,
so the replica data of a degenerate mixing law is the independent product law. -/
theorem monomialMap_simplexPoint (m : ℕ) (law : FiniteReportLaw (Fin m)) (e : Fin m → ℕ) :
    monomialMap m e (simplexPoint m law) = ∏ a, law.mass a ^ e a :=
  monomialMap_apply m e (simplexPoint m law)

/-! ### The tagged source/target pair -/

/-- The embedding of a source and a target probability vector into a single probability
vector on the disjoint union of the two alphabets, each half weighted. -/
def taggedPair (ms mt : ℕ) (source : Fin ms → ℝ) (target : Fin mt → ℝ) :
    (Fin ms ⊕ Fin mt) → ℝ :=
  Sum.elim (fun i ↦ source i / 2) (fun j ↦ target j / 2)

/-- The tagged pair of two probability vectors is a probability vector. -/
theorem taggedPair_mem (ms mt : ℕ) (source : Fin ms → ℝ) (target : Fin mt → ℝ)
    (hs : source ∈ stdSimplex ℝ (Fin ms)) (ht : target ∈ stdSimplex ℝ (Fin mt)) :
    taggedPair ms mt source target ∈ stdSimplex ℝ (Fin ms ⊕ Fin mt) := by
  obtain ⟨hsnn, hssum⟩ := hs
  obtain ⟨htnn, htsum⟩ := ht
  constructor
  · rintro (i | j)
    · exact div_nonneg (hsnn i) (by norm_num)
    · exact div_nonneg (htnn j) (by norm_num)
  · rw [Fintype.sum_sum_type]
    simp only [taggedPair, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_div, hssum, htsum]
    norm_num

/-- The tagging embedding is injective, so completeness on the union alphabet gives
completeness for the source/target pair. -/
theorem taggedPair_injective (ms mt : ℕ) :
    Function.Injective fun p : (Fin ms → ℝ) × (Fin mt → ℝ) ↦ taggedPair ms mt p.1 p.2 := by
  rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ heq
  have hs : ∀ i, s₁ i = s₂ i := by
    intro i
    have := congrFun heq (Sum.inl i)
    simp only [taggedPair, Sum.elim_inl] at this
    linarith
  have ht : ∀ j, t₁ j = t₂ j := by
    intro j
    have := congrFun heq (Sum.inr j)
    simp only [taggedPair, Sum.elim_inr] at this
    linarith
  exact Prod.ext (funext hs) (funext ht)

/-- The tagging embedding is continuous. -/
theorem continuous_taggedPair (ms mt : ℕ) :
    Continuous fun p : (Fin ms → ℝ) × (Fin mt → ℝ) ↦ taggedPair ms mt p.1 p.2 := by
  refine continuous_pi fun x ↦ ?_
  cases x with
  | inl i =>
    exact ((continuous_apply i).comp continuous_fst).div_const 2
  | inr j =>
    exact ((continuous_apply j).comp continuous_snd).div_const 2

end

end Descent.Portability.ReplicaMomentCompleteness

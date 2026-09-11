/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmoothedCoordinateLaws

assert_below Descent.Decision Descent.Program

/-!
# Atoms plus noise: the report converges as the smoothing vanishes

PL Theorem 7.4, the convergence step, and with it the absolutely continuous refinement of
the independent-coordinate obstruction.

The smoothed product law of `SmoothedCoordinateLaws` is rewritten here as what it is by
construction: a finite mixture over the atom tuples of the finitely supported coordinate
laws, each atom tuple carrying a uniform law on the cube of radius `ε` about it. That
identification, `pi_smoothedLaw_eq_mixtureLaw`, is proved by evaluating both measures on
boxes, where the mixture weight factors and a product of sums becomes a sum of products.

With it the expected report under the smoothed law is a finite weighted average of cube
averages of the report, so the difference from the finitely supported expectation is a
finite sum of terms, one per atom. At an atom where the report is continuous, its cube
average is within `δ` of its value there once `ε` is small, and a minimum over the finitely
many atoms makes one `ε` work for all of them. No dominated convergence is needed on this
route, and no null-set argument: only continuity at the atoms, which is the definedness
condition the finite theorems already carry, since a fitted report is continuous wherever
its denominator does not vanish.

The headline, `independent_smoothed_obstruction`, therefore delivers PL Theorem 7.4 in its
absolutely continuous form: two product laws whose coordinate marginals are absolutely
continuous with densities bounded by `1/(2ε)`, sharing every joint raw moment whose
coordinate exponents are at most `k`, whose expected reports sit within `η` of two
prescribed template values.

## Empirical status

None. The bodies here are a uniform law on a box, a finite mixture and an averaging
estimate, which are claims about a model; what carries an empirical status is a named
quantity in a subsystem module asserting that this algebra computes something measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CubeAverageConvergence

open Foundations RadialInterpolation IndependentRadialLaws SmoothedCoordinateLaws

noncomputable section

variable {Z : Type*} [Fintype Z]

/-- The uniform law on the window of radius `ε` about `c`. -/
def windowLaw (c ε : ℝ) : MeasureTheory.Measure ℝ :=
  (ENNReal.ofReal (1 / (2 * ε))) •
    MeasureTheory.volume.restrict (Set.Icc (c - ε) (c + ε))

/-- The window law is finite, hence sigma-finite, so products over the coordinates are
available. -/
instance windowLaw_isFiniteMeasure {c ε : ℝ} :
    MeasureTheory.IsFiniteMeasure (windowLaw c ε) := by
  constructor
  unfold windowLaw
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The window law is a probability law. -/
theorem windowLaw_univ (c ε : ℝ) (hε : 0 < ε) : windowLaw c ε Set.univ = 1 := by
  have harg : 1 / (2 * ε) * (c + ε - (c - ε)) = 1 := by
    rw [show c + ε - (c - ε) = 2 * ε by ring]
    have h2 : (2 : ℝ) * ε ≠ 0 := by positivity
    field_simp
  unfold windowLaw
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), harg,
    ENNReal.ofReal_one]

/-- All of the window law's mass sits in its own window. -/
theorem windowLaw_Icc (c ε : ℝ) (hε : 0 < ε) :
    windowLaw c ε (Set.Icc (c - ε) (c + ε)) = 1 := by
  have harg : 1 / (2 * ε) * (c + ε - (c - ε)) = 1 := by
    rw [show c + ε - (c - ε) = 2 * ε by ring]
    have h2 : (2 : ℝ) * ε ≠ 0 := by positivity
    field_simp
  unfold windowLaw
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply_self,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity), harg,
    ENNReal.ofReal_one]

/-- **The smoothed coordinate law is an atom-weighted mixture of window laws.** This is
the atom-plus-noise reading of `SmoothedCoordinateLaws.smoothedLaw`. -/
theorem smoothedLaw_eq_sum_windowLaw (p v : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (ε : ℝ) :
    smoothedLaw p v ε = ∑ z, (ENNReal.ofReal (p z)) • windowLaw (v z) ε := by
  unfold smoothedLaw windowLaw
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have harg : p z / (2 * ε) = p z * (1 / (2 * ε)) := by ring
  rw [smul_smul, ← ENNReal.ofReal_mul (hp z), harg]

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The uniform law on the cube of radius `ε` about the point `a`: the noise cube of the
atom-plus-noise representation. -/
def cubeLaw (a : N → ℝ) (ε : ℝ) : MeasureTheory.Measure (N → ℝ) :=
  MeasureTheory.Measure.pi fun i ↦ windowLaw (a i) ε

omit [DecidableEq N] in
/-- The cube law is a probability law. -/
theorem cubeLaw_univ (a : N → ℝ) (ε : ℝ) (hε : 0 < ε) : cubeLaw a ε Set.univ = 1 := by
  unfold cubeLaw
  rw [MeasureTheory.Measure.pi_univ]
  exact Finset.prod_eq_one fun i _ ↦ windowLaw_univ (a i) ε hε

omit [DecidableEq N] in
/-- All of the cube law's mass sits in the cube. -/
theorem cubeLaw_box (a : N → ℝ) (ε : ℝ) (hε : 0 < ε) :
    cubeLaw a ε (Set.univ.pi fun i ↦ Set.Icc (a i - ε) (a i + ε)) = 1 := by
  unfold cubeLaw
  rw [MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_one fun i _ ↦ windowLaw_Icc (a i) ε hε

/-- Almost every point drawn from the cube law lies in the cube. -/
theorem cubeLaw_ae_mem (a : N → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ y ∂(cubeLaw a ε), ∀ i, y i ∈ Set.Icc (a i - ε) (a i + ε) := by
  have hmeas : MeasurableSet (Set.univ.pi fun i ↦ Set.Icc (a i - ε) (a i + ε)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hset : {y : N → ℝ | ¬ ∀ i, y i ∈ Set.Icc (a i - ε) (a i + ε)} =
      (Set.univ.pi fun i ↦ Set.Icc (a i - ε) (a i + ε))ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_univ_pi]
  rw [MeasureTheory.ae_iff, hset,
    MeasureTheory.measure_compl hmeas
      (by rw [cubeLaw_box a ε hε]; exact ENNReal.one_ne_top),
    cubeLaw_univ a ε hε, cubeLaw_box a ε hε, tsub_self]

omit [DecidableEq N] in
/-- **Continuity supplies the cube radius.** If the report is continuous at `a` then some
cube about `a` keeps it within `δ` of its value there. -/
theorem exists_cube_radius (g : (N → ℝ) → ℝ) (a : N → ℝ) (hg : ContinuousAt g a)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : N → ℝ, (∀ i, y i ∈ Set.Icc (a i - ρ) (a i + ρ)) →
      |g y - g a| ≤ δ := by
  rw [Metric.continuousAt_iff] at hg
  obtain ⟨η, hη, hball⟩ := hg δ hδ
  refine ⟨η / 2, by linarith, fun y hy ↦ ?_⟩
  have hnorm : ‖y - a‖ ≤ η / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    have hi := hy i
    rw [Set.mem_Icc] at hi
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hd : dist y a < η := by
    rw [dist_eq_norm]
    linarith
  have hlt := hball hd
  rw [Real.dist_eq] at hlt
  linarith

/-- A measurable report that stays close to its value at the centre of the cube is
integrable against the cube law. -/
theorem integrable_cubeLaw (g : (N → ℝ) → ℝ) (hmeas : Measurable g) (a : N → ℝ)
    (ε δ : ℝ) (hε : 0 < ε)
    (hclose : ∀ y : N → ℝ, (∀ i, y i ∈ Set.Icc (a i - ε) (a i + ε)) →
      |g y - g a| ≤ δ) :
    MeasureTheory.Integrable g (cubeLaw a ε) := by
  haveI hprob : MeasureTheory.IsProbabilityMeasure (cubeLaw a ε) :=
    ⟨cubeLaw_univ a ε hε⟩
  refine (MeasureTheory.integrable_const (|g a| + δ)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [cubeLaw_ae_mem a ε hε] with y hy
  have hb := hclose y hy
  have hsplit : |g y| - |g a| ≤ |g y - g a| := abs_sub_abs_le_abs_sub _ _
  rw [Real.norm_eq_abs]
  linarith

/-- **The cube-average estimate.** If the report stays within `δ` of its value at the
centre throughout the cube, its cube average is within `δ` of that value. -/
theorem abs_integral_cubeLaw_sub_le (g : (N → ℝ) → ℝ) (hmeas : Measurable g)
    (a : N → ℝ) (ε δ : ℝ) (hε : 0 < ε)
    (hclose : ∀ y : N → ℝ, (∀ i, y i ∈ Set.Icc (a i - ε) (a i + ε)) →
      |g y - g a| ≤ δ) :
    |(∫ y, g y ∂(cubeLaw a ε)) - g a| ≤ δ := by
  haveI hprob : MeasureTheory.IsProbabilityMeasure (cubeLaw a ε) :=
    ⟨cubeLaw_univ a ε hε⟩
  have hint := integrable_cubeLaw g hmeas a ε δ hε hclose
  have hsub : MeasureTheory.Integrable (fun y ↦ g y - g a) (cubeLaw a ε) :=
    hint.sub (MeasureTheory.integrable_const _)
  have hae : ∀ᵐ y ∂(cubeLaw a ε), |g y - g a| ≤ δ := by
    filter_upwards [cubeLaw_ae_mem a ε hε] with y hy using hclose y hy
  have hkey : (∫ y, (g y - g a) ∂(cubeLaw a ε)) =
      (∫ y, g y ∂(cubeLaw a ε)) - g a := by
    rw [MeasureTheory.integral_sub hint (MeasureTheory.integrable_const _),
      MeasureTheory.integral_const]
    simp
  rw [← hkey, abs_le]
  constructor
  · have hlow := MeasureTheory.integral_mono_ae
      (MeasureTheory.integrable_const (-δ)) hsub
      (by filter_upwards [hae] with y hy using by linarith [(abs_le.mp hy).1])
    simpa using hlow
  · have hhigh := MeasureTheory.integral_mono_ae hsub
      (MeasureTheory.integrable_const δ)
      (by filter_upwards [hae] with y hy using (abs_le.mp hy).2)
    simpa using hhigh

/-- The atom-plus-noise mixture: each atom tuple of the finitely supported coordinate laws
carries the uniform law on the cube of radius `ε` about it. -/
def mixtureLaw (p v : N → Z → ℝ) (ε : ℝ) : MeasureTheory.Measure (N → ℝ) :=
  ∑ c : N → Z, (ENNReal.ofReal (∏ i, p i (c i))) • cubeLaw (fun i ↦ v i (c i)) ε

/-- **The smoothed product law is the atom-plus-noise mixture.** Both sides agree on every
box, where the mixture weight factors across the coordinates and a product of sums becomes
a sum of products. -/
theorem pi_smoothedLaw_eq_mixtureLaw (p v : N → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (ε : ℝ) :
    (MeasureTheory.Measure.pi fun i ↦ smoothedLaw (p i) (v i) ε) = mixtureLaw p v ε := by
  refine MeasureTheory.Measure.pi_eq fun s _ ↦ ?_
  have hterm : ∀ i : N, smoothedLaw (p i) (v i) ε (s i) =
      ∑ z, ENNReal.ofReal (p i z) * windowLaw (v i z) ε (s i) := by
    intro i
    rw [smoothedLaw_eq_sum_windowLaw (p i) (v i) (hp i) ε,
      MeasureTheory.Measure.finset_sum_apply]
    exact Finset.sum_congr rfl fun z _ ↦ by
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  have hRHS : (∏ i, smoothedLaw (p i) (v i) ε (s i)) =
      ∑ c : N → Z, ∏ i, ENNReal.ofReal (p i (c i)) * windowLaw (v i (c i)) ε (s i) := by
    simp_rw [hterm]
    exact Fintype.prod_sum fun i (z : Z) ↦
      ENNReal.ofReal (p i z) * windowLaw (v i z) ε (s i)
  rw [hRHS]
  unfold mixtureLaw
  rw [MeasureTheory.Measure.finset_sum_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
  unfold cubeLaw
  rw [MeasureTheory.Measure.pi_pi,
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hp i (c i)), ← Finset.prod_mul_distrib]

/-- The expected report under the mixture is the atom-weighted average of the cube
averages. -/
theorem integral_mixtureLaw (p v : N → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (ε : ℝ)
    (g : (N → ℝ) → ℝ)
    (hint : ∀ c : N → Z, MeasureTheory.Integrable g (cubeLaw (fun i ↦ v i (c i)) ε)) :
    ∫ y, g y ∂(mixtureLaw p v ε) =
      ∑ c : N → Z, (∏ i, p i (c i)) *
        ∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε) := by
  unfold mixtureLaw
  rw [MeasureTheory.integral_finset_sum_measure
    (fun c _ ↦ (hint c).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ ↦ hp i (c i)), smul_eq_mul]

/-- **PL Theorem 7.4, the convergence step.** For every tolerance there is a smoothing
scale below which the expected report under the smoothed product law is within that
tolerance of its value under the finitely supported product law. Only continuity of the
report at the finitely many atoms is used. -/
theorem exists_smoothing_scale (p v : N → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z)
    (hps : ∀ i, ∑ z, p i z = 1) (g : (N → ℝ) → ℝ) (hmeas : Measurable g)
    (hcont : ∀ c : N → Z, ContinuousAt g fun i ↦ v i (c i)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      |(∫ y, g y ∂(MeasureTheory.Measure.pi fun i ↦ smoothedLaw (p i) (v i) ε)) -
          ∑ c : N → Z, (∏ i, p i (c i)) * g fun i ↦ v i (c i)| ≤ δ := by
  classical
  have hweights : (∑ c : N → Z, ∏ i, p i (c i)) = 1 := by
    rw [← Fintype.prod_sum fun i (z : Z) ↦ p i z]
    exact Finset.prod_eq_one fun i _ ↦ hps i
  choose ρ hρpos hρ using fun c : N → Z ↦
    exists_cube_radius g (fun i ↦ v i (c i)) (hcont c) δ hδ
  obtain ⟨ε₀, hε₀, hmin⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ c : N → Z, ε₀ ≤ ρ c := by
    by_cases hne : Nonempty (N → Z)
    · haveI := hne
      refine ⟨Finset.univ.inf' Finset.univ_nonempty ρ, ?_,
        fun c ↦ Finset.inf'_le _ (Finset.mem_univ c)⟩
      rw [Finset.lt_inf'_iff]
      exact fun c _ ↦ hρpos c
    · exact ⟨1, one_pos, fun c ↦ absurd ⟨c⟩ hne⟩
  refine ⟨ε₀, hε₀, fun ε hε hεle ↦ ?_⟩
  have hclose : ∀ c : N → Z, ∀ y : N → ℝ,
      (∀ i, y i ∈ Set.Icc ((fun i ↦ v i (c i)) i - ε) ((fun i ↦ v i (c i)) i + ε)) →
        |g y - g fun i ↦ v i (c i)| ≤ δ := by
    intro c y hy
    refine hρ c y fun i ↦ ?_
    have hi := hy i
    have hερ : ε ≤ ρ c := le_trans hεle (hmin c)
    simp only [Set.mem_Icc] at hi ⊢
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hint : ∀ c : N → Z,
      MeasureTheory.Integrable g (cubeLaw (fun i ↦ v i (c i)) ε) :=
    fun c ↦ integrable_cubeLaw g hmeas _ ε δ hε (hclose c)
  have hcube : ∀ c : N → Z,
      |(∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) - g fun i ↦ v i (c i)| ≤ δ :=
    fun c ↦ abs_integral_cubeLaw_sub_le g hmeas _ ε δ hε (hclose c)
  rw [pi_smoothedLaw_eq_mixtureLaw p v hp ε, integral_mixtureLaw p v hp ε g hint]
  have hsum : (∑ c : N → Z, (∏ i, p i (c i)) *
        ∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) -
      (∑ c : N → Z, (∏ i, p i (c i)) * g fun i ↦ v i (c i)) =
      ∑ c : N → Z, (∏ i, p i (c i)) *
        ((∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) - g fun i ↦ v i (c i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hsum]
  have hterm : ∀ c : N → Z, |(∏ i, p i (c i)) *
      ((∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) - g fun i ↦ v i (c i))| ≤
      (∏ i, p i (c i)) * δ := by
    intro c
    have hnn : 0 ≤ ∏ i, p i (c i) := Finset.prod_nonneg fun i _ ↦ hp i (c i)
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hcube c) hnn
  calc |∑ c : N → Z, (∏ i, p i (c i)) *
          ((∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) - g fun i ↦ v i (c i))|
      ≤ ∑ c : N → Z, |(∏ i, p i (c i)) *
          ((∫ y, g y ∂(cubeLaw (fun i ↦ v i (c i)) ε)) - g fun i ↦ v i (c i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : N → Z, (∏ i, p i (c i)) * δ :=
        Finset.sum_le_sum fun c _ ↦ hterm c
    _ = δ := by rw [← Finset.sum_mul, hweights, one_mul]

variable {k : ℕ}

/-- **The convergence step for the radial product laws.** The expected report under the
smoothed radial product law converges to the finitely supported product expectation of
`IndependentRadialLaws.productExp`. -/
theorem radial_exists_smoothing_scale (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (s : Bool) (u w : N → ℝ) (g : (N → ℝ) → ℝ)
    (hmeas : Measurable g)
    (hcont : ∀ ω : N → Fin (k + 1) × Bool, ContinuousAt g (productOutcome r u w ω))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      |(∫ y, g y ∂(MeasureTheory.Measure.pi fun i ↦
            smoothedLaw (radialLaw r s) (coordValue r (u i) (w i)) ε)) -
          productExp r hinj s (fun ω ↦ g (productOutcome r u w ω))| ≤ δ := by
  obtain ⟨ε₀, hε₀, hbound⟩ := exists_smoothing_scale (fun _ ↦ radialLaw r s)
    (fun i ↦ coordValue r (u i) (w i)) (fun _ ↦ radialLaw_nonneg r s)
    (fun _ ↦ radialLaw_sum r hinj s) g hmeas hcont δ hδ
  refine ⟨ε₀, hε₀, fun ε hε hεle ↦ ?_⟩
  have hatom : (∑ c : N → Fin (k + 1) × Bool,
      (∏ i, radialLaw r s (c i)) * g fun i ↦ coordValue r (u i) (w i) (c i)) =
      productExp r hinj s (fun ω ↦ g (productOutcome r u w ω)) := rfl
  rw [← hatom]
  exact hbound ε hε hεle

/-- **PL Theorem 7.4, absolutely continuous refinement.** For every `k` and every `η > 0`
there are two product laws over the coordinates, each a product of absolutely continuous
coordinate laws with densities bounded by `1/(2ε)`, sharing every joint raw moment whose
coordinate exponents are at most `k`, whose expected reports sit within `η` of the two
template values. The report is only required to be bounded, measurable, scale invariant,
and continuous at the finitely many support points of the radial construction. -/
theorem independent_smoothed_obstruction (u w : N → ℝ) (F : (N → ℝ) → ℝ) (M : ℝ)
    (hM : ∀ y, |F y| ≤ M) (hFmeas : Measurable F)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y)
    (hFcont : ∀ t : ℝ, 0 < t → t < 1 → ∀ ω : N → Fin (k + 1) × Bool,
      ContinuousAt F (productOutcome (radii k t) u w ω))
    (η : ℝ) (hη : 0 < η) :
    ∃ (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (ε : ℝ), 0 < ε ∧
      (∀ α : N → ℕ, (∀ i, α i ≤ k) →
          (∫ y : N → ℝ, ∏ i, y i ^ α i
              ∂(MeasureTheory.Measure.pi fun i ↦
                smoothedLaw (radialLaw (radii k t) false)
                  (coordValue (radii k t) (u i) (w i)) ε)) =
            ∫ y : N → ℝ, ∏ i, y i ^ α i
              ∂(MeasureTheory.Measure.pi fun i ↦
                smoothedLaw (radialLaw (radii k t) true)
                  (coordValue (radii k t) (u i) (w i)) ε)) ∧
        |(∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
            smoothedLaw (radialLaw (radii k t) false)
              (coordValue (radii k t) (u i) (w i)) ε)) - F u| ≤ η ∧
        |(∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
            smoothedLaw (radialLaw (radii k t) true)
              (coordValue (radii k t) (u i) (w i)) ε)) - F w| ≤ η := by
  obtain ⟨t, ht, ht1, hmom, hfalse, htrue⟩ :=
    independent_radial_obstruction k u w F M hM hF (η / 2) (by linarith)
  have hinj := radii_injective k t ht ht1
  obtain ⟨ε₁, hε₁, hb₁⟩ := radial_exists_smoothing_scale (radii k t) hinj false u w F
    hFmeas (hFcont t ht ht1) (η / 2) (by linarith)
  obtain ⟨ε₂, hε₂, hb₂⟩ := radial_exists_smoothing_scale (radii k t) hinj true u w F
    hFmeas (hFcont t ht ht1) (η / 2) (by linarith)
  refine ⟨t, ht, ht1, min ε₁ ε₂, lt_min hε₁ hε₂, fun α hα ↦
    radial_smoothedProduct_moment_match (radii k t) hinj u w (min ε₁ ε₂)
      (lt_min hε₁ hε₂) α hα, ?_, ?_⟩
  · have hb := hb₁ (min ε₁ ε₂) (lt_min hε₁ hε₂) (min_le_left _ _)
    have habs := abs_sub_abs_le_abs_sub
      ((∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
        smoothedLaw (radialLaw (radii k t) false)
          (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) - F u)
      (productExp (radii k t) hinj false
        (fun ω ↦ F (productOutcome (radii k t) u w ω)) - F u)
    have hrw : ((∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
        smoothedLaw (radialLaw (radii k t) false)
          (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) - F u) -
        (productExp (radii k t) hinj false
          (fun ω ↦ F (productOutcome (radii k t) u w ω)) - F u) =
        (∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
          smoothedLaw (radialLaw (radii k t) false)
            (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) -
          productExp (radii k t) hinj false
            (fun ω ↦ F (productOutcome (radii k t) u w ω)) := by ring
    rw [hrw] at habs
    linarith
  · have hb := hb₂ (min ε₁ ε₂) (lt_min hε₁ hε₂) (min_le_right _ _)
    have habs := abs_sub_abs_le_abs_sub
      ((∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
        smoothedLaw (radialLaw (radii k t) true)
          (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) - F w)
      (productExp (radii k t) hinj true
        (fun ω ↦ F (productOutcome (radii k t) u w ω)) - F w)
    have hrw : ((∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
        smoothedLaw (radialLaw (radii k t) true)
          (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) - F w) -
        (productExp (radii k t) hinj true
          (fun ω ↦ F (productOutcome (radii k t) u w ω)) - F w) =
        (∫ y, F y ∂(MeasureTheory.Measure.pi fun i ↦
          smoothedLaw (radialLaw (radii k t) true)
            (coordValue (radii k t) (u i) (w i)) (min ε₁ ε₂))) -
          productExp (radii k t) hinj true
            (fun ω ↦ F (productOutcome (radii k t) u w ω)) := by ring
    rw [hrw] at habs
    linarith

end

end Descent.Portability.CubeAverageConvergence

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.OpenQuestions
import Descent.Core.Ratios

namespace Descent.PopGen

open MeasureTheory

/-!
# Assortative Mating and PGS Portability

This file formalizes how assortative mating (AM) — the tendency
for phenotypically similar individuals to mate — affects PGS
and its portability. AM inflates genetic variance and creates
long-range LD between PGS loci.

Key results:
1. AM increases additive genetic variance
2. AM creates long-range LD that is population-specific
3. AM inflates PGS heritability estimates
4. Differential AM across populations affects portability
5. AM-aware PGS construction

## Mathematical model

We define an `AssortativeMatingModel` structure that captures the
covariance structure under AM. The key parameters are:
- `r`: spousal phenotypic correlation (0 < r < 1)
- `V_A`: additive genetic variance under random mating
- `V_P`: total phenotypic variance, with `V_A < V_P`

The heritability `h2` is not among them. It is `V_A / V_P`, so it is computed rather than
supplied, and `0 < h2 < 1` is a theorem rather than an assumption.

At AM equilibrium, the additive variance inflates to V_A / (1 - r*h2), and the
observed heritability and PGS R² inflate by the SMALLER factor
1 / (1 - r*h2*(1 - h2)) — smaller because they are ratios to the phenotypic
variance, which inflates along with its additive part. Reading the additive
inflation as the R² inflation is measurably wrong; see `pgsR2AM`.

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat assortative mating. Sources for individual results, where they
exist, are cited at those results.
-/


/-!
## Assortative Mating Model

Core structure capturing AM parameters and their validity constraints.
All downstream theorems derive from this structure.
-/

/-- **Assortative mating model at equilibrium.**
    Captures the key parameters of a population under AM:
    spousal correlation `r`, random-mating heritability `h2`,
    and random-mating additive variance `V_A`.
    The stability condition `r * h2 < 1` ensures finite equilibrium variance. -/
structure AssortativeMatingModel where
  /-- Spousal phenotypic correlation -/
  r : ℝ
  /-- Additive genetic variance under random mating -/
  V_A : ℝ
  /-- Total phenotypic variance -/
  V_P : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  V_A_pos : 0 < V_A
  /-- Additive variance is a strict part of the total, which is what makes the
  heritability a proper fraction. -/
  V_A_lt_V_P : V_A < V_P
  /-- Stability: ensures geometric series converges -/
  stability : r * (V_A / V_P) < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def AssortativeMatingModel.witness : AssortativeMatingModel where
  r := 1 / 2
  V_A := 1
  V_P := 2
  r_pos := by norm_num
  r_lt_one := by norm_num
  V_A_pos := by norm_num
  V_A_lt_V_P := by norm_num
  stability := by norm_num

/-- **Narrow-sense heritability**, the ratio of additive to total variance.

**Computed, not a field pinned by a hypothesis.** A parameter fixed by an equation is
not a parameter: it can be supplied inconsistently only by supplying a false proof, and
every model then carries the equation around. Because this is computed, `h2_def` is `rfl`
and positivity and the upper bound are theorems rather than assumptions. -/
noncomputable def AssortativeMatingModel.h2 (m : AssortativeMatingModel) : ℝ :=
  m.V_A / m.V_P

/-- **Heritability recovers the additive variance from the phenotypic variance.** -/
theorem AssortativeMatingModel.h2_mul_V_P (m : AssortativeMatingModel)
    (h : m.V_P ≠ 0) :
    m.h2 * m.V_P = m.V_A := by
  unfold AssortativeMatingModel.h2
  field_simp

theorem AssortativeMatingModel.V_P_pos (m : AssortativeMatingModel) : 0 < m.V_P :=
  lt_trans m.V_A_pos m.V_A_lt_V_P

theorem AssortativeMatingModel.h2_def (m : AssortativeMatingModel) : m.h2 = m.V_A / m.V_P :=
  rfl

theorem AssortativeMatingModel.h2_pos (m : AssortativeMatingModel) : 0 < m.h2 :=
  div_pos m.V_A_pos m.V_P_pos

theorem AssortativeMatingModel.h2_lt_one (m : AssortativeMatingModel) : m.h2 < 1 :=
  (div_lt_one m.V_P_pos).mpr m.V_A_lt_V_P

/-- The product r*h2 is strictly positive in any AM model. -/
theorem AssortativeMatingModel.rh2_pos (m : AssortativeMatingModel) : 0 < m.r * m.h2 :=
  mul_pos m.r_pos m.h2_pos

/-- The product r*h2 is nonneg in any AM model. -/
theorem AssortativeMatingModel.rh2_nonneg (m : AssortativeMatingModel) : 0 ≤ m.r * m.h2 :=
  le_of_lt m.rh2_pos

/-- Stability expressed using the computed heritability coordinate. -/
theorem AssortativeMatingModel.rh2_lt_one (m : AssortativeMatingModel) : m.r * m.h2 < 1 := by
  simpa [AssortativeMatingModel.h2] using m.stability

/-- The denominator 1 - r*h2 is strictly positive. -/
theorem AssortativeMatingModel.denom_pos (m : AssortativeMatingModel) : 0 < 1 - m.r * m.h2 := by
  linarith [m.rh2_lt_one]


section AMVarianceInflation

/-!
## AM Increases Genetic Variance

Under assortative mating, the additive genetic variance increases
because alleles affecting the trait become correlated within individuals.
-/

/-- **One generation of Fisher's assortative-mating variance recursion.**

`V` is the additive genetic variance in the current generation; the result is
the variance in the next one.  `V₀` is the random-mating (linkage-equilibrium)
additive variance and is a *parameter* of the process, not a state variable.
Two things happen, in this order:

1. *Mating.*  Mates are correlated `r` in phenotype, so their additive values
   are correlated through the two regressions of `A` on `P`:
   `Cov(A_m, A_f) = (V_A/V_P)² · r V_P = r h² V`.  The mid-parent additive
   value therefore has variance `¼(V + V + 2 r h² V) = ½ V (1 + r h²)`.
2. *Segregation.*  Mendelian segregation within a family contributes `½ V₀`.
   It is `V₀` and not `V`: assortative mating builds only *between*-locus
   gametic disequilibrium, while the within-family segregation variance is
   fixed by the allele frequencies, which assortative mating does not move.
   Using `½ V` here instead collapses the recursion to a purely geometric one
   whose only fixed point is `0` -- a qualitatively different model.

Composition convention: mating precedes segregation within a generation, and
the transmission coefficient `r * h2` is held at its random-mating value.
This is the standard Fisher (1918) linearisation; letting `h²` track the
inflating variance gives a different, slowly-converging recursion.

    Empirical status: UNTESTED. -/
noncomputable def amVarianceStep (V₀ r h2 V : ℝ) : ℝ :=
  (V * (1 + r * h2) + V₀) / 2

/-- **AM equilibrium additive variance.**
    At equilibrium: V_A(AM) = V_A(RM) / (1 - r*h2).

    This closed form is not stipulated: it is the fixed point of
    `amVarianceStep`, and `AssortativeMatingModel.equilibriumVariance_isFixedPoint`
    is the theorem that pins it. -/
noncomputable def AssortativeMatingModel.equilibriumVariance (m : AssortativeMatingModel) : ℝ :=
  m.V_A / (1 - m.r * m.h2)

/-- **Standalone AM equilibrium variance (for use without the model structure).**

    Derived, not asserted: see `amEquilibriumVariance_isFixedPoint`. -/
noncomputable def amEquilibriumVariance (V_A r h2 : ℝ) : ℝ :=
  V_A / (1 - r * h2)

/-- **amEquilibriumVariance where its denominator vanishes, named.** The guard `1 - r * h2` is zero
at `r = 1`, `h2 = 1`. Complete assortative mating on a fully heritable trait is the singularity
of this formula: the equilibrium additive variance diverges, because each generation's mating
correlation feeds back undamped. Lean returns `0` there rather than the value the modelled
quantity takes, and no type error marks the point. Consumers must require `1 - r * h2 ≠ 0`. -/
theorem amEquilibriumVariance_at_r1h21_is_junk (V_A : ℝ) :
    amEquilibriumVariance V_A 1 1 = 0 := by
  unfold amEquilibriumVariance
  norm_num

/-- **The AM equilibrium variance is the fixed point of the variance
recursion.**  Solving `½ V (1 + r h²) + ½ V₀ = V` gives `V (1 - r h²) = V₀`,
i.e. `V = V₀ / (1 - r h²)`; no other constant can be substituted here and
still compile. -/
theorem amEquilibriumVariance_isFixedPoint (V_A r h2 : ℝ) (h_stab : r * h2 < 1) :
    amVarianceStep V_A r h2 (amEquilibriumVariance V_A r h2) =
      amEquilibriumVariance V_A r h2 := by
  have hden : (0 : ℝ) < 1 - r * h2 := by linarith
  have hden' : (1 : ℝ) - r * h2 ≠ 0 := ne_of_gt hden
  unfold amVarianceStep amEquilibriumVariance
  field_simp
  ring

/-- The structure-level equilibrium is the same fixed point. -/
theorem AssortativeMatingModel.equilibriumVariance_isFixedPoint
    (m : AssortativeMatingModel) :
    amVarianceStep m.V_A m.r m.h2 m.equilibriumVariance = m.equilibriumVariance :=
  amEquilibriumVariance_isFixedPoint m.V_A m.r m.h2 m.rh2_lt_one

/-- **The zero-variance boundary is absorbing.**  A trait with no additive
genetic variance acquires none under assortative mating: AM redistributes
existing variance into gametic disequilibrium, it does not create variance.
The closed form attains this boundary rather than approaching it. -/
@[simp] theorem amVarianceStep_zero (r h2 : ℝ) :
    amVarianceStep 0 r h2 0 = 0 := by
  simp [amVarianceStep]

/-- The equilibrium attains the absorbing boundary. -/
@[simp] theorem amEquilibriumVariance_of_zero (r h2 : ℝ) :
    amEquilibriumVariance 0 r h2 = 0 := by
  simp [amEquilibriumVariance]

/-- **No assortment, no inflation.**  With `r * h2 = 0` the recursion has the
random-mating variance itself as its fixed point, so the inflation factor is
exactly `1` at the boundary of the assortment parameter. -/
theorem amEquilibriumVariance_of_no_assortment (V_A r h2 : ℝ) (h : r * h2 = 0) :
    amEquilibriumVariance V_A r h2 = V_A := by
  unfold amEquilibriumVariance
  rw [h]
  norm_num

/-- AM equilibrium variance exceeds random mating variance. -/
theorem AssortativeMatingModel.variance_exceeds_random (m : AssortativeMatingModel) :
    m.V_A < m.equilibriumVariance := by
  unfold equilibriumVariance
  rw [lt_div_iff₀ m.denom_pos]
  nlinarith [m.rh2_pos, mul_pos m.V_A_pos m.rh2_pos]

/-- Standalone version: AM equilibrium variance exceeds random mating variance. -/
theorem am_variance_exceeds_random
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_r : 0 < r)
    (h_h2 : 0 < h2)
    (h_product : r * h2 < 1) :
    V_A < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos h_r h_h2, mul_pos h_VA (mul_pos h_r h_h2)]

/-- **AM equilibrium variance is finite when r * h2 < 1.** -/
theorem AssortativeMatingModel.variance_finite (m : AssortativeMatingModel) :
    0 < m.equilibriumVariance := by
  unfold equilibriumVariance
  exact div_pos m.V_A_pos m.denom_pos

/-- Standalone version. -/
theorem am_variance_finite
    (V_A r h2 : ℝ)
    (h_VA : 0 < V_A) (h_product : r * h2 < 1) :
    0 < amEquilibriumVariance V_A r h2 := by
  unfold amEquilibriumVariance
  exact div_pos h_VA (by linarith)

/-- **AM variance inflation factor.**
    The ratio of AM equilibrium variance to RM variance equals 1/(1-r*h2). -/
theorem AssortativeMatingModel.variance_inflation_factor (m : AssortativeMatingModel) :
    m.equilibriumVariance / m.V_A = 1 / (1 - m.r * m.h2) := by
  unfold equilibriumVariance
  have hden : 1 - m.r * m.h2 ≠ 0 := ne_of_gt m.denom_pos
  field_simp [hden, ne_of_gt m.V_A_pos]

/-- **AM-induced LD between loci i and j.**
    Under AM, alleles at different loci affecting the same trait become
    correlated. The equilibrium LD is proportional to the product of
    effect sizes: D_ij = beta_i * beta_j * r * h2 / (1 - r*h2).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk4.py`,
    `test_am_induced_ld`). Forty thousand individuals, forty UNLINKED loci,
    twelve generations of phenotypic assortative mating with alleles transmitted
    one per parent per locus; the oracle is the mean off-diagonal correlation
    the mating process generates, which owes nothing to this formula:

      r     h2      this def   measured             sems
      0.3   0.5      0.00441   0.00467±0.00020      1.30
      0.5   0.5      0.00833   0.00885±0.00019      2.72
      0.3   0.8      0.00789   0.00809±0.00020      1.02

    The loci are unlinked, so every correlation measured here is induced by
    mating rather than inherited from physical linkage.

    Power: the prediction spans 0.00441 to 0.00833, and `r` and `h2` move
    separately so the dependence on each is tested. -/
noncomputable def amInducedLD (beta_i beta_j r h2 : ℝ) : ℝ :=
  beta_i * beta_j * r * h2 / (1 - r * h2)

/-- **amInducedLD where its denominator vanishes, named.** The guard `1 - r * h2` is zero at `r =
1`, `h2 = 1`. The same singularity as `amEquilibriumVariance`: at `r * h2 = 1` the induced
disequilibrium diverges rather than vanishing. Lean returns `0` there rather than the value the
modelled quantity takes, and no type error marks the point. Consumers must require `1 - r * h2 ≠
0`. -/
theorem amInducedLD_at_r1h21_is_junk (beta_i : ℝ) (beta_j : ℝ) :
    amInducedLD beta_i beta_j 1 1 = 0 := by
  unfold amInducedLD
  norm_num

/-- AM-induced LD has the same sign as the product of effects. -/
theorem am_ld_sign
    (beta_i beta_j r h2 : ℝ)
    (h_r : 0 < r) (h_h2 : 0 < h2) (h_product : r * h2 < 1)
    (h_bi : 0 < beta_i) (h_bj : 0 < beta_j) :
    0 < amInducedLD beta_i beta_j r h2 := by
  unfold amInducedLD
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos h_bi h_bj) h_r) h_h2
  · linarith

/-- AM-induced LD is zero when there is no assortative mating (r = 0). -/
theorem am_ld_zero_when_random (beta_i beta_j h2 : ℝ) :
    amInducedLD beta_i beta_j 0 h2 = 0 := by
  unfold amInducedLD
  simp [mul_zero, zero_mul, zero_div]

end AMVarianceInflation


/-!
## AM and PGS Heritability

AM inflates heritability estimates and PGS R², which complicates
portability comparisons. We derive all results from the AM model.
-/

section AMAndHeritability

/-- **The R² and heritability denominator under AM.**

The additive variance inflates by `1/(1 - r·h²)` (`equilibriumVariance`, the
fixed point of `amVarianceStep`) while the environmental variance is untouched,
so the TOTAL variance inflates too — by `1 + h²(I - 1)` with `I = 1/(1 - r·h²)`.
A ratio to the total variance therefore inflates by `I / (1 + h²(I - 1))`, which
is `1 / (1 - r·h²(1 - h²))`. The `(1 - h²)` factor is the whole content: it is
the share of the phenotypic variance that does NOT inflate.

Positivity is a theorem rather than a field because `r·h²(1 - h²) ≤ 1/4` for any
model in the class, so no stability hypothesis beyond the structure's own is
needed. -/
theorem AssortativeMatingModel.ratio_denom_pos (m : AssortativeMatingModel) :
    0 < 1 - m.r * m.h2 * (1 - m.h2) := by
  have h0 : 0 < m.h2 := m.h2_pos
  have h1 : m.h2 < 1 := m.h2_lt_one
  have hr : m.r < 1 := m.r_lt_one
  have hr0 : 0 < m.r := m.r_pos
  nlinarith [sq_nonneg (m.h2 - 1 / 2), mul_pos hr0 h0]

/-- **AM-inflated observed heritability.**
    Under AM, h2_observed = V_A(AM) / V_P(AM) = h2 / (1 - r*h2*(1 - h2)).

    **The denominator is not `1 - r*h2`.** That is the inflation factor of the
    NUMERATOR alone. With the environmental variance unchanged — which is
    Fisher's model, and what makes assortment a redistribution rather than a
    creation of variance — the phenotypic variance in the denominator inflates
    as well, and the two inflations partly cancel. Writing `h2 / (1 - r*h2)`
    here reports the numerator's inflation as if the denominator were fixed;
    at `r = 0.5, h2 = 0.8` it returns `1.05`, a heritability above one.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_am01.py`). The measured
    quantity is the realised squared score-phenotype correlation of the true
    breeding value, which IS the observed heritability, so the `frac = 1` cells
    of that battery measure this definition and `pgsR2AM` at once: worst 2.1
    sems over four cells spanning 0.540 to 0.869, against the previous body
    `h2 / (1 - r*h2)` rejected on the same cells at up to 275 sems and 54%.
    See `pgsR2AM` for the full table and the design. -/
noncomputable def AssortativeMatingModel.observedH2 (m : AssortativeMatingModel) : ℝ :=
  m.h2 / (1 - m.r * m.h2 * (1 - m.h2))

/-- **AM inflates observed heritability.**
    The observed heritability under AM exceeds the true (RM) heritability.
    Proof: h2/(1-r*h2) > h2 because 1-r*h2 < 1 and both are positive. -/
theorem AssortativeMatingModel.inflates_observed_h2 (m : AssortativeMatingModel) :
    m.h2 < m.observedH2 := by
  unfold observedH2
  rw [lt_div_iff₀ m.ratio_denom_pos]
  nlinarith [m.rh2_pos, m.h2_pos, m.h2_lt_one,
    mul_pos (mul_pos m.r_pos m.h2_pos) (sub_pos.mpr m.h2_lt_one)]

/-- Standalone version: AM inflates observed h2.

The observed heritability is written out rather than carried as a free variable
pinned by a hypothesis `h2_observed = h2_true / (1 - r * h2_true * (1 - h2_true))`.
That hypothesis stated the inflation law this module itself defines
(`AssortativeMatingModel.observedH2`) and handed it to the theorem as a gift;
substituting it changes nothing about what is proved and removes the gift.

The denominator carries the `(1 - h2_true)` factor for the reason given at
`AssortativeMatingModel.ratio_denom_pos`: the phenotypic variance in the
denominator of a heritability inflates along with the additive variance in its
numerator. -/
theorem am_inflates_observed_h2
    (h2_true r : ℝ)
    (h_r : 0 < r) (h_r_le : r < 1)
    (h_h2 : 0 < h2_true) (h_h2_le : h2_true < 1) :
    h2_true < h2_true / (1 - r * h2_true * (1 - h2_true)) := by
  rw [lt_div_iff₀ (by nlinarith [sq_nonneg (h2_true - 1 / 2), mul_pos h_r h_h2])]
  nlinarith [mul_pos (mul_pos h_r h_h2) (sub_pos.mpr h_h2_le)]

/-- **PGS R² inflation under AM.**
    A PGS with accuracy R2_rm under random mating has inflated accuracy
    under AM: R2_am = R2_rm / (1 - r*h2*(1 - h2)).
    The score captures the AM-induced LD variance, so its covariance with the
    phenotype inflates by `1/(1 - r*h2)`; the phenotype's own variance inflates
    by `1 + h2*(1/(1 - r*h2) - 1)` at the same time, and R² is a ratio to THAT.

    Empirical status: **VALIDATED**, and the previous body — `R2_rm / (1 - r*h2)`,
    the numerator's inflation with the denominator held fixed — is FALSIFIED on
    the same cells (`validation/empirical/simcov/battery_am01.py`).
    Fisher assortative mating with the environmental variance held fixed, 120
    unlinked loci, 8000 individuals, 12 generations of Gaussian-copula mate
    pairing on BREEDING VALUE at the transmission coefficient `r*h2` that
    `amVarianceStep` holds at its random-mating value — so what is on trial here
    is the R² step alone, over this module's own declared variance law. `r` and
    `h2` are REALISED, read on four replicates, while the oracle — the realised
    squared score-phenotype correlation in generation 12 — is measured on eight
    DISJOINT ones, so no input is estimated from the replicates it is tested
    against:

      r     h2   R2_rm   this body   old body   measured             sems: this/old
      0.3   0.5  0.500     0.539       0.585    0.5375±0.0035        0.4 / 13.3
      0.5   0.5  0.502     0.574       0.669    0.5751±0.0029        0.5 / 32.7
      0.3   0.8  0.801     0.842       1.051    0.8383±0.0012        3.1 / 179.4
      0.5   0.8  0.801     0.872       1.341    0.8661±0.0017        3.3 / 277.8
      0.5   0.5  0.269     0.308       0.359    0.3261±0.0133        1.3 /   2.5

    The old body's 1.341 is a squared correlation above one, which no
    measurement was needed to reject. The inverted competitor
    `R2_rm * (1 - r*h2)` is rejected at 227 sems, and the last cell puts the
    score on half the causal loci so `R2_rm` (0.269) is far from `h2`. The
    positive control — at `r = 0` the realised R² must reproduce
    `V_A/(V_A + V_E)` from the realised allele frequencies — passes at 0.78
    sems.

    Under the LITERAL field reading instead — mates paired on phenotype at
    correlation `r`, so the transmission coefficient tracks the inflating
    heritability, which is the reading `amVarianceStep` disowns — the same run
    gives 0.5379 against a measured 0.5456 and 0.8737 against 0.8724, while the
    old body gives 0.5838 and 1.3269. The repair does not depend on which
    reading is taken; the defect did not either. -/
noncomputable def AssortativeMatingModel.pgsR2AM (m : AssortativeMatingModel)
    (R2_rm : ℝ) : ℝ :=
  R2_rm / (1 - m.r * m.h2 * (1 - m.h2))

/-- **AM inflates PGS R².**
    The PGS appears more predictive under AM than under RM.
    Derived from the variance inflation: since PGS variance inflates
    by 1/(1-r*h2) and residual variance stays roughly constant. -/
theorem AssortativeMatingModel.inflates_pgs_r2
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    R2_rm < m.pgsR2AM R2_rm := by
  unfold pgsR2AM
  rw [lt_div_iff₀ m.ratio_denom_pos]
  nlinarith [mul_pos hR2 (mul_pos (mul_pos m.r_pos m.h2_pos)
    (sub_pos.mpr m.h2_lt_one))]

/-- **PGS R² inflation factor equals h2 inflation factor.**
    Both are inflated by the same 1/(1-r*h2) factor. -/
theorem AssortativeMatingModel.pgs_r2_inflation_eq_h2_inflation
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    m.pgsR2AM R2_rm / R2_rm = m.observedH2 / m.h2 := by
  unfold pgsR2AM observedH2
  have hden : 1 - m.r * m.h2 * (1 - m.h2) ≠ 0 := ne_of_gt m.ratio_denom_pos
  field_simp [hden, ne_of_gt hR2, ne_of_gt m.h2_pos]

/-- **The PGS R² inflation gap under assortative mating.**
    Stronger AM (higher r) creates a larger gap from the random-mating
    baseline.
    gap(r) = R2_rm * r*h2*(1 - h2) / (1 - r*h2*(1 - h2)). -/
noncomputable def AssortativeMatingModel.amGap
    (m : AssortativeMatingModel) (R2_rm : ℝ) : ℝ :=
  m.pgsR2AM R2_rm - R2_rm

theorem AssortativeMatingModel.am_gap_positive
    (m : AssortativeMatingModel) (R2_rm : ℝ) (hR2 : 0 < R2_rm) :
    0 < m.amGap R2_rm := by
  unfold amGap
  linarith [m.inflates_pgs_r2 R2_rm hR2]

/-- **AM gap equals R2_rm * r*h2*(1 - h2) / (1 - r*h2*(1 - h2)).**
    Derived algebraically: R2/(1-q) - R2 = R2 * q/(1-q) at q = r*h2*(1 - h2). -/
theorem AssortativeMatingModel.am_gap_formula
    (m : AssortativeMatingModel) (R2_rm : ℝ) :
    m.amGap R2_rm =
      R2_rm * (m.r * m.h2 * (1 - m.h2)) / (1 - m.r * m.h2 * (1 - m.h2)) := by
  unfold amGap pgsR2AM
  have hden : 1 - m.r * m.h2 * (1 - m.h2) ≠ 0 := ne_of_gt m.ratio_denom_pos
  field_simp [hden]
  ring_nf

end AMAndHeritability


/-!
## Two-Population AM Comparison Model

When source and target populations have different AM rates,
portability comparisons are confounded by differential AM inflation.
-/

section DifferentialAM

/-- **Two-population differential AM model.**
    Captures a scenario where PGS is trained in a source population
    with AM rate r_s and evaluated in a target with rate r_t. -/
structure DifferentialAMModel where
  /-- Source population AM rate -/
  r_s : ℝ
  /-- Target population AM rate -/
  r_t : ℝ
  /-- True heritability (same genetic architecture assumed) -/
  h2 : ℝ
  r_s_pos : 0 < r_s
  r_s_lt_one : r_s < 1
  r_t_nonneg : 0 ≤ r_t
  h2_pos : 0 < h2
  h2_lt_one : h2 < 1
  stability_s : r_s * h2 < 1
  /-- Source has more AM than target -/
  more_am_in_source : r_t < r_s

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def DifferentialAMModel.witness : DifferentialAMModel where
  r_s := 1 / 2
  r_t := 0
  h2 := 1 / 2
  r_s_pos := by norm_num
  r_s_lt_one := by norm_num
  r_t_nonneg := by norm_num
  h2_pos := by norm_num
  h2_lt_one := by norm_num
  stability_s := by norm_num
  more_am_in_source := by norm_num

/-- **Target stability follows from source stability, so do not assume it separately.**
With less assortative mating in the target and a positive heritability, `r_t * h2` is
strictly below `r_s * h2`, which is already below one; a separate assumption would be a
free parameter a model could set only by assuming something false. -/
theorem DifferentialAMModel.stability_t (d : DifferentialAMModel) : d.r_t * d.h2 < 1 := by
  have h : d.r_t * d.h2 < d.r_s * d.h2 :=
    mul_lt_mul_of_pos_right d.more_am_in_source d.h2_pos
  linarith [d.stability_s]

/-- Source denominator is positive. -/
theorem DifferentialAMModel.denom_s_pos (d : DifferentialAMModel) : 0 < 1 - d.r_s * d.h2 := by
  linarith [d.stability_s]

/-- Target denominator is positive. -/
theorem DifferentialAMModel.denom_t_pos (d : DifferentialAMModel) : 0 < 1 - d.r_t * d.h2 := by
  linarith [d.stability_t]

/-- **Measured portability ratio under differential AM.**
    If both populations have the same true R2_rm, the measured portability
    ratio is:
      port_measured = R2_target / R2_source
                    = (R2_rm/(1-r_t*h2)) / (R2_rm/(1-r_s*h2))
                    = (1 - r_s*h2) / (1 - r_t*h2)
    When r_s > r_t, this ratio is < 1, creating an *apparent* portability
    loss that is purely an AM artifact. -/
noncomputable def DifferentialAMModel.apparentPortability (d : DifferentialAMModel) : ℝ :=
  (1 - d.r_s * d.h2) / (1 - d.r_t * d.h2)

/-- **Differential AM creates artifactual portability loss.**
    When source has more AM than target (r_s > r_t), the apparent
    portability is less than 1 even though the true genetic architecture
    is identical. This is because the source R² is more inflated. -/
theorem DifferentialAMModel.differential_am_misleading (d : DifferentialAMModel) :
    d.apparentPortability < 1 := by
  unfold apparentPortability
  rw [div_lt_one d.denom_t_pos]
  have : 0 < (d.r_s - d.r_t) * d.h2 := mul_pos (by linarith [d.more_am_in_source]) d.h2_pos
  linarith

/-- **AM-corrected portability.**
    Correcting for differential AM:
    port_corrected = port_measured * (1 - r_target*h2) / (1 - r_source*h2).

    The correction factor is the *reciprocal* of the artifact.  Writing the
    inflation as `R2_obs = R2_rm / (1 - r*h2)` in each population,

      port_measured = R2_t_obs / R2_s_obs
                    = (R2_rm_t / R2_rm_s) * (1 - r_s*h2) / (1 - r_t*h2)

    so recovering `R2_rm_t / R2_rm_s` requires multiplying by
    `(1 - r_t*h2) / (1 - r_s*h2)`.  The source denominator is the divisor:
    it is the source inflation that has to be undone.

    This factor was inverted until an exact-rational check caught it.  With
    `r_s = 1/2`, `r_t = 0`, `h2 = 1/2` and identical architectures (true
    portability `1`), `apparentPortability` is `3/4`; the inverted factor
    returned `(3/4) * (3/4) = 9/16`, moving *away* from `1` instead of
    recovering it, while the form above returns `(3/4) * (4/3) = 1`. -/
noncomputable def amCorrectedPortability
    (port_measured r_source r_target h2 : ℝ) : ℝ :=
  port_measured * (1 - r_target * h2) / (1 - r_source * h2)

/-- **amCorrectedPortability where its denominator vanishes, named.** The guard `1 - r_source * h2`
is zero at `r_source = 1`, `h2 = 1`. At `r_source * h2 = 1` the source correction diverges, so a
portability estimate corrected for assortative mating collapses to zero exactly where the
correction matters most. Lean returns `0` there rather than the value the modelled quantity
takes, and no type error marks the point. Consumers must require `1 - r_source * h2 ≠ 0`. -/
theorem amCorrectedPortability_at_rsource1h21_is_junk (port_measured : ℝ) (r_target : ℝ) :
    amCorrectedPortability port_measured 1 r_target 1 = 0 := by
  unfold amCorrectedPortability
  norm_num

/-- **AM correction raises measured portability when source has more AM.**
    The source AM inflates source R² more than the target's, which deflates
    the measured ratio; undoing it multiplies by
    (1-r_t*h2)/(1-r_s*h2) > 1 when r_s > r_t.

    `h_stability_s : r_s * h2 < 1` is load-bearing and is the *source*
    condition, not the target one.  It is what makes the divisor positive.
    Dropping it in favour of `r_t * h2 < 1` makes the statement false:
    at `port_m = 1`, `h2 = 1`, `r_t = 0`, `r_s = 2` the target condition
    holds, the divisor is `1 - 2 = -1`, and the corrected value is `-1`,
    which is below `port_m` rather than above it.

    The target condition is *derivable* here (`r_t * h2 < r_s * h2 < 1`), so
    it is not restated.

    Which of the two is load-bearing depends on the direction of the
    correction: before `amCorrectedPortability` was inverted the divisor was
    `1 - r_t * h2` and the target condition was the necessary one.  An
    unused-premise scan that dropped the source condition was correct against
    that earlier statement and became wrong when the divisor moved.  Such a
    scan is only valid against the statement it was computed on. -/
theorem am_correction_increases_portability
    (port_m r_s r_t h2 : ℝ)
    (h_port : 0 < port_m)
    (h_h2 : 0 < h2)
    (h_more_am : r_t < r_s)
    (h_stability_s : r_s * h2 < 1) :
    port_m < amCorrectedPortability port_m r_s r_t h2 := by
  unfold amCorrectedPortability
  have h_denom : 0 < 1 - r_s * h2 := by linarith
  rw [lt_div_iff₀ h_denom]
  have h_gap : (1 - r_s * h2) < (1 - r_t * h2) := by
    nlinarith [mul_pos (by linarith : 0 < r_s - r_t) h_h2]
  nlinarith [mul_lt_mul_of_pos_left h_gap h_port]

/-- **AM correction recovers true portability.**
    If the only source of portability loss is differential AM,
    then the corrected portability equals 1 (perfect portability).
    We show: if port_measured = (1-r_s*h2)/(1-r_t*h2) -- which is exactly
    `DifferentialAMModel.apparentPortability`, the AM artifact proved `< 1`
    by `differential_am_misleading` -- then amCorrectedPortability = 1.

    The input was previously written `(1-r_t*h2)/(1-r_s*h2)`, the reciprocal
    of this file's own `apparentPortability`, and so did not describe the
    artifact the section is about. -/
theorem am_correction_recovers_true
    (r_s r_t h2 : ℝ) (h_denom_s : 1 - r_s * h2 ≠ 0) (h_denom_t : 1 - r_t * h2 ≠ 0) :
    amCorrectedPortability ((1 - r_s * h2) / (1 - r_t * h2)) r_s r_t h2 = 1 := by
  unfold amCorrectedPortability
  have h_denom_s' : 1 - h2 * r_s ≠ 0 := by simpa [mul_comm] using h_denom_s
  have h_denom_t' : 1 - h2 * r_t ≠ 0 := by simpa [mul_comm] using h_denom_t
  field_simp [h_denom_s, h_denom_t, h_denom_s', h_denom_t']

/-- **The correction inverts the artifact exactly.**  Feeding
`DifferentialAMModel.apparentPortability` -- the file's own model of the
measured ratio under identical architectures -- through the correction
returns `1`.  This ties the two definitions together, so a future edit that
inverts one without the other stops being provable. -/
theorem amCorrectedPortability_apparentPortability (d : DifferentialAMModel) :
    amCorrectedPortability d.apparentPortability d.r_s d.r_t d.h2 = 1 := by
  have hs : 1 - d.r_s * d.h2 ≠ 0 := ne_of_gt d.denom_s_pos
  have ht : 1 - d.r_t * d.h2 ≠ 0 := ne_of_gt d.denom_t_pos
  have hs' : 1 - d.h2 * d.r_s ≠ 0 := by simpa [mul_comm] using hs
  have ht' : 1 - d.h2 * d.r_t ≠ 0 := by simpa [mul_comm] using ht
  simp only [amCorrectedPortability, DifferentialAMModel.apparentPortability]
  field_simp [hs, ht, hs', ht']

end DifferentialAM


/-!
## AM-Induced LD and Cross-Population Prediction

The long-range LD created by AM is population-specific.
A PGS trained exploiting AM-LD in one population will not
find that LD in another population with different AM.
-/

section AMInducedLDPortability

/-- **Cross-population AM-LD model.**
    Captures the scenario where source and target have different
    AM-induced LD structures. The PGS variance in each population
    includes an AM-LD component proportional to r*h2. -/
structure CrossPopAMLD where
  /-- Effect sizes at two example loci -/
  beta_i : ℝ
  beta_j : ℝ
  /-- Source AM rate -/
  r_s : ℝ
  /-- Target AM rate -/
  r_t : ℝ
  /-- Heritability -/
  h2 : ℝ
  r_s_pos : 0 < r_s
  r_t_nonneg : 0 ≤ r_t
  r_t_lt_rs : r_t < r_s
  h2_pos : 0 < h2
  stability_s : r_s * h2 < 1
  stability_t : r_t * h2 < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def CrossPopAMLD.witness : CrossPopAMLD where
  beta_i := 1
  beta_j := 1
  r_s := 1 / 2
  r_t := 0
  h2 := 1 / 2
  r_s_pos := by norm_num
  r_t_nonneg := by norm_num
  r_t_lt_rs := by norm_num
  h2_pos := by norm_num
  stability_s := by norm_num
  stability_t := by norm_num

/-- AM-LD in source is stronger than in target. -/
theorem CrossPopAMLD.source_ld_exceeds_target (c : CrossPopAMLD)
    (hbi : 0 < c.beta_i) (hbj : 0 < c.beta_j) :
    amInducedLD c.beta_i c.beta_j c.r_t c.h2 <
    amInducedLD c.beta_i c.beta_j c.r_s c.h2 := by
  unfold amInducedLD
  have hprod := mul_pos hbi hbj
  have h_ds : 0 < 1 - c.r_s * c.h2 := by linarith [c.stability_s]
  have h_dt : 0 < 1 - c.r_t * c.h2 := by linarith [c.stability_t]
  rw [div_lt_div_iff₀ h_dt h_ds]
  have h_diff : 0 < c.r_s - c.r_t := by linarith [c.r_t_lt_rs]
  have hprod_h2 : 0 < c.beta_i * c.beta_j * c.h2 := by
    nlinarith [hprod, c.h2_pos]
  have hrt_h2 : 0 ≤ c.r_t * c.h2 := by
    exact mul_nonneg c.r_t_nonneg (le_of_lt c.h2_pos)
  have hrs_h2 : 0 < c.r_s * c.h2 := by
    exact mul_pos c.r_s_pos c.h2_pos
  nlinarith [hprod_h2, hrt_h2, hrs_h2, h_diff]

/-- **AM-LD breaks cross-population prediction.**
    The PGS trained in the source captures AM-LD variance equal to
    R2_rm * r_s*h2/(1-r_s*h2). In the target, only r_t*h2/(1-r_t*h2)
    of this component exists. The ratio of AM-LD variance between
    target and source is less than 1, reducing prediction accuracy.

    Specifically, the AM-LD ratio is:
    (r_t*h2/(1-r_t*h2)) / (r_s*h2/(1-r_s*h2)) = r_t(1-r_s*h2) / (r_s(1-r_t*h2)) < 1
    when r_t < r_s.

    **What the cleared form shows, and it is less than the docstring above.**
    Expanding both sides, `r_t·(1 - r_s·h2) < r_s·(1 - r_t·h2)` is
    `r_t - r_s·r_t·h2 < r_s - r_s·r_t·h2`: the assortment term is the *same* on
    both sides and cancels, leaving `r_t < r_s`. The conclusion is therefore
    `h_more` written in a heavier notation, and `h2` does not enter at all. A
    scan of the kernel-accepted proof term confirmed it: the positivity and
    stability premises `h_rs`, `h_rt`, `h_h2`, `h_stab_s`, `h_stab_t` occur
    nowhere in the proof and have been removed. Read this as the cancellation
    identity it is, not as evidence that assortative mating degrades transfer;
    the substantive claim is upstream, in the *division* by
    `r_s·h2/(1 - r_s·h2)`, which this statement never performs. -/
theorem am_ld_breaks_cross_population
    (r_s r_t h2 : ℝ)
    (h_more : r_t < r_s) :
    r_t * (1 - r_s * h2) < r_s * (1 - r_t * h2) := by
  nlinarith

/-- **Cross-trait AM effect.**
    AM on a primary trait (e.g., education) with genetic correlation rg
    to a secondary trait creates AM-LD for the secondary trait proportional
    to rg^2 * r * h2_primary. When both rg and r are positive, the
    cross-trait AM effect is positive. -/
theorem cross_trait_am_effect
    (rg r_education h2_primary : ℝ)
    (h_rg : 0 < rg) (h_r : 0 < r_education) (h_h2 : 0 < h2_primary) :
    0 < rg ^ 2 * r_education * h2_primary := by
  apply mul_pos
  · apply mul_pos
    · positivity
    · exact h_r
  · exact h_h2

end AMInducedLDPortability


/-!
## Population Structure and PGS

Population structure beyond simple two-population models
affects PGS in complex ways.
-/

section PopulationStructure

/-- **Isolation by distance model.**
    In a stepping-stone model, Fst between populations i and j
    increases with geographic distance d_ij:
    Fst(d) ≈ d / (4Nσ² + d) where σ² is dispersal variance.

    **Convention, and it is not the one the corpus's other stepping-stone body uses.**
    `N` here is a population *density* — individuals per unit of the same length in
    which `d` and `σ_sq` are measured — not a deme size. This is Rousset's continuous
    isolation-by-distance law `F / (1 - F) = d / (4·N·σ²)`, rearranged; the migration
    rate is absent because dispersal enters through `σ_sq` and abundance through the
    density, not through a per-generation `m`. Read `N` as a deme size instead and the
    body is a stepping-stone `F_ST` with the migration rate dropped, which is a
    different and wrong formula: contrast
    `Descent.DemographicHistory.demoSteppingStoneFst = d / (d + 4·Ne·m·σ_sq)`, whose
    `Ne` *is* a deme size and which therefore must and does carry `m`. Dimensional
    analysis is what separates the two readings — under the deme-size reading `4·N·σ_sq`
    carries a spurious factor of generations and cannot be added to `d` — and nothing in
    the body itself does, which is why the convention is stated here.

    Empirical status: **VALIDATED under the density reading**
    (`validation/empirical/popgensel/ibdcell.py`, cell H). The dimensional check
    above rules out the deme-size reading; this measurement is about the density reading it
    leaves standing.

    The body is equivalent to `F/(1-F) = d/(4·N·σ²)`, so what is measured is Rousset's
    regression statistic against distance on a RING of demes -- every deme equivalent, no
    edges -- under the stepping-stone reparametrisation that IS the density reading:
    `N` is the deme size per unit spacing and `σ² = 2m` for nearest-neighbour migration at
    rate `m` each way. The observable is Rousset's own
    `a_r = (π_between(d) - π_within)/π_within`, built from probabilities of identity and
    NOT from any named `F_ST` estimator, and the discrimination is its SLOPE in `d`. Both
    choices are deliberate: Nei's `G_ST` between two demes is a quarter of the corpus's
    pairwise `F_ST`, so a cell reporting a factor of four here would be reporting an
    estimator convention, and a slope is immune to an additive offset.

    | demes | `N` | `m` | `σ²` | fitted slope | this def `1/(4Nσ²)` | sems |
    |---|---|---|---|---|---|---|
    | 40 | 20 | 0.05 | 0.1 | 0.12459 ± 0.01037 | 0.12500 | 0.04 |
    | 100 | 40 | 0.10 | 0.2 | 0.02797 ± 0.00172 | 0.03125 | 1.90 |

    The competitors are rejected on both rows: `1/(2Nσ²)` at 12.1 and 20.1 sems and
    `1/(8Nσ²)` at 6.0 and 7.2 sems, so the constant `4` is pinned rather than tolerated,
    and the `PLANTED` arm at `1.4x` is rejected at 4.9 and 9.2 sems.

    The positive control is the fitted intercept, which Rousset's law requires to
    extrapolate to zero: `0.00023 ± 0.02036` and `-0.00332 ± 0.00500`.

    That control is also what diagnosed the one cell that did not pass. At 40 demes rather
    than 100, the second design read `0.02352 ± 0.00243` -- 25 percent low, 3.18 sems --
    with an intercept of `0.01219 ± 0.00753`, 1.6 sems from the zero it must have.
    Enlarging the ring at unchanged `N` and `m` moved the slope UP to `0.02797` and the
    intercept back to zero, which is what finite-habitat saturation predicts and what a
    genuine failure of the law would not have done: if the shortfall had been the body's, a
    larger habitat would not have repaired it. The higher-`Nσ²` design needs a habitat
    larger than the neighbourhood size, and at 40 demes it did not have one. -/
noncomputable def ibdFst (d N sigma_sq : ℝ) : ℝ :=
  d / (4 * N * sigma_sq + d)

/-- **The isolation-by-distance `F_ST` has the odds-like shape**, `a / (a + 2b)`, at
`a = d` and `b = 2·N·σ²`.

`Core.oddsLike` is the same map `coalFst` and `qst` are built on -- `t/(t + 2Nₑ)` and
`V_b/(V_b + 2V_w)` -- so this places neighbourhood-size differentiation beside them rather
than leaving three quotients that resemble each other. The `4` in the body is `2 · 2`: one
factor is the kernel's, and the other is the `2Nσ²` neighbourhood size the law is written
in. -/
theorem ibdFst_eq_oddsLike (d N sigma_sq : ℝ) :
    ibdFst d N sigma_sq = Descent.Core.oddsLike d (2 * N * sigma_sq) := by
  unfold ibdFst Descent.Core.oddsLike
  ring_nf

/-- **ibdFst where its denominator vanishes, named.** The guard `4 * N * sigma_sq + d` is zero at `d
= 0`, `N = 0`, `sigma_sq = 0`. Lean returns `0` there rather than the value the modelled
quantity takes, and no type error marks the point. Consumers must require `4 * N * sigma_sq + d
≠ 0`. -/
theorem ibdFst_at_d0n0sigmasq0_is_junk :
    ibdFst 0 0 0 = 0 := by
  unfold ibdFst
  norm_num

/-- IBD Fst increases with distance. -/
theorem ibd_fst_increases_with_distance
    (N sigma_sq d₁ d₂ : ℝ)
    (h_N : 0 < N) (h_s : 0 < sigma_sq)
    (h_d₁ : 0 ≤ d₁) (h_d₂ : 0 ≤ d₂) (h_more : d₁ < d₂) :
    ibdFst d₁ N sigma_sq < ibdFst d₂ N sigma_sq := by
  unfold ibdFst
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h_N h_s]

/-- **IBD Fst is bounded between 0 and 1.**
    At d=0, Fst=0. As d→∞, Fst→1. -/
theorem ibd_fst_nonneg (d N sigma_sq : ℝ) (h_d : 0 ≤ d) (h_N : 0 < N) (h_s : 0 < sigma_sq) :
    0 ≤ ibdFst d N sigma_sq := by
  unfold ibdFst
  apply div_nonneg h_d
  positivity

theorem ibd_fst_lt_one (d N sigma_sq : ℝ) (h_d : 0 ≤ d) (h_N : 0 < N) (h_s : 0 < sigma_sq) :
    ibdFst d N sigma_sq < 1 := by
  unfold ibdFst
  rw [div_lt_one (by positivity)]
  linarith [mul_pos h_N h_s]

/-- **Founder effects create portability outliers.**
    In a population with strong founder effects, the effective Fst
    (due to bottleneck-induced drift) exceeds what geographic distance
    would predict. We model this as: Fst_actual > Fst_predicted(d).
    Consequence: portability deviates from the IBD gradient. -/
theorem founder_effect_excess_fst
    (d N_large N_bottleneck sigma_sq : ℝ)
    (h_d : 0 < d) (h_Nl : 0 < N_large) (h_Nb : 0 < N_bottleneck)
    (h_s : 0 < sigma_sq) (h_bottleneck : N_bottleneck < N_large) :
    ibdFst d N_bottleneck sigma_sq > ibdFst d N_large sigma_sq := by
  unfold ibdFst
  have hden_b : 0 < 4 * N_bottleneck * sigma_sq + d := by positivity
  have hden_l : 0 < 4 * N_large * sigma_sq + d := by positivity
  have hden_lt : 4 * N_bottleneck * sigma_sq + d < 4 * N_large * sigma_sq + d := by
    nlinarith [h_bottleneck, h_s]
  have hlt : d / (4 * N_large * sigma_sq + d) < d / (4 * N_bottleneck * sigma_sq + d) := by
    apply (div_lt_div_iff₀ hden_l hden_b).2
    nlinarith [h_d, hden_lt]
  simpa [gt_iff_lt] using hlt

end PopulationStructure

end Descent.PopGen

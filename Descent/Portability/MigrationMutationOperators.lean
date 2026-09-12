/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DriftOperatorCoordinates

assert_below Descent.Decision Descent.Program

/-!
# The migration and mutation operators of NOTE1 equations (8) and (9)

NOTE1 writes the generator of the low-order LD family deme by deme in the coordinates `p_i`,
`q_i`, `D_i`: the drift (7) at coalescence rate `c_i`, the migration (8) and the mutation (9).
`Descent.Portability.DriftOperatorCoordinates` states (7) literally on `CoordinatePolynomial`.
This module states (8) and (9) in the same literal form, with Mathlib's partial derivatives.

## Mutation, equation (9)

Mutation acts within one deme, so its operator lives on the coordinates of that deme, the ring
`CoordinatePolynomial` of the drift operator. `mutationOperator θ` is
`θ [(½ - p) ∂_p f + (½ - q) ∂_q f - 2 D ∂_D f]`. It is additive, commutes with constant
multiples, annihilates constants, and obeys the Leibniz rule of a first-order operator
(`mutationOperator_mul`). On the coordinates it gives the displayed coefficients `θ (½ - p)`,
`θ (½ - q)` and `-2 θ D` (`mutationOperator_X_zero`, `mutationOperator_X_one`,
`mutationOperator_X_two`). The linkage product then decays at rate `4 θ`
(`mutationOperator_linkage_sq`).

## Migration, equation (8)

Migration from a source deme `j` into a recipient deme `i` couples two demes, so its operator
lives on `DemeCoordinatePolynomial D`, the polynomials in the coordinates `p_k`, `q_k`, `D_k` of
all `D` demes. `migrationOperator m i j` is

`m [(p_j - p_i) ∂_{p_i} f + (q_j - q_i) ∂_{q_i} f`
`   + {D_j - D_i + (p_j - p_i)(q_j - q_i)} ∂_{D_i} f]`.

It obeys the same algebra (`migrationOperator_mul`), is null when the source is the recipient
(`migrationOperator_self`), and leaves every coordinate of another deme unchanged
(`migrationOperator_X_of_ne`). On the recipient's coordinates it gives the displayed coefficients
`m (p_j - p_i)`, `m (q_j - q_i)` and `m {D_j - D_i + (p_j - p_i)(q_j - q_i)}`
(`migrationOperator_X_left`, `migrationOperator_X_right`, `migrationOperator_X_linkage`).

Scope. The operators are stated on polynomials. They are not tied to the corpus rows
`lowOrderLDMigration`, `lowOrderLDMutationCoupling` and `lowOrderLDRecurrentMutationDamping` in
the way `lowOrderLDDrift_eq_driftOperator` ties (7) to the drift rows. The recombination term
`-ρ D ∂_D f / 2`, and the many-deme generator that sums (7), (8) and (9), are not assembled here.

## Empirical status

None. The bodies here are algebra: first-order partial differential operators on polynomials,
so no measurement can bear on them.
-/

namespace Descent.Portability.MigrationMutationOperators

open MvPolynomial
open Descent.Portability.DriftOperatorCoordinates

noncomputable section

/-! ## Mutation, equation (9) -/

/-- The partial derivatives of the coordinates of one deme: `∂_i X_j` is `1` when `j = i` and `0`
otherwise. -/
theorem pderiv_X_coordinate (i j : Fin 3) :
    pderiv i (X j : CoordinatePolynomial) = if j = i then 1 else 0 := by
  rw [pderiv_X, Pi.single_apply]

/-- **The mutation operator of NOTE1 equation (9)** at mutation parameter `θ`, on polynomials in
`p`, `q`, `D`. -/
def mutationOperator (θ : ℝ) (f : CoordinatePolynomial) : CoordinatePolynomial :=
  C θ * ((C (1 / 2) - X 0) * pderiv 0 f + (C (1 / 2) - X 1) * pderiv 1 f -
    2 * X 2 * pderiv 2 f)

/-- The mutation operator is additive. -/
theorem mutationOperator_add (θ : ℝ) (f g : CoordinatePolynomial) :
    mutationOperator θ (f + g) = mutationOperator θ f + mutationOperator θ g := by
  simp only [mutationOperator, map_add]
  ring

/-- The mutation operator commutes with constant multiples. -/
theorem mutationOperator_C_mul (θ level : ℝ) (f : CoordinatePolynomial) :
    mutationOperator θ (C level * f) = C level * mutationOperator θ f := by
  simp only [mutationOperator, pderiv_C_mul]
  ring

/-- The mutation operator annihilates constants. -/
theorem mutationOperator_C (θ level : ℝ) : mutationOperator θ (C level) = 0 := by
  simp only [mutationOperator, pderiv_C]
  ring

/-- **The Leibniz rule of equation (9)**: mutation is a first-order operator. -/
theorem mutationOperator_mul (θ : ℝ) (f g : CoordinatePolynomial) :
    mutationOperator θ (f * g) = f * mutationOperator θ g + g * mutationOperator θ f := by
  simp only [mutationOperator, Derivation.leibniz, smul_eq_mul]
  ring

/-- **Mutation pulls the left allele frequency toward `½`**: `L p = θ (½ - p)`. -/
theorem mutationOperator_X_zero (θ : ℝ) :
    mutationOperator θ (X 0) = C θ * (C (1 / 2) - X 0) := by
  simp +decide only [mutationOperator, pderiv_X_coordinate, ↓reduceIte]
  ring

/-- Mutation pulls the right allele frequency toward `½`: `L q = θ (½ - q)`. -/
theorem mutationOperator_X_one (θ : ℝ) :
    mutationOperator θ (X 1) = C θ * (C (1 / 2) - X 1) := by
  simp +decide only [mutationOperator, pderiv_X_coordinate, ↓reduceIte]
  ring

/-- **Mutation decays linkage at rate `2 θ`**: `L D = -2 θ D`. -/
theorem mutationOperator_X_two (θ : ℝ) : mutationOperator θ (X 2) = C θ * (-2 * X 2) := by
  simp +decide only [mutationOperator, pderiv_X_coordinate, ↓reduceIte]
  ring

/-- The linkage product decays at rate `4 θ`: `L D² = -4 θ D²`. -/
theorem mutationOperator_linkage_sq (θ : ℝ) :
    mutationOperator θ (X 2 ^ 2) = C θ * (-4 * X 2 ^ 2) := by
  rw [sq, mutationOperator_mul, mutationOperator_X_two]
  ring

/-! ## Migration, equation (8) -/

/-- Polynomials in the coordinates of all `D` demes: variable `(k, 0)` is the left allele
frequency `p_k`, `(k, 1)` the right allele frequency `q_k`, and `(k, 2)` the linkage determinant
`D_k`. -/
abbrev DemeCoordinatePolynomial (D : ℕ) := MvPolynomial (Fin D × Fin 3) ℝ

/-- The partial derivatives of the coordinates of all demes. -/
theorem pderiv_X_deme {D : ℕ} (a b : Fin D × Fin 3) :
    pderiv a (X b : DemeCoordinatePolynomial D) = if b = a then 1 else 0 := by
  rw [pderiv_X, Pi.single_apply]

/-- **The migration operator of NOTE1 equation (8)**, at rate `m` from the source deme `j` into
the recipient deme `i`. -/
def migrationOperator {D : ℕ} (m : ℝ) (i j : Fin D) (f : DemeCoordinatePolynomial D) :
    DemeCoordinatePolynomial D :=
  C m * ((X (j, 0) - X (i, 0)) * pderiv (i, 0) f + (X (j, 1) - X (i, 1)) * pderiv (i, 1) f +
    (X (j, 2) - X (i, 2) + (X (j, 0) - X (i, 0)) * (X (j, 1) - X (i, 1))) * pderiv (i, 2) f)

/-- The migration operator is additive. -/
theorem migrationOperator_add {D : ℕ} (m : ℝ) (i j : Fin D) (f g : DemeCoordinatePolynomial D) :
    migrationOperator m i j (f + g) = migrationOperator m i j f + migrationOperator m i j g := by
  simp only [migrationOperator, map_add]
  ring

/-- The migration operator commutes with constant multiples. -/
theorem migrationOperator_C_mul {D : ℕ} (m level : ℝ) (i j : Fin D)
    (f : DemeCoordinatePolynomial D) :
    migrationOperator m i j (C level * f) = C level * migrationOperator m i j f := by
  simp only [migrationOperator, pderiv_C_mul]
  ring

/-- The migration operator annihilates constants. -/
theorem migrationOperator_C {D : ℕ} (m level : ℝ) (i j : Fin D) :
    migrationOperator m i j (C level) = 0 := by
  simp only [migrationOperator, pderiv_C]
  ring

/-- **The Leibniz rule of equation (8)**: migration is a first-order operator. -/
theorem migrationOperator_mul {D : ℕ} (m : ℝ) (i j : Fin D) (f g : DemeCoordinatePolynomial D) :
    migrationOperator m i j (f * g) =
      f * migrationOperator m i j g + g * migrationOperator m i j f := by
  simp only [migrationOperator, Derivation.leibniz, smul_eq_mul]
  ring

/-- Migration from a deme into itself is null. -/
theorem migrationOperator_self {D : ℕ} (m : ℝ) (i : Fin D) (f : DemeCoordinatePolynomial D) :
    migrationOperator m i i f = 0 := by
  simp [migrationOperator]

/-- **Migration moves the recipient's left allele frequency toward the source's**:
`L p_i = m (p_j - p_i)`. -/
theorem migrationOperator_X_left {D : ℕ} (m : ℝ) (i j : Fin D) :
    migrationOperator m i j (X (i, 0)) = C m * (X (j, 0) - X (i, 0)) := by
  simp +decide only [migrationOperator, pderiv_X_deme, Prod.mk.injEq, eq_self_iff_true,
    true_and, ↓reduceIte]
  ring

/-- Migration moves the recipient's right allele frequency toward the source's:
`L q_i = m (q_j - q_i)`. -/
theorem migrationOperator_X_right {D : ℕ} (m : ℝ) (i j : Fin D) :
    migrationOperator m i j (X (i, 1)) = C m * (X (j, 1) - X (i, 1)) := by
  simp +decide only [migrationOperator, pderiv_X_deme, Prod.mk.injEq, eq_self_iff_true,
    true_and, ↓reduceIte]
  ring

/-- **Migration mixes linkage and creates it from frequency differences**:
`L D_i = m {D_j - D_i + (p_j - p_i)(q_j - q_i)}`. -/
theorem migrationOperator_X_linkage {D : ℕ} (m : ℝ) (i j : Fin D) :
    migrationOperator m i j (X (i, 2)) =
      C m * (X (j, 2) - X (i, 2) + (X (j, 0) - X (i, 0)) * (X (j, 1) - X (i, 1))) := by
  simp +decide only [migrationOperator, pderiv_X_deme, Prod.mk.injEq, eq_self_iff_true,
    true_and, ↓reduceIte]
  ring

/-- Migration into deme `i` leaves every coordinate of another deme unchanged. -/
theorem migrationOperator_X_of_ne {D : ℕ} (m : ℝ) {i k : Fin D} (hk : k ≠ i) (j : Fin D)
    (l : Fin 3) : migrationOperator m i j (X (k, l)) = 0 := by
  simp only [migrationOperator, pderiv_X_deme, Prod.mk.injEq, hk, false_and, ↓reduceIte]
  ring

end

end Descent.Portability.MigrationMutationOperators

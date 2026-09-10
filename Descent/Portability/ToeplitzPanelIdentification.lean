/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GaussianPanelLaw
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Dist

assert_below Descent.Decision Descent.Program

/-!
Distinct nonzero lag values in a scalar Toeplitz covariance are labeled by
their exact off-diagonal multiplicities. Coordinate permutation preserves these
multiplicities, so the unordered Gaussian panel law identifies every lag value.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ToeplitzPanelIdentification

open MeasureTheory ProbabilityTheory GaussianCovarianceSeparation GaussianPanelLaw

def lag {d : ℕ} (i j : Fin d) : Fin d :=
  ⟨Nat.dist i.val j.val, by have hi := i.isLt; have hj := j.isLt; simp [Nat.dist]; omega⟩

@[simp] theorem lag_self {d : ℕ} [NeZero d] (i : Fin d) : lag i i = 0 := by
  apply Fin.ext
  simp [lag]

@[simp] theorem lag_zero {d : ℕ} [NeZero d] (i : Fin d) : lag 0 i = i := by
  apply Fin.ext
  simp [lag]

theorem lag_pos_iff {d : ℕ} (i j : Fin d) : 0 < (lag i j).val ↔ i ≠ j := by
  simp only [lag, Nat.dist]
  constructor
  · intro h he
    subst j
    omega
  · intro h
    have hn : i.val ≠ j.val := fun he ↦ h (Fin.ext he)
    omega

def toeplitz {d : ℕ} (r : Fin d → ℝ) : SymmetricCovariance (Fin d) :=
  ⟨fun i j ↦ r (lag i j), by intro i j; congr 1; apply Fin.ext; exact Nat.dist_comm _ _⟩

noncomputable def offMultiplicity {D : Type*} [Fintype D] (A : Matrix D D ℝ)
    (value : ℝ) : ℕ := by
  classical
  exact Fintype.card {ij : D × D // ij.1 ≠ ij.2 ∧ A ij.1 ij.2 = value}

theorem offMultiplicity_permute {D : Type*} [Fintype D]
    (A : SymmetricCovariance D) (π : Equiv.Perm D) (value : ℝ) :
    offMultiplicity (permuteCovariance A π).val value = offMultiplicity A.val value := by
  classical
  apply Fintype.card_congr
  exact (Equiv.prodCongr π π).subtypeEquiv (fun ij ↦ by simp [permuteCovariance])

def upperEquiv (d k : ℕ) :
    {ij : Fin d × Fin d // ij.1.val + k = ij.2.val} ≃ Fin (d - k) where
  toFun ij := ⟨ij.val.1.val, by have h := ij.property; have hj := ij.val.2.isLt; omega⟩
  invFun i := ⟨(⟨i.val, by have hi := i.isLt; omega⟩,
    ⟨i.val + k, by have hi := i.isLt; omega⟩), rfl⟩
  left_inv ij := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      exact ij.property
  right_inv i := by rfl

theorem upper_card (d k : ℕ) :
    Fintype.card {ij : Fin d × Fin d // ij.1.val + k = ij.2.val} = d - k := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (upperEquiv d k)

theorem lower_card (d k : ℕ) :
    Fintype.card {ij : Fin d × Fin d // ij.2.val + k = ij.1.val} = d - k := by
  rw [← upper_card d k]
  exact Fintype.card_congr ((Equiv.prodComm (Fin d) (Fin d)).subtypeEquiv (fun _ ↦ Iff.rfl))

theorem lag_card (d k : ℕ) (hk : 0 < k) :
    Fintype.card {ij : Fin d × Fin d // Nat.dist ij.1.val ij.2.val = k} = 2 * (d - k) := by
  let p := fun ij : Fin d × Fin d ↦ ij.1.val + k = ij.2.val
  let q := fun ij : Fin d × Fin d ↦ ij.2.val + k = ij.1.val
  have he : (fun ij : Fin d × Fin d ↦ Nat.dist ij.1.val ij.2.val = k) =
      fun ij ↦ p ij ∨ q ij := by
    funext ij
    apply propext
    simp only [p, q, Nat.dist]
    omega
  rw [he, Fintype.card_subtype_or_disjoint]
  · change Fintype.card {ij : Fin d × Fin d // ij.1.val + k = ij.2.val} +
        Fintype.card {ij : Fin d × Fin d // ij.2.val + k = ij.1.val} = _
    rw [upper_card, lower_card]
    omega
  · rw [disjoint_iff]
    intro ij h
    change (p ij ∧ q ij) → False at h ⊢
    intro hh
    dsimp [p, q] at hh
    omega

theorem toeplitz_multiplicity {d : ℕ} (r : Fin d → ℝ)
    (hr : Set.InjOn r {k | 0 < k.val}) (k : Fin d) (hk : 0 < k.val) :
    offMultiplicity (toeplitz r).val (r k) = 2 * (d - k.val) := by
  classical
  unfold offMultiplicity
  have he : (fun ij : Fin d × Fin d ↦ ij.1 ≠ ij.2 ∧ (toeplitz r).val ij.1 ij.2 = r k) =
      fun ij ↦ Nat.dist ij.1.val ij.2.val = k.val := by
    funext ij
    apply propext
    constructor
    · rintro ⟨hne, hv⟩
      exact congrArg Fin.val (hr ((lag_pos_iff _ _).mpr hne) hk hv)
    · intro h
      have hl : lag ij.1 ij.2 = k := Fin.ext h
      exact ⟨(lag_pos_iff _ _).mp (by rw [hl]; exact hk), congrArg r hl⟩
  rw [he]
  exact lag_card d k.val hk

/-- Distinct off-diagonal lag values force a Toeplitz covariance orbit to
contain only one Toeplitz covariance with distinct off-diagonal lag values. -/
theorem orbit_identifies_lags {d : ℕ} [NeZero d] (r t : Fin d → ℝ)
    (hr : Set.InjOn r {k | 0 < k.val}) (ht : Set.InjOn t {k | 0 < k.val})
    (π : Equiv.Perm (Fin d)) (hπ : permuteCovariance (toeplitz r) π = toeplitz t) : r = t := by
  have he (i j : Fin d) : r (lag (π i) (π j)) = t (lag i j) :=
    congrFun (congrFun (congrArg Subtype.val hπ) i) j
  funext k
  by_cases hk : k.val = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst k
    simpa only [lag_self] using he 0 0
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    let i := π.symm 0
    let j := π.symm k
    let l := lag i j
    have hlpos : 0 < l.val := by
      apply (lag_pos_iff i j).mpr
      intro hij
      have hh := congrArg π hij
      have hz : (0 : Fin d) = k := by simpa [i, j] using hh
      exact hk (congrArg Fin.val hz.symm)
    have hval : r k = t l := by simpa [i, j, l] using he i j
    have hcount := offMultiplicity_permute (toeplitz r) π (r k)
    rw [hπ, toeplitz_multiplicity r hr k hkpos, hval,
      toeplitz_multiplicity t ht l hlpos] at hcount
    have hlk : l = k := by
      apply Fin.ext
      have hl := l.isLt
      have hk' := k.isLt
      omega
    simpa only [hlk] using hval

theorem bag_law_identifies_lags {d : ℕ} [NeZero d]
    (μ ν : Measure (Fin d → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hμ : Centered μ) (hν : Centered ν) (r t : Fin d → ℝ)
    (hr : Set.InjOn r {k | 0 < k.val}) (ht : Set.InjOn t {k | 0 < k.val})
    (hcμ : covariance μ = toeplitz r) (hcν : covariance ν = toeplitz t)
    (hbag : μ.map bag = ν.map bag) : r = t := by
  obtain ⟨π, hπ⟩ := bag_law_identifies_covariance_orbit μ ν hμ hν hbag
  rw [hcμ, hcν] at hπ
  exact orbit_identifies_lags r t hr ht π hπ

end Descent.Portability.ToeplitzPanelIdentification

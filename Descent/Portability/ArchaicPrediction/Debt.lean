/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Cube
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
# Additive transport debt and rare-source amplification

Theorem 2 uses explicit finite Bernoulli expectations. The target intercept is
already correct: the remaining debt is caused by stale additive slopes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators
open Filter Topology
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sum_singleton_subsets (f : Finset I → ℝ) :
    (∑ S : Finset I, if S.card = 1 then f S else 0) = ∑ i, f {i} := by
  have he : Finset.univ.filter (fun S : Finset I => S.card = 1) =
      (Finset.univ : Finset I).powersetCard 1 := by ext; simp
  rw [← Finset.sum_filter, he, Finset.powersetCard_one, Finset.sum_map]
  rfl

lemma sum_by_interaction_order (f : Finset I → ℝ) :
    ∑ S, f S = f ∅ + (∑ i, f {i}) + ∑ S, if 2 ≤ S.card then f S else 0 := by
  have hs (S : Finset I) : f S =
      (if S = ∅ then f S else 0) + (if S.card = 1 then f S else 0) +
        (if 2 ≤ S.card then f S else 0) := by
    by_cases h₀ : S = ∅
    · simp [h₀]
    · have hp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h₀)
      by_cases h₁ : S.card = 1
      · simp [h₀, h₁]
      · simp [h₀, h₁, show 2 ≤ S.card by omega]
  conv_lhs => arg 2; intro S; rw [hs S]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_singleton_subsets]
  simp

noncomputable def additiveResponse (p b : I → ℝ) (x : I → Bool) : ℝ :=
  ∑ i, b i * centeredCharacter p {i} x

noncomputable def interactionResponse (p : I → ℝ) (a : Finset I → ℝ) (x : I → Bool) : ℝ :=
  ∑ S, (if 2 ≤ S.card then a S else 0) * centeredCharacter p S x

theorem additive_squared_norm (p b : I → ℝ) :
    cubeMean p (fun x => additiveResponse p b x ^ 2) = ∑ i, b i ^ 2 * (p i * (1 - p i)) := by
  simp_rw [additiveResponse, pow_two, Finset.sum_mul, Finset.mul_sum, cubeMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [show ∀ j x, b i * centeredCharacter p {i} x * (b j * centeredCharacter p {j} x) =
    (b i * b j) * (centeredCharacter p {i} x * centeredCharacter p {j} x) by intros; ring]
  simp_rw [cubeMean_smul, centered_orthogonality]
  simp

theorem interaction_squared_norm (p : I → ℝ) (a : Finset I → ℝ) :
    cubeMean p (fun x => interactionResponse p a x ^ 2) =
      ∑ S, if 2 ≤ S.card then a S ^ 2 * ∏ i ∈ S, p i * (1 - p i) else 0 := by
  change cubeMean p (fun x => (∑ S, (if 2 ≤ S.card then a S else 0) * centeredCharacter p S x) ^ 2) = _
  rw [centered_parseval]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

theorem interaction_additive_orthogonal (p b : I → ℝ) (a : Finset I → ℝ) :
    cubeMean p (fun x => interactionResponse p a x * additiveResponse p b x) = 0 := by
  simp_rw [interactionResponse, additiveResponse, Finset.sum_mul, Finset.mul_sum, cubeMean_sum]
  apply Finset.sum_eq_zero
  intro S _
  apply Finset.sum_eq_zero
  intro i _
  have he (x : I → Bool) :
      ((if 2 ≤ S.card then a S else 0) * centeredCharacter p S x) *
        (b i * centeredCharacter p {i} x) =
      ((if 2 ≤ S.card then a S else 0) * b i) *
        (centeredCharacter p S x * centeredCharacter p {i} x) := by ring
  simp_rw [he, cubeMean_smul, centered_orthogonality]
  by_cases h : S = {i}
  · simp [h]
  · simp [h]

/-- Theorem 2: residual interaction variance plus the exact stale-slope debt. -/
theorem exact_transport_debt (p source target : I → ℝ) (a : Finset I → ℝ) :
    cubeMean p (fun x => (interactionResponse p a x +
      additiveResponse p target x - additiveResponse p source x) ^ 2) =
      (∑ S, if 2 ≤ S.card then a S ^ 2 * ∏ i ∈ S, p i * (1 - p i) else 0) +
      ∑ i, (p i * (1 - p i)) * (target i - source i) ^ 2 := by
  have hd (x : I → Bool) : additiveResponse p target x - additiveResponse p source x =
      additiveResponse p (target - source) x := by
    simp [additiveResponse, ← Finset.sum_sub_distrib, sub_mul]
  have hex (x : I → Bool) :
      (interactionResponse p a x + additiveResponse p target x - additiveResponse p source x) ^ 2 =
      interactionResponse p a x ^ 2 + additiveResponse p (target - source) x ^ 2 +
        2 * (interactionResponse p a x * additiveResponse p (target - source) x) := by
    rw [add_sub_assoc, hd]
    ring
  simp_rw [hex, cubeMean_add, cubeMean_smul, interaction_additive_orthogonal,
    interaction_squared_norm, additive_squared_norm]
  simp [mul_comm]

/-- The total response decomposes into its mean, best additive part, and interactions. -/
theorem centered_response_split (p : I → ℝ) (a : Finset I → ℝ) (x : I → Bool) :
    (∑ S, a S * centeredCharacter p S x) =
      a ∅ + additiveResponse p (fun i => a {i}) x + interactionResponse p a x := by
  rw [sum_by_interaction_order]
  simp [centeredCharacter, additiveResponse, interactionResponse, ite_mul]

noncomputable def rareSourceVariance (γ ε : ℝ) : ℝ := γ ^ 2 * ε ^ 2 * (1 - ε) ^ 2
noncomputable def rareTransportDebt (γ ε : ℝ) : ℝ := γ ^ 2 / 2 * (1 / 2 - ε) ^ 2

/-- The exact centered expansion of the stable two-locus interaction. -/
theorem pair_interaction_centering (γ p₀ p₁ x₀ x₁ : ℝ) :
    γ * x₀ * x₁ = γ * p₀ * p₁ + γ * p₁ * (x₀ - p₀) +
      γ * p₀ * (x₁ - p₁) + γ * (x₀ - p₀) * (x₁ - p₁) := by ring

/-- The vanishing source quantity is an actual finite-population interaction MSE. -/
theorem rare_source_variance_realized (γ ε : ℝ) :
    cubeMean (fun _ : Fin 2 => ε) (fun x =>
      (γ * centeredCharacter (fun _ => ε) Finset.univ x) ^ 2) = rareSourceVariance γ ε := by
  simp_rw [mul_pow]
  rw [cubeMean_smul]
  have h := centered_orthogonality (fun _ : Fin 2 => ε) Finset.univ Finset.univ
  simp only [if_pos rfl, ← pow_two] at h
  rw [h]
  simp [Fin.prod_univ_two, rareSourceVariance]
  ring

/-- The persistent target quantity is the squared norm of the stale-slope error. -/
theorem rare_transport_debt_realized (γ ε : ℝ) :
    cubeMean (fun _ : Fin 2 => (1 : ℝ) / 2) (fun x =>
      additiveResponse (fun _ => 1 / 2) (fun _ => γ * ε - γ / 2) x ^ 2) =
      rareTransportDebt γ ε := by
  rw [additive_squared_norm]
  simp [Fin.sum_univ_two, rareTransportDebt]
  ring

theorem rare_source_limits (γ : ℝ) :
    Tendsto (rareSourceVariance γ) (𝓝 0) (𝓝 0) ∧
    Tendsto (rareTransportDebt γ) (𝓝 0) (𝓝 (γ ^ 2 / 8)) := by
  constructor
  · have h := (show Continuous (rareSourceVariance γ) by unfold rareSourceVariance; fun_prop).continuousAt (x := 0)
    change Tendsto (rareSourceVariance γ) (𝓝 0) (𝓝 (rareSourceVariance γ 0)) at h
    simpa only [rareSourceVariance, sub_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul] using h
  · have h := (show Continuous (rareTransportDebt γ) by unfold rareTransportDebt; fun_prop).continuousAt (x := 0)
    change Tendsto (rareTransportDebt γ) (𝓝 0) (𝓝 (rareTransportDebt γ 0)) at h
    have he : rareTransportDebt γ 0 = γ ^ 2 / 8 := by unfold rareTransportDebt; ring
    rwa [he] at h

/-- No constant uniformly bounds target debt by discovery interaction variance. -/
theorem no_uniform_source_variance_bound (γ : ℝ) (hγ : γ ≠ 0) :
    ¬ ∃ C : ℝ, ∀ ε ∈ Set.Ioo (0 : ℝ) 1, rareTransportDebt γ ε ≤ C * rareSourceVariance γ ε := by
  rintro ⟨C, hC⟩
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    norm_num [Function.comp_def, Nat.cast_add, add_assoc] at h
    simpa only [one_div] using h
  have hD := (rare_source_limits γ).2.comp heps
  have hV := ((rare_source_limits γ).1.comp heps).const_mul C
  have hle := le_of_tendsto_of_tendsto' hD hV (fun n => hC _ (by
    constructor
    · positivity
    · apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
      linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]))
  have hp := sq_pos_of_ne_zero hγ
  norm_num at hle
  linarith

end Descent.Portability.ArchaicPrediction

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Probability.Distributions.Exponential

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The single-feature Kingman limit behind Theorem 3

The spec is `ANCESTRAL_LOCALITY.md` §4.1, where the Kingman limit of each feature's genealogy is
called classical. This file proves its pair version for the finite-population chain (4.5) of
`CompatibilityNeutrality`: two lineages sampled at one feature `k`.

**Sources.** An offspring carries at feature `k` the value of exactly one parent, its source.
`orderedSource` names the source of an ordered child, whose value at `k` is its source's
(`orderedChild_apply_eq_source`). `annotatedLaw G N k pop` is the joint law of an offspring's
source and genome given the parental population `pop`: with weight `1 - R/N` it copies a
uniformly drawn parent (`copyAnnotation`), and with weight `r_ij/N` it is an ordered child of two
independently drawn parents (`exchangeAnnotation`). Its genome marginal is the finite-population
law `Q_N` of the empirical law of `pop` (`sum_annotatedLaw_fst`), so the offspring count at `k` is
the binomial law of `sum_offspringCount` (`sum_offspringCount_annotatedLaw`). Its source marginal
is uniform, `1/N` for every parent and every parental population (`sum_annotatedLaw_snd`): as in
the proof of Theorem 3, an exchange permutes the two parents at every coordinate
(`orderedSource_indicator_add`).

**One generation.** A generation is `N` independent offspring. Two distinct offspring have the
same source with probability exactly `1/N`, whatever the parental genomes
(`sum_prod_annotatedLaw_source_eq`), through the pair marginal of a product law
(`sum_prod_mul_pair`).

**Many generations.** `featureHistoryWeight` is the law of an `m`-generation history from founders
`pop₀`, each generation drawn from the annotated law of the one before, and `featureAncestor`
traces an offspring of the newest generation back to the founders. The probability `P(T_N > m)`
that two distinct offspring have distinct founder ancestors is exactly `(1 - 1/N)^m`, for every
checking graph and all founders (`featurePairSurvival_eq`). The parental population of each
generation is the random genomes of the one before, and the survival does not depend on them: the
per-generation coalescence events are independent, each of probability `1/N`.

**The limit.** `(1 - 1/N)^⌊tN⌋ → e^{-t}` (`tendsto_one_sub_inv_pow_floor`). So on the time scale
of `N` generations `P(T_N > ⌊tN⌋) → e^{-t}` (`tendsto_featurePairSurvival`), and `P(T_N ≤ ⌊tN⌋)`
converges to the distribution function of `Exp(1)`, `ProbabilityTheory.expMeasure 1`
(`tendsto_one_sub_featurePairSurvival`).

Scope. Two lineages at one feature are treated; the `n`-lineage coalescent, with rate `C(n,2)/N`
up to `O(1/N²)`, is not formalized. Convergence in law is stated as convergence of the
distribution function at every `t ≥ 0`, not as weak convergence of measures. In the limit
theorems the population has size `N + 2` and the sampled offspring are individuals `0` and `1`.

## Empirical status

None. The bodies here are finite sums of products of supplied rates and indicators, and one real
limit; no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter
open scoped Topology

noncomputable section

/-! ### Marginals of mixtures and of product laws -/

section Marginals

/-- The mixture of a point with itself is the point mass. -/
theorem halfMix_self {H : Type*} [DecidableEq H] (u z : H) :
    halfMix u u z = if u = z then 1 else 0 := by
  unfold halfMix
  ring

/-- Summing the first coordinate out of a mixture of two point masses on a product. -/
theorem sum_halfMix_fst {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (u v : α × β) (z : β) : ∑ s, halfMix u v (s, z) = halfMix u.2 v.2 z := by
  have h : ∀ (w : α × β) (s : α), (if w = (s, z) then (1 : ℝ) else 0) =
      if w.1 = s then (if w.2 = z then 1 else 0) else 0 := by
    intro w s
    obtain ⟨w1, w2⟩ := w
    by_cases h1 : w1 = s <;> by_cases h2 : w2 = z <;> simp [h1, h2]
  simp only [halfMix, sum_add_distrib, ← sum_div, h, sum_ite_eq, mem_univ, ↓reduceIte]

/-- Summing the second coordinate out of a mixture of two point masses on a product. -/
theorem sum_halfMix_snd {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype β]
    (u v : α × β) (s : α) : ∑ z, halfMix u v (s, z) = halfMix u.1 v.1 s := by
  have h : ∀ (w : α × β) (z : β), (if w = (s, z) then (1 : ℝ) else 0) =
      if w.2 = z then (if w.1 = s then 1 else 0) else 0 := by
    intro w z
    obtain ⟨w1, w2⟩ := w
    by_cases h1 : w1 = s <;> by_cases h2 : w2 = z <;> simp [h1, h2]
  simp only [halfMix, sum_add_distrib, ← sum_div, h, sum_ite_eq, mem_univ, ↓reduceIte]

/-- The two-point mixtures over all ordered pairs of `N` points carry total mass `N` at a point. -/
theorem sum_sum_halfMix {N : ℕ} (s : Fin N) : ∑ a, ∑ b, halfMix a b s = N := by
  have h : ∀ a : Fin N, ∑ b, halfMix a b s = (N : ℝ) * ((if a = s then 1 else 0) / 2) + 1 / 2 := by
    intro a
    unfold halfMix
    rw [sum_add_distrib, sum_const, ← sum_div, sum_ite_eq', if_pos (mem_univ s), card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  simp only [h]
  rw [sum_add_distrib, ← mul_sum, ← sum_div, sum_ite_eq', if_pos (mem_univ s), sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The pair marginal of a product law.** Under `∏_c w_c(x_c)`, with every `w_c` of total mass
one, the coordinates `a ≠ b` have the product law `w_a ⊗ w_b`. -/
theorem sum_prod_mul_pair {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : ι → κ → ℝ) (hw : ∀ c, ∑ t, w c t = 1) {a b : ι} (hab : a ≠ b) (g : κ → κ → ℝ) :
    ∑ x : ι → κ, (∏ c, w c (x c)) * g (x a) (x b) = ∑ u, ∑ v, w a u * w b v * g u v := by
  have hfac : ∀ (u v : κ) (c : ι), ∑ t, w c t * (if c = a then (if t = u then 1 else 0) else 1) *
      (if c = b then (if t = v then 1 else 0) else 1) =
      (if c = a then w a u else 1) * (if c = b then w b v else 1) := by
    intro u v c
    by_cases hca : c = a
    · subst hca
      simp [hab]
    · by_cases hcb : c = b
      · subst hcb
        simp [hca]
      · simp [hca, hcb, hw c]
  have key : ∀ u v : κ, ∑ x : ι → κ, (∏ c, w c (x c)) *
      ((if x a = u then 1 else 0) * (if x b = v then 1 else 0)) = w a u * w b v := by
    intro u v
    have hprod : ∀ x : ι → κ, (∏ c, w c (x c)) * ((if x a = u then 1 else 0) *
        (if x b = v then 1 else 0)) = ∏ c, (w c (x c) *
          (if c = a then (if x c = u then 1 else 0) else 1) *
          (if c = b then (if x c = v then 1 else 0) else 1)) := by
      intro x
      rw [prod_mul_distrib, prod_mul_distrib,
        Fintype.prod_ite_eq' a fun c ↦ if x c = u then (1 : ℝ) else 0,
        Fintype.prod_ite_eq' b fun c ↦ if x c = v then (1 : ℝ) else 0, mul_assoc]
    rw [sum_congr rfl fun x _ ↦ hprod x]
    rw [← Fintype.prod_sum fun c t ↦ w c t * (if c = a then (if t = u then 1 else 0) else 1) *
      (if c = b then (if t = v then 1 else 0) else 1)]
    rw [prod_congr rfl fun c _ ↦ hfac u v c, prod_mul_distrib,
      Fintype.prod_ite_eq' a fun _ ↦ w a u, Fintype.prod_ite_eq' b fun _ ↦ w b v]
  calc ∑ x : ι → κ, (∏ c, w c (x c)) * g (x a) (x b)
      = ∑ x : ι → κ, ∑ u, ∑ v, g u v * ((∏ c, w c (x c)) *
          ((if x a = u then 1 else 0) * (if x b = v then 1 else 0))) := by
        refine sum_congr rfl fun x _ ↦ ?_
        have hterm : ∀ u v, g u v * ((∏ c, w c (x c)) *
            ((if x a = u then (1 : ℝ) else 0) * (if x b = v then 1 else 0))) =
            if x b = v then (if x a = u then g u v * ∏ c, w c (x c) else 0) else 0 := by
          intro u v
          split_ifs <;> ring
        simp only [hterm, sum_ite_eq, mem_univ, ↓reduceIte]
        ring
    _ = ∑ u, ∑ v, g u v * ∑ x : ι → κ, (∏ c, w c (x c)) *
          ((if x a = u then 1 else 0) * (if x b = v then 1 else 0)) := by
        conv_lhs => rw [sum_comm]
        refine sum_congr rfl fun u _ ↦ ?_
        conv_lhs => rw [sum_comm]
        simp only [mul_sum]
    _ = ∑ u, ∑ v, w a u * w b v * g u v := by
        simp only [key]
        exact sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ by ring

end Marginals

/-! ### Sources and the annotated offspring law -/

section Sources

variable {V : Type*} [DecidableEq V]

/-- **The source at feature `k` of an ordered child.** The ordered child `T_ij(pop a, pop b)`
carries at `k` the value of parent `b` exactly when `k` is the target `i` and the parents agree at
the checker `j`, and the value of parent `a` otherwise. -/
def orderedSource {N : ℕ} (i j k : V) (pop : Fin N → V → Bool) (a b : Fin N) : Fin N :=
  if k = i ∧ pop a j = pop b j then b else a

/-- The ordered child carries at feature `k` the value of its source there. -/
theorem orderedChild_apply_eq_source {N : ℕ} (i j k : V) (pop : Fin N → V → Bool)
    (a b : Fin N) : orderedChild i j (pop a) (pop b) k = pop (orderedSource i j k pop a b) k := by
  by_cases h : k = i ∧ pop a j = pop b j
  · have e1 : orderedChild i j (pop a) (pop b) k = pop b i := if_pos h
    have e2 : orderedSource i j k pop a b = b := if_pos h
    rw [e1, e2, h.1]
  · have e1 : orderedChild i j (pop a) (pop b) k = pop a k := if_neg h
    have e2 : orderedSource i j k pop a b = a := if_neg h
    rw [e1, e2]

/-- **An exchange permutes the two parents at every feature**: the sources of the two ordered
children are the two parents, in some order. -/
theorem orderedSource_indicator_add {N : ℕ} (i j k : V) (pop : Fin N → V → Bool)
    (a b s : Fin N) :
    (if orderedSource i j k pop a b = s then (1 : ℝ) else 0) +
        (if orderedSource i j k pop b a = s then 1 else 0) =
      (if a = s then 1 else 0) + (if b = s then 1 else 0) := by
  by_cases h : k = i ∧ pop a j = pop b j
  · have e1 : orderedSource i j k pop a b = b := if_pos h
    have e2 : orderedSource i j k pop b a = a := if_pos ⟨h.1, h.2.symm⟩
    rw [e1, e2, add_comm]
  · have e1 : orderedSource i j k pop a b = a := if_neg h
    have e2 : orderedSource i j k pop b a = b := if_neg fun h' ↦ h ⟨h'.1, h'.2.symm⟩
    rw [e1, e2]

variable [Fintype V]

/-- The empirical law `(1/N) ∑_a δ_{pop a}` of a population of `N` genomes. -/
def empiricalLaw {N : ℕ} (pop : Fin N → V → Bool) (z : V → Bool) : ℝ :=
  ∑ a, (N : ℝ)⁻¹ * (if pop a = z then 1 else 0)

/-- Averaging against the empirical law averages over the individuals. -/
theorem sum_empiricalLaw_mul {N : ℕ} (pop : Fin N → V → Bool) (f : (V → Bool) → ℝ) :
    ∑ z, empiricalLaw pop z * f z = ∑ a, (N : ℝ)⁻¹ * f (pop a) := by
  simp only [empiricalLaw, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ ↦ ?_
  simp only [mul_assoc, boole_mul, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte]

/-- The empirical law of a nonempty population has total mass one. -/
theorem sum_empiricalLaw {N : ℕ} (hN : N ≠ 0) (pop : Fin N → V → Bool) :
    ∑ z, empiricalLaw pop z = 1 := by
  have h := sum_empiricalLaw_mul pop fun _ ↦ (1 : ℝ)
  simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [h, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN)]

/-- **The annotated copy event**: a uniformly drawn parent, which is the source at every
feature. -/
def copyAnnotation {N : ℕ} (pop : Fin N → V → Bool) (q : Fin N × (V → Bool)) : ℝ :=
  ∑ a, (N : ℝ)⁻¹ * halfMix (a, pop a) (a, pop a) q

/-- The annotated exchange event along the edge `e` with parents `a` and `b`: half the mass on
each ordered child, together with its source at feature `k`. -/
def annotatedExchange {N : ℕ} (k : V) (pop : Fin N → V → Bool) (e : V × V) (a b : Fin N) :
    Fin N × (V → Bool) → ℝ :=
  halfMix (orderedSource e.1 e.2 k pop a b, orderedChild e.1 e.2 (pop a) (pop b))
    (orderedSource e.1 e.2 k pop b a, orderedChild e.1 e.2 (pop b) (pop a))

/-- **The annotated exchange event** along the edge `e`, with two independently drawn parents. -/
def exchangeAnnotation {N : ℕ} (k : V) (pop : Fin N → V → Bool) (e : V × V)
    (q : Fin N × (V → Bool)) : ℝ :=
  ∑ a, ∑ b, (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * annotatedExchange k pop e a b q)

/-- **The annotated offspring law**: the joint law of an offspring's source at feature `k` and of
its genome under the finite-population law (4.5), given the parental population `pop`. -/
def annotatedLaw (G : CheckingGraph V) (N : ℕ) (k : V) (pop : Fin N → V → Bool)
    (q : Fin N × (V → Bool)) : ℝ :=
  (1 - G.totalRate / N) * copyAnnotation pop q +
    (∑ e ∈ G.edges, G.rate e * exchangeAnnotation k pop e q) / N

theorem sum_copyAnnotation_fst {N : ℕ} (pop : Fin N → V → Bool) (z : V → Bool) :
    ∑ s, copyAnnotation pop (s, z) = empiricalLaw pop z := by
  unfold copyAnnotation empiricalLaw
  rw [sum_comm]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← mul_sum, sum_halfMix_fst, halfMix_self]

theorem sum_copyAnnotation_snd {N : ℕ} (pop : Fin N → V → Bool) (s : Fin N) :
    ∑ z, copyAnnotation pop (s, z) = (N : ℝ)⁻¹ := by
  unfold copyAnnotation
  rw [sum_comm]
  simp only [← mul_sum]
  simp only [sum_halfMix_snd]
  simp only [halfMix_self, sum_ite_eq', mem_univ, ↓reduceIte, mul_one]

theorem sum_annotatedExchange_fst {N : ℕ} (k : V) (pop : Fin N → V → Bool) (e : V × V)
    (a b : Fin N) (z : V → Bool) :
    ∑ s, annotatedExchange k pop e a b (s, z) = exchangeKernel e.1 e.2 (pop a) (pop b) z := by
  unfold annotatedExchange
  rw [sum_halfMix_fst]
  rfl

theorem sum_annotatedExchange_snd {N : ℕ} (k : V) (pop : Fin N → V → Bool) (e : V × V)
    (a b s : Fin N) : ∑ z, annotatedExchange k pop e a b (s, z) = halfMix a b s := by
  have h := orderedSource_indicator_add e.1 e.2 k pop a b s
  unfold annotatedExchange
  rw [sum_halfMix_snd]
  simp only [halfMix]
  linarith

theorem sum_exchangeAnnotation_fst {N : ℕ} (k : V) (pop : Fin N → V → Bool) (e : V × V)
    (z : V → Bool) :
    ∑ s, exchangeAnnotation k pop e (s, z) =
      reproduce (exchangeKernel e.1 e.2) (empiricalLaw pop) z := by
  have hin : ∀ x : V → Bool,
      ∑ y, empiricalLaw pop x * empiricalLaw pop y * exchangeKernel e.1 e.2 x y z =
        empiricalLaw pop x * ∑ b, (N : ℝ)⁻¹ * exchangeKernel e.1 e.2 x (pop b) z := by
    intro x
    rw [← sum_empiricalLaw_mul pop fun y ↦ exchangeKernel e.1 e.2 x y z, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    show _ = empiricalLaw pop x * (empiricalLaw pop y * exchangeKernel e.1 e.2 x y z)
    ring
  calc ∑ s, exchangeAnnotation k pop e (s, z)
      = ∑ a, (N : ℝ)⁻¹ * ∑ b, (N : ℝ)⁻¹ * exchangeKernel e.1 e.2 (pop a) (pop b) z := by
        unfold exchangeAnnotation
        rw [sum_comm]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun b _ ↦ ?_
        rw [← mul_sum, ← mul_sum, sum_annotatedExchange_fst]
    _ = reproduce (exchangeKernel e.1 e.2) (empiricalLaw pop) z := by
        rw [reproduce]
        simp only [hin]
        exact (sum_empiricalLaw_mul pop fun x ↦
          ∑ b, (N : ℝ)⁻¹ * exchangeKernel e.1 e.2 x (pop b) z).symm

theorem sum_exchangeAnnotation_snd {N : ℕ} (hN : N ≠ 0) (k : V) (pop : Fin N → V → Bool)
    (e : V × V) (s : Fin N) : ∑ z, exchangeAnnotation k pop e (s, z) = (N : ℝ)⁻¹ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc ∑ z, exchangeAnnotation k pop e (s, z)
      = (N : ℝ)⁻¹ * ((N : ℝ)⁻¹ * ∑ a, ∑ b, halfMix a b s) := by
        unfold exchangeAnnotation
        conv_lhs => rw [sum_comm]
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun a _ ↦ ?_
        conv_lhs => rw [sum_comm]
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun b _ ↦ ?_
        rw [← mul_sum, ← mul_sum, sum_annotatedExchange_snd]
    _ = (N : ℝ)⁻¹ := by rw [sum_sum_halfMix, inv_mul_cancel₀ hN', mul_one]

/-- **The genome marginal of the annotated law is `Q_N`**: forgetting the source gives the
finite-population law (4.5) of the empirical law of the parents. -/
theorem sum_annotatedLaw_fst (G : CheckingGraph V) (N : ℕ) (k : V) (pop : Fin N → V → Bool)
    (z : V → Bool) :
    ∑ s, annotatedLaw G N k pop (s, z) = finitePopulationLaw G N (empiricalLaw pop) z := by
  simp only [annotatedLaw, sum_add_distrib, ← mul_sum, ← sum_div]
  rw [sum_comm]
  simp only [← mul_sum, sum_copyAnnotation_fst, sum_exchangeAnnotation_fst]
  rfl

/-- **The source is uniform**: every parent is an offspring's source at feature `k` with
probability `1/N`, for every checking graph and every parental population. -/
theorem sum_annotatedLaw_snd (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) (s : Fin N) :
    ∑ z, annotatedLaw G N k pop (s, z) = (N : ℝ)⁻¹ := by
  simp only [annotatedLaw, sum_add_distrib, ← mul_sum, ← sum_div]
  rw [sum_comm]
  simp only [← mul_sum, sum_copyAnnotation_snd, sum_exchangeAnnotation_snd hN, ← sum_mul]
  simp only [CheckingGraph.totalRate]
  ring

/-- The annotated law has total mass one. -/
theorem sum_annotatedLaw (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) : ∑ q, annotatedLaw G N k pop q = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_annotatedLaw_snd G hN k pop, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN)

/-- **The offspring count is binomial**: among `N` independent offspring the count carrying
allele `1` at feature `k` has the law of `sum_offspringCount` at the empirical frequency of the
parents. -/
theorem sum_offspringCount_annotatedLaw (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) (c : ℕ) :
    ∑ z ∈ univ.filter (fun z : Fin N → V → Bool ↦ #(univ.filter fun i ↦ z i k = true) = c),
        ∏ i, ∑ s, annotatedLaw G N k pop (s, z i) =
      N.choose c * featureMass (empiricalLaw pop) k true ^ c *
        (1 - featureMass (empiricalLaw pop) k true) ^ (N - c) := by
  simp only [sum_annotatedLaw_fst]
  exact sum_offspringCount G N (empiricalLaw pop) (sum_empiricalLaw hN pop) k c

/-- Two independent offspring: the joint law of their sources is uniform on pairs. -/
theorem sum_sum_annotatedLaw_mul (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) (f : Fin N → Fin N → ℝ) :
    ∑ q, ∑ q', annotatedLaw G N k pop q * annotatedLaw G N k pop q' * f q.1 q'.1 =
      ∑ s, ∑ s', (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * f s s' := by
  have h : ∀ s s' : Fin N, ∑ z, ∑ z',
      annotatedLaw G N k pop (s, z) * annotatedLaw G N k pop (s', z') * f s s' =
        (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * f s s' := by
    intro s s'
    calc ∑ z, ∑ z', annotatedLaw G N k pop (s, z) * annotatedLaw G N k pop (s', z') * f s s'
        = (∑ z, annotatedLaw G N k pop (s, z)) * (∑ z', annotatedLaw G N k pop (s', z')) *
            f s s' := by
          rw [sum_mul_sum, sum_mul]
          exact sum_congr rfl fun z _ ↦ by rw [sum_mul]
      _ = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * f s s' := by
          rw [sum_annotatedLaw_snd G hN k pop s, sum_annotatedLaw_snd G hN k pop s']
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun s' _ ↦ h s s'

/-- **Two distinct offspring share their source with probability exactly `1/N`**, for every
checking graph and every parental population. -/
theorem sum_prod_annotatedLaw_source_eq (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop : Fin N → V → Bool) {a b : Fin N} (hab : a ≠ b) :
    ∑ x : Fin N → Fin N × (V → Bool), (∏ c, annotatedLaw G N k pop (x c)) *
      (if (x a).1 = (x b).1 then 1 else 0) = (N : ℝ)⁻¹ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [sum_prod_mul_pair (fun _ q ↦ annotatedLaw G N k pop q)
      (fun _ ↦ sum_annotatedLaw G hN k pop) hab (fun q q' ↦ if q.1 = q'.1 then (1 : ℝ) else 0),
    sum_sum_annotatedLaw_mul G hN k pop fun u v ↦ if u = v then (1 : ℝ) else 0]
  simp only [mul_boole, sum_ite_eq, mem_univ, ↓reduceIte, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]

/-! ### Histories and the pair coalescence time -/

/-- A generation of `N` offspring, each with its source at feature `k` and its genome. -/
abbrev FeatureGeneration (N : ℕ) (V : Type*) := Fin N → Fin N × (V → Bool)

/-- The genomes of the newest generation of a history, or the founders when it is empty. -/
def newestFeaturePopulation {N : ℕ} (pop₀ : Fin N → V → Bool) :
    (m : ℕ) → (Fin m → FeatureGeneration N V) → Fin N → V → Bool
  | 0, _ => pop₀
  | _ + 1, h => fun c ↦ (h 0 c).2

/-- **The law of an `m`-generation history** of the finite-population chain (4.5), with sources
at feature `k`. Generation `0` of the history is the newest; each of its offspring is drawn
independently from the annotated law of the next older generation, or of the founders `pop₀`. -/
def featureHistoryWeight (G : CheckingGraph V) (N : ℕ) (k : V) (pop₀ : Fin N → V → Bool) :
    (m : ℕ) → (Fin m → FeatureGeneration N V) → ℝ
  | 0, _ => 1
  | m + 1, h =>
      (∏ c, annotatedLaw G N k (newestFeaturePopulation pop₀ m (Fin.tail h)) (h 0 c)) *
        featureHistoryWeight G N k pop₀ m (Fin.tail h)

/-- The founder ancestor at feature `k` of offspring `c` of the newest generation. -/
def featureAncestor {N : ℕ} : (m : ℕ) → (Fin m → FeatureGeneration N V) → Fin N → Fin N
  | 0, _, c => c
  | m + 1, h, c => featureAncestor m (Fin.tail h) (h 0 c).1

/-- **`P(T_N > m)`**: the probability that offspring `a` and `b` of the newest generation of an
`m`-generation history have distinct founder ancestors at feature `k`. -/
def featurePairSurvival (G : CheckingGraph V) (N : ℕ) (k : V) (pop₀ : Fin N → V → Bool)
    (m : ℕ) (a b : Fin N) : ℝ :=
  ∑ h : Fin m → FeatureGeneration N V, featureHistoryWeight G N k pop₀ m h *
    (if featureAncestor m h a = featureAncestor m h b then 0 else 1)

/-- **The pair coalescence time is geometric**: `P(T_N > m) = (1 - 1/N)^m` for two distinct
sampled offspring, every checking graph and all founders. -/
theorem featurePairSurvival_eq (G : CheckingGraph V) {N : ℕ} (hN : N ≠ 0) (k : V)
    (pop₀ : Fin N → V → Bool) (m : ℕ) {a b : Fin N} (hab : a ≠ b) :
    featurePairSurvival G N k pop₀ m a b = (1 - (N : ℝ)⁻¹) ^ m := by
  induction m generalizing a b with
  | zero =>
    rw [featurePairSurvival, Fintype.sum_unique]
    simp [featureHistoryWeight, featureAncestor, hab]
  | succ m ih =>
    have hstep : ∀ t : Fin m → FeatureGeneration N V,
        ∑ x : FeatureGeneration N V, featureHistoryWeight G N k pop₀ (m + 1) (Fin.cons x t) *
          (if featureAncestor (m + 1) (Fin.cons x t) a =
            featureAncestor (m + 1) (Fin.cons x t) b then 0 else 1) =
        featureHistoryWeight G N k pop₀ m t * ∑ u, ∑ v, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
          (if featureAncestor m t u = featureAncestor m t v then 0 else 1) := by
      intro t
      simp only [featureHistoryWeight, featureAncestor, Fin.tail_cons, Fin.cons_zero]
      calc ∑ x : FeatureGeneration N V,
            (∏ c, annotatedLaw G N k (newestFeaturePopulation pop₀ m t) (x c)) *
              featureHistoryWeight G N k pop₀ m t *
              (if featureAncestor m t (x a).1 = featureAncestor m t (x b).1 then 0 else 1)
          = featureHistoryWeight G N k pop₀ m t * ∑ x : FeatureGeneration N V,
              (∏ c, annotatedLaw G N k (newestFeaturePopulation pop₀ m t) (x c)) *
                (if featureAncestor m t (x a).1 = featureAncestor m t (x b).1 then 0 else 1) := by
            rw [mul_sum]
            exact sum_congr rfl fun x _ ↦ by ring
        _ = featureHistoryWeight G N k pop₀ m t * ∑ q, ∑ q',
              annotatedLaw G N k (newestFeaturePopulation pop₀ m t) q *
                annotatedLaw G N k (newestFeaturePopulation pop₀ m t) q' *
                (if featureAncestor m t q.1 = featureAncestor m t q'.1 then 0 else 1) := by
            congr 1
            exact sum_prod_mul_pair
              (fun _ q ↦ annotatedLaw G N k (newestFeaturePopulation pop₀ m t) q)
              (fun _ ↦ sum_annotatedLaw G hN k _) hab
              (fun q q' ↦ if featureAncestor m t q.1 = featureAncestor m t q'.1 then (0 : ℝ)
                else 1)
        _ = featureHistoryWeight G N k pop₀ m t * ∑ u, ∑ v, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
              (if featureAncestor m t u = featureAncestor m t v then 0 else 1) := by
            congr 1
            exact sum_sum_annotatedLaw_mul G hN k _
              fun u v ↦ if featureAncestor m t u = featureAncestor m t v then (0 : ℝ) else 1
    calc featurePairSurvival G N k pop₀ (m + 1) a b
        = ∑ p : FeatureGeneration N V × (Fin m → FeatureGeneration N V),
            featureHistoryWeight G N k pop₀ (m + 1) (Fin.cons p.1 p.2) *
              (if featureAncestor (m + 1) (Fin.cons p.1 p.2) a =
                featureAncestor (m + 1) (Fin.cons p.1 p.2) b then 0 else 1) :=
          ((Fin.consEquiv fun _ ↦ FeatureGeneration N V).sum_comp
            fun h ↦ featureHistoryWeight G N k pop₀ (m + 1) h *
              (if featureAncestor (m + 1) h a = featureAncestor (m + 1) h b then 0 else 1)).symm
      _ = ∑ t : Fin m → FeatureGeneration N V, featureHistoryWeight G N k pop₀ m t *
            ∑ u, ∑ v, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
              (if featureAncestor m t u = featureAncestor m t v then 0 else 1) := by
          rw [Fintype.sum_prod_type, sum_comm]
          exact sum_congr rfl fun t _ ↦ hstep t
      _ = ∑ u, ∑ v, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * featurePairSurvival G N k pop₀ m u v := by
          simp only [featurePairSurvival, mul_sum]
          conv_lhs => rw [sum_comm]
          refine sum_congr rfl fun u _ ↦ ?_
          conv_lhs => rw [sum_comm]
          exact sum_congr rfl fun v _ ↦ sum_congr rfl fun t _ ↦ by ring
      _ = ∑ u : Fin N, ∑ v : Fin N, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
            (if u = v then 0 else (1 - (N : ℝ)⁻¹) ^ m) := by
          refine sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ ?_
          by_cases huv : u = v
          · subst huv
            simp [featurePairSurvival]
          · rw [ih huv, if_neg huv]
      _ = (1 - (N : ℝ)⁻¹) ^ (m + 1) := by
          have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
          have hterm : ∀ u v : Fin N, (N : ℝ)⁻¹ * (N : ℝ)⁻¹ *
              (if u = v then 0 else (1 - (N : ℝ)⁻¹) ^ m) =
              (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (1 - (N : ℝ)⁻¹) ^ m -
                (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (1 - (N : ℝ)⁻¹) ^ m * (if u = v then 1 else 0) := by
            intro u v
            split_ifs <;> ring
          simp only [hterm, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte, mul_one]
          have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN'
          linear_combination ((N * (N : ℝ)⁻¹ + 1) * (1 - (N : ℝ)⁻¹) ^ m -
            (N : ℝ)⁻¹ * (1 - (N : ℝ)⁻¹) ^ m) * h1

end Sources

/-! ### The limit -/

/-- **The geometric survival on the `N`-generation scale tends to `e^{-t}`**:
`(1 - 1/N)^⌊tN⌋ → e^{-t}` for every `t ≥ 0`. -/
theorem tendsto_one_sub_inv_pow_floor {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ ↦ (1 - (N : ℝ)⁻¹) ^ ⌊t * N⌋₊) atTop (𝓝 (Real.exp (-t))) := by
  have hbase : Tendsto (fun N : ℕ ↦ (1 - (N : ℝ)⁻¹) ^ N) atTop (𝓝 (Real.exp (-1))) :=
    (Real.tendsto_one_add_div_pow_exp (-1)).congr fun N ↦ by ring
  have hexp : Tendsto (fun N : ℕ ↦ (⌊t * N⌋₊ : ℝ) / N) atTop (𝓝 t) :=
    (tendsto_nat_floor_mul_div_atTop ht).comp tendsto_natCast_atTop_atTop
  have hrpow := hbase.rpow hexp (Or.inl (Real.exp_pos _).ne')
  rw [← Real.exp_mul, neg_one_mul] at hrpow
  refine hrpow.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  show ((1 - (N : ℝ)⁻¹) ^ N) ^ ((⌊t * N⌋₊ : ℝ) / N) = (1 - (N : ℝ)⁻¹) ^ ⌊t * N⌋₊
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbase0 : 0 ≤ 1 - (N : ℝ)⁻¹ :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hN))
  have hmul : (N : ℝ) * ((⌊t * N⌋₊ : ℝ) / N) = ⌊t * N⌋₊ := by field_simp
  rw [← Real.rpow_natCast (1 - (N : ℝ)⁻¹) N, ← Real.rpow_mul hbase0, hmul, Real.rpow_natCast]

section Limit

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The pair coalescence time converges on the `N`-generation scale**: in a population of
`N + 2` genomes, `P(T > ⌊t(N+2)⌋) → e^{-t}`, whatever the checking graphs and founders. -/
theorem tendsto_featurePairSurvival (G : ℕ → CheckingGraph V) (k : V)
    (pop₀ : (N : ℕ) → Fin (N + 2) → V → Bool) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ ↦ featurePairSurvival (G N) (N + 2) k (pop₀ N) ⌊t * (N + 2 : ℕ)⌋₊ 0 1)
      atTop (𝓝 (Real.exp (-t))) := by
  refine ((tendsto_one_sub_inv_pow_floor ht).comp (tendsto_add_atTop_nat 2)).congr fun N ↦ ?_
  exact (featurePairSurvival_eq (G N) (by omega) k (pop₀ N) _ zero_ne_one).symm

/-- **The rescaled pair coalescence time converges in law to `Exp(1)`**: the distribution
function of `T/(N+2)` at every `t ≥ 0` tends to that of `ProbabilityTheory.expMeasure 1`. -/
theorem tendsto_one_sub_featurePairSurvival (G : ℕ → CheckingGraph V) (k : V)
    (pop₀ : (N : ℕ) → Fin (N + 2) → V → Bool) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto
      (fun N : ℕ ↦ 1 - featurePairSurvival (G N) (N + 2) k (pop₀ N) ⌊t * (N + 2 : ℕ)⌋₊ 0 1)
      atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.expMeasure 1) t)) := by
  rw [ProbabilityTheory.cdf_expMeasure_eq one_pos, if_pos ht, one_mul]
  exact (tendsto_featurePairSurvival G k pop₀ ht).const_sub 1

end Limit

end

end Descent.Pangenome.AncestralLocality

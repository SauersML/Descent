/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Tactic

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Compatibility neutrality: local checking gates leave every feature exactly neutral

The spec is `ANCESTRAL_LOCALITY.md` §4, §4.1 and §5.2, from the research note "Ancestral
locality" of 11 September 2026. Genomes are Boolean assignments `V → Bool` to a finite feature
set `V`. A `CheckingGraph` carries directed edges `i → j` with positive rates `r_ij`:
recombination at the target `i` is permitted when the parents agree at the checker `j`.

The ordered child `orderedChild i j x y` is the note's `T_ij(x,y)` (4.1). The symmetric kernel
`exchangeKernel i j` is `K_ij` (4.2), the equal mixture `halfMix` of the two ordered children.
`compatibilityKernel G` is `K_G` (4.3): the rate-weighted average of the `K_ij` over the edges,
or unbiased parental copying `halfMix x y` when `G` has no edges.

**Theorem 3 (4.4).** `compatibilityKernel_marginal`: `K_G(x,y; {z : z_k = a})` equals
`1{x_k = a}/2 + 1{y_k = a}/2` for every graph, feature, allele and parental pair. The proof is
the note's: an exchange permutes the two parental values at every coordinate
(`orderedChild_indicator_add`). The population form, `featureMass_reproduce_compatibilityKernel`,
says one generation leaves the allele law at every feature unchanged, `(R_{K_G}(p))_k = p_k`,
for every `p` of total mass one.

**The finite population (§4.1).** `finitePopulationLaw G N p` is `Q_N(p)` (4.5). It keeps every
allele law (`featureMass_finitePopulationLaw`), and it is a probability vector when `R ≤ N`
(`finitePopulationLaw_nonneg`, `sum_finitePopulationLaw`). The law of `N` i.i.d. offspring is
the product law, and the number of offspring carrying allele `1` at feature `k` is binomial.
`sum_offspringCount` gives `C(N,c) p_k^c (1 - p_k)^(N-c)` as an exact finite sum over the
`N`-tuples of genomes, from the general count law `sum_prod_filter_card_eq_choose`.
`offspringCount_eq_binomial` identifies that sum with Mathlib's `PMF.binomial`. So the marginal
frequency process is the ordinary Wright-Fisher chain, whatever the graph. The Kingman limit of
that chain is classical and is not re-proved here.

**The eight-state witness (§5.2).** Take features `(a, b, h) = (0, 1, 2)` of `Fin 3`, the single
rule `witnessGraph` ("exchange `a` only when the parents agree at `h`"), and the observation
`observeAB`. The populations `witnessP = ½δ_000 + ½δ_110` and `witnessQ = ½δ_000 + ½δ_111` have
the same observed law (`witness_pushforward_eq`). Yet (5.5) holds, `witness_drift`:
`R_K(p)[ab] - p[ab] = -1/4` and `R_K(q)[ab] - q[ab] = 0`. Hence no map on observed laws predicts
both next generations (`witness_no_observed_transition_law`). No kernel on `(a, b)` states
satisfies the autonomy equation (2.2) either (`witness_not_autonomous`).

Scope. The population map `reproduce` (2.1) and the pushforward `pushforward` are local
stand-ins for the heredity-kernel layer of spec §2; they are to be swapped for that layer's
versions once it is on main. Kernels are plain functions `H → H → H → ℝ`, not bundled stochastic
kernels, and nonnegativity and total mass are proved where they are used. The binomial law is
stated for one generation given `p`, as the product-law mass of each count. The Markov chain of
frequencies over many generations, its diffusion limit and the Kingman limit are not
constructed. (5.5) is stated as the note's checker, the one-step difference
`R_K(p)[ab] - p[ab]`, which is the drift of the unit-rate generator (7.1) at time zero; the time
derivative itself is not formalized.

## Empirical status

None. The bodies here are finite sums of products of kernel weights over Boolean genomes. The
checking graph, its rates and the population are supplied, and no measurement can bear on an
identity between finite sums.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped NNReal

noncomputable section

/-! ### Populations on a finite state space -/

section Population

variable {H : Type*} [Fintype H]

/-- **The population map (2.1)**, `R_K(p)(z) = ∑_{x,y} p_x p_y K(x,y;z)`: two parents drawn
independently from `p`, and one offspring drawn from the kernel `K`. -/
def reproduce (K : H → H → H → ℝ) (p : H → ℝ) (z : H) : ℝ :=
  ∑ x, ∑ y, p x * p y * K x y z

/-- The mass the population map gives a set of states is the parental average of the kernel's
mass on that set. -/
theorem sum_block_reproduce (K : H → H → H → ℝ) (p : H → ℝ) (B : Finset H) :
    ∑ z ∈ B, reproduce K p z = ∑ x, ∑ y, p x * p y * ∑ z ∈ B, K x y z := by
  unfold reproduce
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [mul_sum]

/-- A kernel whose offspring laws have total mass one sends `p` to total mass `(∑ p)²`. -/
theorem sum_reproduce (K : H → H → H → ℝ) (p : H → ℝ) (hK : ∀ x y, ∑ z, K x y z = 1) :
    ∑ z, reproduce K p z = (∑ x, p x) ^ 2 := by
  rw [sum_block_reproduce K p univ, sq, sum_mul_sum]
  simp only [hK, mul_one]

/-- A nonnegative kernel sends a nonnegative population to a nonnegative one. -/
theorem reproduce_nonneg (K : H → H → H → ℝ) (hK : ∀ x y z, 0 ≤ K x y z) (p : H → ℝ)
    (hp : ∀ z, 0 ≤ p z) (z : H) : 0 ≤ reproduce K p z :=
  sum_nonneg fun x _ ↦ sum_nonneg fun y _ ↦ mul_nonneg (mul_nonneg (hp x) (hp y)) (hK x y z)

/-- The pushforward `obs_# p` of a mass function along an observation `obs`. -/
def pushforward {O : Type*} [DecidableEq O] (obs : H → O) (p : H → ℝ) (o : O) : ℝ :=
  ∑ z ∈ univ.filter (fun z ↦ obs z = o), p z

/-- **The count law of an i.i.d. sample.** Under the product law `∏_i q(z_i)` of `N` independent
draws from a mass function `q` of total mass one, the number of draws landing in the event `P`
is `c` with mass `C(N,c) s^c (1 - s)^(N-c)`, where `s` is the mass of `P`. -/
theorem sum_prod_filter_card_eq_choose (q : H → ℝ) (hq : ∑ w, q w = 1) (P : H → Prop)
    [DecidablePred P] (N c : ℕ) :
    ∑ z ∈ univ.filter (fun z : Fin N → H ↦ #(univ.filter fun i ↦ P (z i)) = c), ∏ i, q (z i) =
      N.choose c * (∑ w ∈ univ.filter P, q w) ^ c *
        (1 - ∑ w ∈ univ.filter P, q w) ^ (N - c) := by
  have hcompl : ∑ w ∈ univ.filter (fun w ↦ ¬ P w), q w = 1 - ∑ w ∈ univ.filter P, q w := by
    have h := sum_filter_add_sum_filter_not univ P q
    linarith
  have hprod : ∀ S : Finset (Fin N), ∏ i : Fin N,
      (if i ∈ S then ∑ w ∈ univ.filter P, q w else 1 - ∑ w ∈ univ.filter P, q w) =
      (∑ w ∈ univ.filter P, q w) ^ #S * (1 - ∑ w ∈ univ.filter P, q w) ^ (N - #S) := by
    intro S
    rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter,
      filter_notMem_eq_sdiff, card_univ_diff, Fintype.card_fin]
  have hmaps : ∀ z ∈ univ.filter (fun z : Fin N → H ↦ #(univ.filter fun i ↦ P (z i)) = c),
      univ.filter (fun i ↦ P (z i)) ∈ powersetCard c (univ : Finset (Fin N)) :=
    fun z hz ↦ mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hz).2⟩
  have hterm : ∀ S ∈ powersetCard c (univ : Finset (Fin N)),
      ∑ z ∈ univ.filter (fun z : Fin N → H ↦ #(univ.filter fun i ↦ P (z i)) = c) with
          univ.filter (fun i ↦ P (z i)) = S, ∏ i, q (z i) =
        (∑ w ∈ univ.filter P, q w) ^ c * (1 - ∑ w ∈ univ.filter P, q w) ^ (N - c) := by
    intro S hS
    have hcard : #S = c := (mem_powersetCard.mp hS).2
    have hfiber : (univ.filter fun z : Fin N → H ↦ #(univ.filter fun i ↦ P (z i)) = c).filter
        (fun z ↦ univ.filter (fun i ↦ P (z i)) = S) =
        Fintype.piFinset fun i ↦ univ.filter fun w ↦ (P w ↔ i ∈ S) := by
      ext z
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, hz⟩ i
        rw [← hz]
        simp
      · intro hz
        have hset : univ.filter (fun i ↦ P (z i)) = S := by
          ext i
          simpa using hz i
        exact ⟨by rw [hset, hcard], hset⟩
    rw [hfiber, ← hcard, ← hprod S]
    calc ∑ z ∈ Fintype.piFinset (fun i ↦ univ.filter fun w ↦ (P w ↔ i ∈ S)), ∏ i, q (z i)
        = ∏ i, ∑ w ∈ univ.filter (fun w ↦ (P w ↔ i ∈ S)), q w := (prod_univ_sum _ _).symm
      _ = ∏ i : Fin N,
          (if i ∈ S then ∑ w ∈ univ.filter P, q w else 1 - ∑ w ∈ univ.filter P, q w) := by
        refine prod_congr rfl fun i _ ↦ ?_
        by_cases hi : i ∈ S
        · rw [if_pos hi]
          exact sum_congr (by ext w; simp [hi]) fun _ _ ↦ rfl
        · rw [if_neg hi, ← hcompl]
          exact sum_congr (by ext w; simp [hi]) fun _ _ ↦ rfl
  rw [← sum_fiberwise_of_maps_to hmaps, sum_congr rfl hterm, sum_const, card_powersetCard,
    card_fin, nsmul_eq_mul, mul_assoc]

end Population

/-! ### The equal mixture of two point masses -/

section Mixture

variable {H : Type*} [DecidableEq H]

/-- The equal mixture `½δ_u + ½δ_v` of two point masses. -/
def halfMix (u v z : H) : ℝ :=
  (if u = z then 1 else 0) / 2 + (if v = z then 1 else 0) / 2

/-- The mixture is nonnegative. -/
theorem halfMix_nonneg (u v z : H) : 0 ≤ halfMix u v z := by
  unfold halfMix
  positivity

variable [Fintype H]

/-- Integrating against the mixture averages the two endpoints. -/
theorem sum_halfMix_mul (u v : H) (g : H → ℝ) :
    ∑ z, halfMix u v z * g z = g u / 2 + g v / 2 := by
  have hz : ∀ z, halfMix u v z * g z =
      (if u = z then g z else 0) / 2 + (if v = z then g z else 0) / 2 := by
    intro z
    unfold halfMix
    split_ifs <;> ring
  simp only [hz, sum_add_distrib, ← sum_div, sum_ite_eq, mem_univ, ↓reduceIte]

/-- The mass of an event under the mixture counts the endpoints in the event. -/
theorem sum_filter_halfMix (u v : H) (P : H → Prop) [DecidablePred P] :
    ∑ z ∈ univ.filter P, halfMix u v z =
      (if P u then 1 else 0) / 2 + (if P v then 1 else 0) / 2 := by
  have h := sum_halfMix_mul u v (fun z ↦ if P z then (1 : ℝ) else 0)
  simp only [mul_boole] at h
  rw [sum_filter]
  exact h

/-- The mixture has total mass one. -/
theorem sum_halfMix (u v : H) : ∑ z, halfMix u v z = 1 := by
  have h := sum_halfMix_mul u v (fun _ ↦ (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  norm_num

/-- **The population map at a two-point population**: `R_K(½δ_u + ½δ_v)` is the average of the
four ordered parental pairs. -/
theorem reproduce_halfMix (K : H → H → H → ℝ) (u v z : H) :
    reproduce K (halfMix u v) z = (K u u z + K u v z + K v u z + K v v z) / 4 := by
  have hin : ∀ x, ∑ y, halfMix u v x * halfMix u v y * K x y z =
      halfMix u v x * (K x u z / 2 + K x v z / 2) := by
    intro x
    calc ∑ y, halfMix u v x * halfMix u v y * K x y z
        = halfMix u v x * ∑ y, halfMix u v y * K x y z := by
          rw [mul_sum]
          exact sum_congr rfl fun y _ ↦ by ring
      _ = halfMix u v x * (K x u z / 2 + K x v z / 2) := by
          rw [sum_halfMix_mul u v fun y ↦ K x y z]
  unfold reproduce
  simp only [hin]
  calc ∑ x, halfMix u v x * (K x u z / 2 + K x v z / 2)
      = (K u u z / 2 + K u v z / 2) / 2 + (K v u z / 2 + K v v z / 2) / 2 :=
        sum_halfMix_mul u v fun x ↦ K x u z / 2 + K x v z / 2
    _ = (K u u z + K u v z + K v u z + K v v z) / 4 := by ring

/-- An observable's mean after one generation from a two-point population, pair by pair. -/
theorem sum_reproduce_halfMix_mul (K : H → H → H → ℝ) (u v : H) (g : H → ℝ) :
    ∑ z, reproduce K (halfMix u v) z * g z =
      (∑ z, K u u z * g z + ∑ z, K u v z * g z + ∑ z, K v u z * g z +
        ∑ z, K v v z * g z) / 4 := by
  simp only [reproduce_halfMix, div_mul_eq_mul_div, add_mul, ← sum_div, sum_add_distrib]

end Mixture

/-! ### The checked-exchange model (§4) -/

/-- **A checking graph** on the features `V`: directed edges `i → j`, each with a positive rate
`r_ij`. An edge permits recombination at its target `i` when the parents agree at its checker
`j`. -/
structure CheckingGraph (V : Type*) where
  /-- The directed edges `(i, j)`, target first. -/
  edges : Finset (V × V)
  /-- The rate `r_ij` of each edge. -/
  rate : V × V → ℝ
  /-- Every edge has a positive rate. -/
  rate_pos : ∀ e ∈ edges, 0 < rate e

section Model

variable {V : Type*}

/-- The total rate `R = ∑_{i → j} r_ij`. -/
def CheckingGraph.totalRate (G : CheckingGraph V) : ℝ :=
  ∑ e ∈ G.edges, G.rate e

/-- A graph with an edge has positive total rate. -/
theorem CheckingGraph.totalRate_pos (G : CheckingGraph V) (h : G.edges.Nonempty) :
    0 < G.totalRate :=
  sum_pos G.rate_pos h

/-- The graph with the single edge `i → j` at unit rate. -/
def singleEdge (i j : V) : CheckingGraph V where
  edges := {(i, j)}
  rate _ := 1
  rate_pos _ _ := one_pos

variable [DecidableEq V]

/-- **The ordered child (4.1)**, `T_ij(x,y)`: the genome `x`, except that it takes `y_i` at the
target `i` exactly when the parents agree at the checker `j`. -/
def orderedChild (i j : V) (x y : V → Bool) : V → Bool :=
  fun k ↦ if k = i ∧ x j = y j then y i else x k

/-- **An exchange permutes the parental values at every coordinate**: the indicators of allele
`a` in the two ordered children add up to those in the two parents. -/
theorem orderedChild_indicator_add (i j k : V) (x y : V → Bool) (a : Bool) :
    (if orderedChild i j x y k = a then (1 : ℝ) else 0) +
        (if orderedChild i j y x k = a then 1 else 0) =
      (if x k = a then 1 else 0) + (if y k = a then 1 else 0) := by
  by_cases hk : k = i
  · by_cases hxy : x j = y j
    · have h1 : orderedChild i j x y k = y k := by simp [orderedChild, hk, hxy]
      have h2 : orderedChild i j y x k = x k := by simp [orderedChild, hk, hxy.symm]
      rw [h1, h2, add_comm]
    · have h1 : orderedChild i j x y k = x k := by simp [orderedChild, hxy]
      have h2 : orderedChild i j y x k = y k := by simp [orderedChild, Ne.symm hxy]
      rw [h1, h2]
  · have h1 : orderedChild i j x y k = x k := by simp [orderedChild, hk]
    have h2 : orderedChild i j y x k = y k := by simp [orderedChild, hk]
    rw [h1, h2]

variable [Fintype V]

/-- **The exchange kernel (4.2)**, `K_ij(x,y) = ½δ_{T_ij(x,y)} + ½δ_{T_ij(y,x)}`. -/
def exchangeKernel (i j : V) (x y : V → Bool) : (V → Bool) → ℝ :=
  halfMix (orderedChild i j x y) (orderedChild i j y x)

/-- The allele law `p{z : z_k = a}` of a mass function at the feature `k`; `featureMass p k true`
is the note's `p_k`. -/
def featureMass (p : (V → Bool) → ℝ) (k : V) (a : Bool) : ℝ :=
  ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a), p z

/-- The allele law at a feature is the pushforward along that coordinate. -/
theorem featureMass_eq_pushforward (p : (V → Bool) → ℝ) (k : V) (a : Bool) :
    featureMass p k a = pushforward (fun z : V → Bool ↦ z k) p a :=
  rfl

/-- One exchange kernel is neutral at every feature. -/
theorem exchangeKernel_marginal (i j k : V) (a : Bool) (x y : V → Bool) :
    ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a), exchangeKernel i j x y z =
      (if x k = a then 1 else 0) / 2 + (if y k = a then 1 else 0) / 2 := by
  have h := orderedChild_indicator_add i j k x y a
  simp only [exchangeKernel, sum_filter_halfMix]
  linarith

/-- **The compatibility kernel (4.3)**, `K_G = (1/R) ∑_{i → j} r_ij K_ij`, and unbiased parental
copying `½δ_x + ½δ_y` when the graph has no edges. -/
def compatibilityKernel (G : CheckingGraph V) (x y z : V → Bool) : ℝ :=
  if G.edges = ∅ then halfMix x y z
  else (∑ e ∈ G.edges, G.rate e * exchangeKernel e.1 e.2 x y z) / G.totalRate

/-- With no edges the compatibility kernel is unbiased parental copying. -/
theorem compatibilityKernel_of_eq_empty (G : CheckingGraph V) (h : G.edges = ∅)
    (x y z : V → Bool) : compatibilityKernel G x y z = halfMix x y z :=
  if_pos h

/-- With edges the compatibility kernel is the rate-weighted average of the exchange kernels. -/
theorem compatibilityKernel_of_ne_empty (G : CheckingGraph V) (h : G.edges ≠ ∅)
    (x y z : V → Bool) :
    compatibilityKernel G x y z =
      (∑ e ∈ G.edges, G.rate e * exchangeKernel e.1 e.2 x y z) / G.totalRate :=
  if_neg h

/-- The one-edge graph's compatibility kernel is that edge's exchange kernel. -/
theorem compatibilityKernel_singleEdge (i j : V) (x y z : V → Bool) :
    compatibilityKernel (singleEdge i j) x y z = exchangeKernel i j x y z := by
  rw [compatibilityKernel_of_ne_empty _ (singleton_ne_empty _)]
  simp [singleEdge, CheckingGraph.totalRate]

/-- **Theorem 3 (4.4): every feature is exactly neutral.** For every checking graph, feature `k`,
allele `a` and parental pair, `K_G(x,y; {z : z_k = a}) = ½·1{x_k = a} + ½·1{y_k = a}`. -/
theorem compatibilityKernel_marginal (G : CheckingGraph V) (k : V) (a : Bool) (x y : V → Bool) :
    ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a), compatibilityKernel G x y z =
      (if x k = a then 1 else 0) / 2 + (if y k = a then 1 else 0) / 2 := by
  by_cases h : G.edges = ∅
  · simp only [compatibilityKernel_of_eq_empty G h]
    exact sum_filter_halfMix x y _
  · have hR : G.totalRate ≠ 0 := (G.totalRate_pos (nonempty_iff_ne_empty.mpr h)).ne'
    simp only [compatibilityKernel_of_ne_empty G h]
    rw [← sum_div, sum_comm]
    simp only [← mul_sum, exchangeKernel_marginal, ← sum_mul]
    rw [mul_comm, mul_div_assoc]
    change _ * (G.totalRate / G.totalRate) = _
    rw [div_self hR, mul_one]

/-- A kernel that is neutral at feature `k` for allele `a` keeps the population's mass on
`{z : z_k = a}`, for every population of total mass one. -/
theorem featureMass_reproduce_of_marginal (K : (V → Bool) → (V → Bool) → (V → Bool) → ℝ)
    (k : V) (a : Bool)
    (hK : ∀ x y, ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a), K x y z =
      (if x k = a then 1 else 0) / 2 + (if y k = a then 1 else 0) / 2)
    (p : (V → Bool) → ℝ) (hp : ∑ z, p z = 1) :
    featureMass (reproduce K p) k a = featureMass p k a := by
  have hm : featureMass p k a = ∑ x, p x * (if x k = a then 1 else 0) := by
    simp only [featureMass, sum_filter, mul_boole]
  have hsplit : ∀ x y, p x * p y *
      ((if x k = a then (1 : ℝ) else 0) / 2 + (if y k = a then 1 else 0) / 2) =
      p x * (if x k = a then 1 else 0) * p y / 2 +
        p x * (p y * (if y k = a then 1 else 0)) / 2 := by
    intro x y
    ring
  rw [hm, featureMass, sum_block_reproduce]
  simp only [hK, hsplit, sum_add_distrib, ← sum_div, ← mul_sum, ← sum_mul, hp, mul_one, one_mul]
  ring

/-- **Theorem 3, population form**: `(R_{K_G}(p))_k = p_k`. One generation of the compatibility
kernel leaves the allele law at every feature unchanged, for every population of total mass
one. -/
theorem featureMass_reproduce_compatibilityKernel (G : CheckingGraph V) (p : (V → Bool) → ℝ)
    (hp : ∑ z, p z = 1) (k : V) (a : Bool) :
    featureMass (reproduce (compatibilityKernel G) p) k a = featureMass p k a :=
  featureMass_reproduce_of_marginal _ k a (compatibilityKernel_marginal G k a) p hp

/-- The allele law of a nonnegative population is nonnegative. -/
theorem featureMass_nonneg (p : (V → Bool) → ℝ) (hp : ∀ z, 0 ≤ p z) (k : V) (a : Bool) :
    0 ≤ featureMass p k a :=
  sum_nonneg fun z _ ↦ hp z

/-- The allele law of a probability vector is at most one. -/
theorem featureMass_le_one (p : (V → Bool) → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp : ∑ z, p z = 1)
    (k : V) (a : Bool) : featureMass p k a ≤ 1 := by
  rw [← hp]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ ↦ hp0 z

/-! ### The finite population (§4.1) -/

/-- **The finite-population law (4.5)**, `Q_N(p) = (1 - R/N) p + (1/N) ∑_{i → j} r_ij R_{K_ij}(p)`,
for a population of `N ≥ R` offspring. -/
def finitePopulationLaw (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ) (z : V → Bool) : ℝ :=
  (1 - G.totalRate / N) * p z +
    (∑ e ∈ G.edges, G.rate e * reproduce (exchangeKernel e.1 e.2) p z) / N

/-- **The finite-population law keeps every allele law**: the allele-`a` probability at feature
`k` under `Q_N(p)` is that under `p`. -/
theorem featureMass_finitePopulationLaw (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (hp : ∑ z, p z = 1) (k : V) (a : Bool) :
    featureMass (finitePopulationLaw G N p) k a = featureMass p k a := by
  have hK : ∀ e : V × V, ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a),
      reproduce (exchangeKernel e.1 e.2) p z =
        ∑ z ∈ univ.filter (fun z : V → Bool ↦ z k = a), p z :=
    fun e ↦ featureMass_reproduce_of_marginal _ k a (exchangeKernel_marginal e.1 e.2 k a) p hp
  simp only [featureMass, finitePopulationLaw, sum_add_distrib, ← mul_sum, ← sum_div]
  rw [sum_comm]
  simp only [← mul_sum, hK, ← sum_mul]
  simp only [CheckingGraph.totalRate]
  ring

/-- `Q_N(p)` is nonnegative when `R ≤ N` and `p` is nonnegative. -/
theorem finitePopulationLaw_nonneg (G : CheckingGraph V) (N : ℕ) (hN : G.totalRate ≤ N)
    (p : (V → Bool) → ℝ) (hp : ∀ z, 0 ≤ p z) (z : V → Bool) :
    0 ≤ finitePopulationLaw G N p z := by
  have hR : G.totalRate / N ≤ 1 := div_le_one_of_le₀ hN (Nat.cast_nonneg N)
  have hsum : 0 ≤ ∑ e ∈ G.edges, G.rate e * reproduce (exchangeKernel e.1 e.2) p z :=
    sum_nonneg fun e he ↦ mul_nonneg (G.rate_pos e he).le
      (reproduce_nonneg _ (fun x y w ↦ halfMix_nonneg _ _ w) p hp z)
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hR) (hp z)) (div_nonneg hsum (Nat.cast_nonneg N))

/-- `Q_N(p)` has total mass one when `p` does. -/
theorem sum_finitePopulationLaw (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (hp : ∑ z, p z = 1) : ∑ z, finitePopulationLaw G N p z = 1 := by
  have hK : ∀ e : V × V, ∑ z, reproduce (exchangeKernel e.1 e.2) p z = 1 := fun e ↦ by
    rw [sum_reproduce (exchangeKernel e.1 e.2) p fun x y ↦ sum_halfMix _ _, hp, one_pow]
  simp only [finitePopulationLaw, sum_add_distrib, ← mul_sum, ← sum_div]
  rw [sum_comm]
  simp only [← mul_sum, hK, hp, mul_one]
  simp only [CheckingGraph.totalRate]
  ring

/-- **The exact binomial law (4.6), as a finite sum.** Under `N` i.i.d. offspring drawn from
`Q_N(p)`, the number carrying allele `1` at feature `k` is `c` with mass
`C(N,c) p_k^c (1 - p_k)^(N-c)`, whatever the checking graph. -/
theorem sum_offspringCount (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (hp : ∑ z, p z = 1) (k : V) (c : ℕ) :
    ∑ z ∈ univ.filter (fun z : Fin N → V → Bool ↦ #(univ.filter fun i ↦ z i k = true) = c),
        ∏ i, finitePopulationLaw G N p (z i) =
      N.choose c * featureMass p k true ^ c * (1 - featureMass p k true) ^ (N - c) := by
  refine (sum_prod_filter_card_eq_choose (finitePopulationLaw G N p)
    (sum_finitePopulationLaw G N p hp) (fun z : V → Bool ↦ z k = true) N c).trans ?_
  change (N.choose c : ℝ) * featureMass (finitePopulationLaw G N p) k true ^ c *
    (1 - featureMass (finitePopulationLaw G N p) k true) ^ (N - c) = _
  rw [featureMass_finitePopulationLaw G N p hp k true]

end Model

/-- Mathlib's binomial mass function, read as a real number. -/
theorem binomial_toReal (ρ : ℝ≥0) (hρ : ρ ≤ 1) (N : ℕ) (c : Fin (N + 1)) :
    (PMF.binomial ρ hρ N c).toReal =
      N.choose c * (ρ : ℝ) ^ (c : ℕ) * (1 - (ρ : ℝ)) ^ (N - c) := by
  simp only [PMF.binomial, PMF.ofFintype_apply, ENNReal.coe_toReal, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_sub hρ, NNReal.coe_one, NNReal.coe_natCast, Fin.val_last]
  ring

section Binomial

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **The exact binomial law (4.6)**: `N p'_k | p ~ Binomial(N, p_k)`. The product-law mass of
each allele-`1` count at feature `k` among `N` i.i.d. offspring from `Q_N(p)` is Mathlib's
`PMF.binomial` at `p_k`. So the marginal frequency process is the ordinary Wright-Fisher chain,
independently of the checking graph. -/
theorem offspringCount_eq_binomial (G : CheckingGraph V) (N : ℕ) (p : (V → Bool) → ℝ)
    (hp : ∑ z, p z = 1) (k : V) (ρ : ℝ≥0) (hρ : ρ ≤ 1) (hρp : (ρ : ℝ) = featureMass p k true)
    (c : Fin (N + 1)) :
    ∑ z ∈ univ.filter (fun z : Fin N → V → Bool ↦ #(univ.filter fun i ↦ z i k = true) = c),
        ∏ i, finitePopulationLaw G N p (z i) =
      (PMF.binomial ρ hρ N c).toReal := by
  rw [sum_offspringCount G N p hp k c, binomial_toReal, hρp]

end Binomial

/-! ### The eight-state witness (§5.2) -/

section Witness

/-- The witness rule "exchange `a` only when the parents agree at `h`", with the features
`(a, b, h)` numbered `(0, 1, 2)`: the single edge `0 → 2` at unit rate. -/
def witnessGraph : CheckingGraph (Fin 3) :=
  singleEdge 0 2

/-- The observation `(a, b)` of a genome. -/
def observeAB (z : Fin 3 → Bool) : Bool × Bool :=
  (z 0, z 1)

/-- The observed product `ab`: the indicator that both observed features carry allele `1`. -/
def observedProduct (z : Fin 3 → Bool) : ℝ :=
  if z 0 = true ∧ z 1 = true then 1 else 0

/-- The population `p = ½δ_(0,0,0) + ½δ_(1,1,0)`. -/
def witnessP : (Fin 3 → Bool) → ℝ :=
  halfMix ![false, false, false] ![true, true, false]

/-- The population `q = ½δ_(0,0,0) + ½δ_(1,1,1)`. -/
def witnessQ : (Fin 3 → Bool) → ℝ :=
  halfMix ![false, false, false] ![true, true, true]

/-- The two witness populations have the same observed law `½δ_00 + ½δ_11`. -/
theorem witness_pushforward_eq :
    pushforward observeAB witnessP = pushforward observeAB witnessQ := by
  funext o
  have hobs : observeAB ![true, true, false] = observeAB ![true, true, true] := rfl
  simp only [pushforward, witnessP, witnessQ, sum_filter_halfMix, hobs]

/-- The observed mass at `(1, 1)` is the mean of the observed product. -/
theorem pushforward_observeAB_true_true (f : (Fin 3 → Bool) → ℝ) :
    pushforward observeAB f (true, true) = ∑ z, f z * observedProduct z := by
  rw [pushforward, sum_filter]
  refine sum_congr rfl fun z _ ↦ ?_
  simp [observeAB, observedProduct]

/-- Both witness populations have `E[ab] = 1/2`. -/
theorem witness_observed :
    ∑ z, witnessP z * observedProduct z = 1 / 2 ∧
      ∑ z, witnessQ z * observedProduct z = 1 / 2 := by
  constructor <;>
    simp only [witnessP, witnessQ, sum_halfMix_mul] <;>
    norm_num [observedProduct, Matrix.cons_val]

/-- The checker coordinate `h` of the three witness genomes: `0` in `000` and `110`, `1` in
`111`. -/
theorem witness_checker_values :
    (![false, false, false] : Fin 3 → Bool) 2 = false ∧
      (![true, true, false] : Fin 3 → Bool) 2 = false ∧
        (![true, true, true] : Fin 3 → Bool) 2 = true :=
  ⟨rfl, rfl, rfl⟩

/-- After one generation, `E[ab]` is `1/4` from `p` and `1/2` from `q`. -/
theorem witness_expected :
    ∑ z, reproduce (compatibilityKernel witnessGraph) witnessP z * observedProduct z = 1 / 4 ∧
      ∑ z, reproduce (compatibilityKernel witnessGraph) witnessQ z * observedProduct z =
        1 / 2 := by
  constructor <;>
    simp only [witnessP, witnessQ, witnessGraph, sum_reproduce_halfMix_mul,
      compatibilityKernel_singleEdge, exchangeKernel, sum_halfMix_mul] <;>
    norm_num [observedProduct, orderedChild, witness_checker_values.1,
      witness_checker_values.2.1, witness_checker_values.2.2]

/-- **The drifts (5.5)**: at unit event rate, `R_K(p)[ab] - p[ab] = -1/4` and
`R_K(q)[ab] - q[ab] = 0`, although `p` and `q` have the same observed law. -/
theorem witness_drift :
    ∑ z, reproduce (compatibilityKernel witnessGraph) witnessP z * observedProduct z -
        ∑ z, witnessP z * observedProduct z = -1 / 4 ∧
      ∑ z, reproduce (compatibilityKernel witnessGraph) witnessQ z * observedProduct z -
        ∑ z, witnessQ z * observedProduct z = 0 := by
  rw [witness_expected.1, witness_expected.2, witness_observed.1, witness_observed.2]
  norm_num

/-- **No two-feature transition law gives both answers.** No map on observed laws of `(a, b)`
sends the observed law of each witness population to the observed law of its next generation. -/
theorem witness_no_observed_transition_law :
    ¬ ∃ F : ((Bool × Bool) → ℝ) → (Bool × Bool) → ℝ,
      F (pushforward observeAB witnessP) =
          pushforward observeAB (reproduce (compatibilityKernel witnessGraph) witnessP) ∧
        F (pushforward observeAB witnessQ) =
          pushforward observeAB (reproduce (compatibilityKernel witnessGraph) witnessQ) := by
  rintro ⟨F, hp, hq⟩
  rw [witness_pushforward_eq, hq] at hp
  have h := congrFun hp (true, true)
  rw [pushforward_observeAB_true_true, pushforward_observeAB_true_true, witness_expected.1,
    witness_expected.2] at h
  norm_num at h

/-- **The observation `(a, b)` is not hereditarily autonomous (2.2).** No kernel `K̄` on observed
states satisfies `K_G(x,y; π⁻¹(o)) = K̄(πx, πy; o)` for the witness rule. -/
theorem witness_not_autonomous :
    ¬ ∃ Kbar : (Bool × Bool) → (Bool × Bool) → (Bool × Bool) → ℝ, ∀ x y o,
      ∑ z ∈ univ.filter (fun z ↦ observeAB z = o), compatibilityKernel witnessGraph x y z =
        Kbar (observeAB x) (observeAB y) o := by
  rintro ⟨Kbar, hK⟩
  have h := (hK ![false, false, false] ![true, true, false] (true, true)).trans
    (hK ![false, false, false] ![true, true, true] (true, true)).symm
  simp only [witnessGraph, compatibilityKernel_singleEdge, exchangeKernel,
    sum_filter_halfMix] at h
  norm_num [observeAB, orderedChild, witness_checker_values.1, witness_checker_values.2.1,
    witness_checker_values.2.2] at h

end Witness

end

end Descent.Pangenome.AncestralLocality

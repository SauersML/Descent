/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.FiniteGenomeAncestry
import Mathlib.Algebra.BigOperators.Fin

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Ancestral decisions: sampling observables, substitutions and support tags

The research note "Ancestral locality" (§7) reads the neutral checking model backwards in time. A
population is a vector `p` on a finite state space `H`, and an observation of `n` sampled genomes
is a function `f : (Fin n → H) → ℝ`. Its sampling observable `H_f(p) = ∑_x f(x) ∏_a p(x_a)`
(7.2) is `samplingObservable f p`. The backward process never touches `p`: it rewrites `f` by two
substitutions.

* **Coalescence** `C_ab` identifies two arguments: `coalesceArguments a b f` feeds the genome of
  argument `b` to argument `a` as well. On a vector of total mass one its observable is the
  diagonal sum `∑_{x_a = x_b} f(x) ∏_{c ≠ a} p(x_c)` (`samplingObservable_coalesceArguments`),
  symmetric in the two arguments (`samplingObservable_coalesceArguments_comm`).
* **Decision branching** `B_{a,T}` (7.3) replaces argument `a` by the child `T(x_a, x_{n+1})` of
  its own genome and a new parental genome: `decisionBranch T a f`. Its observable sums the new
  parent out (`samplingObservable_decisionBranch`), and when `f` cannot see what the rule changes
  the event is invisible (`samplingObservable_decisionBranch_of_agree`).

The sampling identity (7.4) says that an ordered rule and its exchange kernel
`K_T(x,y) = ½δ_{T(x,y)} + ½δ_{T(y,x)}` (`exchangeKernel`, the note's (4.2)) have the same
expectations against `p ⊗ p` (`sampling_identity`).

For the checking rule (4.1), `checkedTransfer i j` ("copy coordinate `i` from the second parent
when the parents agree at `j`"), §7.3 attaches a support tag `A_a ⊆ V` to every argument.
`TagDetermined f A` says `f` reads argument `a` only at the coordinates `A a`; observing a set `A`
of coordinates in every sampled genome is such a state (`tagDetermined_restrict`). The updates
(7.6) are `decisionTags` and `coalesceTags`:

* a decision at a target `i ∉ A_a` is omitted: the new parent gets an empty tag, and on a vector
  of total mass one the observable does not move (`samplingObservable_decisionBranch_of_not_mem`);
* a decision at a target `i ∈ A_a` adds the checker `j` to `A_a` and gives the new parent the
  support `{i, j}`;
* coalescence gives the surviving argument the union of the two supports.

After each update the substituted observable is determined by the updated tags
(`tagDetermined_coalesceArguments`, `tagDetermined_decisionBranch`). The support count
`Z = ∑_a |A_a|` (`tagCount`) rises by at most three at a decision (`tagCount_decisionTags_le`)
and does not rise at a coalescence (`tagCount_coalesceTags_le`). A nonnegative coordinate weight
rises by at most `w(i) + 2w(j)` at a decision (`tagWeight_decisionTags_le`) and does not rise at a
coalescence (`tagWeight_coalesceTags_le`): the two increments behind the note's Theorems 7 and 8.
The total rate of the decisions that are not omitted is at most `D Z` when the outgoing rates of
every target sum to at most `D` (`decisionRate_le`). On a genome of `L` coordinates a tag state is
a set of ancestral material in the sense of `Descent.Coalescent.FiniteGenomeAncestry`, of size `Z`
(`card_tagMaterial`).

Scope. The note's neutral-model module is not on main when this file is written, so the checked
transfer (4.1) and the exchange kernel (4.2) are defined here from the note. A coalesced
observable keeps its arity and leaves argument `a` unread, so it agrees with the note's
`(n - 1)`-argument observable on vectors of total mass one only. The forward generator (7.1), the
generator identity of Theorem 6, the backward jump process, its nonexplosion and the semigroup
form (7.5) are not in this file.

## Empirical status

None. The bodies here are finite sums and set updates over a supplied state space, rule, rate
table and vector, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

variable {H : Type*} {n : ℕ}

/-! ### Sampling observables and the two substitutions -/

/-- **The sampling observable (7.2)** `H_f(p) = ∑_x f(x) ∏_a p(x_a)`: the expectation of `f` at `n`
genomes sampled independently from `p`. It is a polynomial in the entries of `p`, defined at every
vector and not only at probability vectors. -/
def samplingObservable [Fintype H] (f : (Fin n → H) → ℝ) (p : H → ℝ) : ℝ :=
  ∑ w, f w * ∏ a, p (w a)

/-- **Coalescence `C_ab`.** The genome of argument `b` is fed to argument `a` as well, so the two
arguments become one ancestor. Argument `a` of the result is not read. -/
def coalesceArguments (a b : Fin n) (f : (Fin n → H) → ℝ) : (Fin n → H) → ℝ :=
  fun w ↦ f (Function.update w a (w b))

/-- **Decision branching `B_{a,T}` (7.3).** Argument `a` is replaced by the child `T(x_a, x_{n+1})`
of its own genome and a new parental genome in the last argument. -/
def decisionBranch (T : H → H → H) (a : Fin n) (f : (Fin n → H) → ℝ) :
    (Fin (n + 1) → H) → ℝ :=
  fun u ↦ f (Function.update (Fin.init u) a (T (u a.castSucc) (u (Fin.last n))))

/-- **The exchange kernel (4.2)** of an ordered rule: the child is `T(x, y)` or `T(y, x)`, each
with probability one half. -/
def exchangeKernel [DecidableEq H] (T : H → H → H) (x y z : H) : ℝ :=
  ((if T x y = z then 1 else 0) + (if T y x = z then 1 else 0)) / 2

/-- **The sampling identity (7.4).** Against `p ⊗ p` an ordered rule and its exchange kernel give
the same expectation of every function of the child, `∬ ∑_z K_T(x,y;z) φ(z) = ∬ φ(T(x,y))`: the
two orders of the parents are exchangeable under the product law, and exchanging them is all the
symmetrization does. -/
theorem sampling_identity [Fintype H] [DecidableEq H] (T : H → H → H) (p φ : H → ℝ) :
    ∑ x, ∑ y, p x * p y * ∑ z, exchangeKernel T x y z * φ z =
      ∑ x, ∑ y, p x * p y * φ (T x y) := by
  have hkernel : ∀ x y, ∑ z, exchangeKernel T x y z * φ z = (φ (T x y) + φ (T y x)) / 2 := by
    intro x y
    have hterm : ∀ z, exchangeKernel T x y z * φ z =
        ((if T x y = z then φ z else 0) + (if T y x = z then φ z else 0)) / 2 := by
      intro z
      simp only [exchangeKernel]
      split_ifs <;> ring
    simp only [hterm, ← sum_div, sum_add_distrib, sum_ite_eq, mem_univ, if_true]
  have hswap : ∑ x, ∑ y, p x * p y * φ (T y x) = ∑ x, ∑ y, p x * p y * φ (T x y) := by
    rw [sum_comm]
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    ring
  have hsplit : ∑ x, ∑ y, p x * p y * ∑ z, exchangeKernel T x y z * φ z =
      (∑ x, ∑ y, p x * p y * φ (T x y) + ∑ x, ∑ y, p x * p y * φ (T y x)) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [hkernel]
    ring
  rw [hsplit, hswap]
  ring

/-- Summing over `n + 1` genomes is summing over the first `n` and then over the last. -/
theorem sum_tuple_snoc [Fintype H] (F : (Fin (n + 1) → H) → ℝ) :
    ∑ u, F u = ∑ w : Fin n → H, ∑ y, F (Fin.snoc w y) := by
  calc ∑ u, F u = ∑ x : H × (Fin n → H), F (Fin.snoc x.2 x.1) :=
        (Fintype.sum_equiv (Fin.snocEquiv fun _ ↦ H) _ _ fun _ ↦ rfl).symm
    _ = ∑ y, ∑ w : Fin n → H, F (Fin.snoc w y) := Fintype.sum_prod_type _
    _ = ∑ w : Fin n → H, ∑ y, F (Fin.snoc w y) := sum_comm

/-- **The branched observable sums the new parent out**: argument `a` is the child of its own
genome and a parental genome `y` drawn from `p`. -/
theorem samplingObservable_decisionBranch [Fintype H] (T : H → H → H) (a : Fin n)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (decisionBranch T a f) p =
      ∑ w, ∑ y, f (Function.update w a (T (w a) y)) * (∏ c, p (w c)) * p y := by
  rw [samplingObservable, sum_tuple_snoc]
  refine sum_congr rfl fun w _ ↦ sum_congr rfl fun y _ ↦ ?_
  simp only [decisionBranch, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.prod_univ_castSucc]
  ring

/-- **Moving a coordinate constraint.** Resetting argument `a` is a bijection between the tuples
with `x_a = φ(x)` and the tuples with `x_a = h`, when `φ` does not read argument `a`. -/
theorem sum_filter_update [Fintype H] [DecidableEq H] (a : Fin n) (φ : (Fin n → H) → H)
    (hφ : ∀ w h, φ (Function.update w a h) = φ w) (h : H) (G : (Fin n → H) → ℝ) :
    ∑ w ∈ univ.filter (fun w ↦ w a = φ w), G w =
      ∑ w ∈ univ.filter (fun w ↦ w a = h), G (Function.update w a (φ w)) := by
  refine sum_nbij' (fun w ↦ Function.update w a h) (fun w ↦ Function.update w a (φ w))
    (fun w _ ↦ by simp) (fun w _ ↦ by simp [hφ]) (fun w hw ↦ ?_) (fun w hw ↦ ?_)
    (fun w hw ↦ ?_)
  · rw [mem_filter] at hw
    dsimp only
    rw [hφ, Function.update_idem, ← hw.2, Function.update_eq_self]
  · rw [mem_filter] at hw
    dsimp only
    rw [Function.update_idem, ← hw.2, Function.update_eq_self]
  · rw [mem_filter] at hw
    dsimp only
    rw [hφ, Function.update_idem, ← hw.2, Function.update_eq_self]

/-- **The coalesced observable is a diagonal sum.** On a vector of total mass one, feeding the
genome of argument `b` to argument `a` gives `∑_{x_a = x_b} f(x) ∏_{c ≠ a} p(x_c)`: the unread
argument integrates to one. -/
theorem samplingObservable_coalesceArguments [Fintype H] [DecidableEq H] {a b : Fin n}
    (hab : a ≠ b) (f : (Fin n → H) → ℝ) {p : H → ℝ} (hp : ∑ h, p h = 1) :
    samplingObservable (coalesceArguments a b f) p =
      ∑ w, if w a = w b then f w * ∏ c ∈ univ.erase a, p (w c) else 0 := by
  have hrest : ∀ w h, ∏ c ∈ univ.erase a, p (Function.update w a h c) =
      ∏ c ∈ univ.erase a, p (w c) := fun w h ↦
    prod_congr rfl fun c hc ↦ by rw [Function.update_of_ne (ne_of_mem_erase hc)]
  have hfiber : ∀ h, ∑ w ∈ univ.filter (fun w ↦ w a = h),
      f (Function.update w a (w b)) * ∏ c ∈ univ.erase a, p (w c) =
        ∑ w ∈ univ.filter (fun w ↦ w a = w b), f w * ∏ c ∈ univ.erase a, p (w c) := by
    intro h
    refine Eq.trans ?_ (sum_filter_update a (fun w ↦ w b)
      (fun w h' ↦ Function.update_of_ne hab.symm h' w) h
      fun w ↦ f w * ∏ c ∈ univ.erase a, p (w c)).symm
    refine sum_congr rfl fun w _ ↦ ?_
    simp only [hrest]
  calc samplingObservable (coalesceArguments a b f) p
      = ∑ w, ∑ h, if w a = h then
          p h * (f (Function.update w a (w b)) * ∏ c ∈ univ.erase a, p (w c)) else 0 := by
        refine sum_congr rfl fun w _ ↦ ?_
        rw [sum_ite_eq, if_pos (mem_univ _),
          ← mul_prod_erase univ (fun c ↦ p (w c)) (mem_univ a)]
        simp only [coalesceArguments]
        ring
    _ = ∑ h, p h * ∑ w ∈ univ.filter (fun w ↦ w a = h),
          f (Function.update w a (w b)) * ∏ c ∈ univ.erase a, p (w c) := by
        rw [sum_comm]
        refine sum_congr rfl fun h _ ↦ ?_
        rw [mul_sum, sum_filter]
    _ = ∑ h, p h * ∑ w ∈ univ.filter (fun w ↦ w a = w b),
          f w * ∏ c ∈ univ.erase a, p (w c) := by
        simp only [hfiber]
    _ = ∑ w, if w a = w b then f w * ∏ c ∈ univ.erase a, p (w c) else 0 := by
        rw [← sum_mul, hp, one_mul, sum_filter]

/-- **Coalescence is symmetric.** On a vector of total mass one it does not matter which of the two
arguments survives. -/
theorem samplingObservable_coalesceArguments_comm [Fintype H] [DecidableEq H] {a b : Fin n}
    (hab : a ≠ b) (f : (Fin n → H) → ℝ) {p : H → ℝ} (hp : ∑ h, p h = 1) :
    samplingObservable (coalesceArguments a b f) p =
      samplingObservable (coalesceArguments b a f) p := by
  rw [samplingObservable_coalesceArguments hab f hp,
    samplingObservable_coalesceArguments hab.symm f hp]
  refine sum_congr rfl fun w _ ↦ ?_
  by_cases hw : w a = w b
  · have h1 : ∏ c ∈ univ.erase a, p (w c) = p (w b) * ∏ c ∈ (univ.erase a).erase b, p (w c) :=
      (mul_prod_erase _ (fun c ↦ p (w c)) (mem_erase.mpr ⟨hab.symm, mem_univ b⟩)).symm
    have h2 : ∏ c ∈ univ.erase b, p (w c) = p (w a) * ∏ c ∈ (univ.erase b).erase a, p (w c) :=
      (mul_prod_erase _ (fun c ↦ p (w c)) (mem_erase.mpr ⟨hab, mem_univ a⟩)).symm
    rw [if_pos hw, if_pos hw.symm, h1, h2, erase_right_comm, hw]
  · rw [if_neg hw, if_neg fun h ↦ hw h.symm]

/-- **An event the observation cannot see is invisible.** If replacing argument `a` by its child
never changes `f`, the branched observable on a vector of total mass one is the original. -/
theorem samplingObservable_decisionBranch_of_agree [Fintype H] (T : H → H → H) {a : Fin n}
    {f : (Fin n → H) → ℝ} (hT : ∀ w y, f (Function.update w a (T (w a) y)) = f w)
    {p : H → ℝ} (hp : ∑ h, p h = 1) :
    samplingObservable (decisionBranch T a f) p = samplingObservable f p := by
  rw [samplingObservable_decisionBranch, samplingObservable]
  simp only [hT, ← mul_sum, hp, mul_one]

/-! ### The checking rule and support tags -/

variable {V : Type*}

/-- **The checked transfer (4.1).** The child is the first parent, except that coordinate `i` is
copied from the second parent when the two parents agree at the checker `j`. -/
def checkedTransfer [DecidableEq V] (i j : V) (x y : V → Bool) : V → Bool :=
  fun k ↦ if k = i ∧ x j = y j then y i else x k

/-- The checked transfer changes nothing away from its target. -/
theorem checkedTransfer_of_ne [DecidableEq V] {i k : V} (j : V) (hk : k ≠ i) (x y : V → Bool) :
    checkedTransfer i j x y k = x k :=
  if_neg fun h ↦ hk h.1

/-- **The support-tag condition (§7.3).** `f` reads argument `a` only at the coordinates `A a`:
two tuples of genomes that agree there give the same value. -/
def TagDetermined (f : (Fin n → V → Bool) → ℝ) (A : Fin n → Finset V) : Prop :=
  ∀ w w' : Fin n → V → Bool, (∀ a, ∀ v ∈ A a, w a v = w' a v) → f w = f w'

/-- **The initial tag state.** Observing the coordinates `A` of every sampled genome reads each
argument only at `A`, so every argument starts with the tag `A`, as in the note's `Z_0 = n|A|`. -/
theorem tagDetermined_restrict (A : Finset V) (g : (Fin n → A → Bool) → ℝ) :
    TagDetermined (fun w ↦ g fun c v ↦ w c v) fun _ ↦ A := by
  intro w w' hw
  exact congrArg g (funext fun c ↦ funext fun v ↦ hw c v.1 v.2)

/-- **Coalescence tags.** The surviving argument `b` needs the union of the two supports, and the
unread argument `a` needs nothing. -/
def coalesceTags [DecidableEq V] (a b : Fin n) (A : Fin n → Finset V) : Fin n → Finset V :=
  fun c ↦ if c = a then ∅ else if c = b then A a ∪ A b else A c

/-- The coalescence tag of one argument. -/
theorem coalesceTags_apply [DecidableEq V] (a b c : Fin n) (A : Fin n → Finset V) :
    coalesceTags a b A c = if c = a then ∅ else if c = b then A a ∪ A b else A c :=
  rfl

/-- **Decision tags (7.6).** A decision at target `i` and checker `j` on argument `a`: if
`i ∈ A a`, argument `a` also needs the checker `j` and the new parent needs `{i, j}`; otherwise the
event is omitted and the new parent needs nothing. -/
def decisionTags [DecidableEq V] (i j : V) (a : Fin n) (A : Fin n → Finset V) :
    Fin (n + 1) → Finset V :=
  Fin.snoc (fun c ↦ if c = a ∧ i ∈ A a then insert j (A a) else A c)
    (if i ∈ A a then {i, j} else ∅)

/-- The decision tag of an old argument. -/
theorem decisionTags_castSucc [DecidableEq V] (i j : V) (a c : Fin n) (A : Fin n → Finset V) :
    decisionTags i j a A c.castSucc = if c = a ∧ i ∈ A a then insert j (A a) else A c := by
  simp only [decisionTags, Fin.snoc_castSucc]

/-- The decision tag of the new parent. -/
theorem decisionTags_last [DecidableEq V] (i j : V) (a : Fin n) (A : Fin n → Finset V) :
    decisionTags i j a A (Fin.last n) = if i ∈ A a then {i, j} else ∅ := by
  simp only [decisionTags, Fin.snoc_last]

/-- **Coalescence keeps the observable determined by its tags.** The coalesced observable reads
the surviving argument at the union of the two supports and does not read the other.

Assumes: `TagDetermined f A`. -/
theorem tagDetermined_coalesceArguments [DecidableEq V] {a b : Fin n} (hab : a ≠ b)
    {f : (Fin n → V → Bool) → ℝ} {A : Fin n → Finset V} (hf : TagDetermined f A) :
    TagDetermined (coalesceArguments a b f) (coalesceTags a b A) := by
  intro w w' hw
  refine hf _ _ fun c v hv ↦ ?_
  by_cases hca : c = a
  · rw [hca, Function.update_self, Function.update_self]
    rw [hca] at hv
    refine hw b v ?_
    rw [coalesceTags_apply, if_neg hab.symm, if_pos rfl]
    exact mem_union_left _ hv
  · rw [Function.update_of_ne hca, Function.update_of_ne hca]
    refine hw c v ?_
    by_cases hcb : c = b
    · rw [coalesceTags_apply, if_neg hca, if_pos hcb]
      rw [hcb] at hv
      exact mem_union_right _ hv
    · rw [coalesceTags_apply, if_neg hca, if_neg hcb]
      exact hv

/-- **A decision keeps the observable determined by its tags (7.6).** The branched observable reads
argument `a` at `A_a ∪ {j}` and the new parent at `{i, j}` when `i ∈ A_a`, and reads the new parent
nowhere otherwise.

Assumes: `TagDetermined f A`. -/
theorem tagDetermined_decisionBranch [DecidableEq V] (i j : V) (a : Fin n)
    {f : (Fin n → V → Bool) → ℝ} {A : Fin n → Finset V} (hf : TagDetermined f A) :
    TagDetermined (decisionBranch (checkedTransfer i j) a f) (decisionTags i j a A) := by
  intro u u' hu
  refine hf _ _ fun c v hv ↦ ?_
  by_cases hca : c = a
  · rw [hca] at hv ⊢
    rw [Function.update_self, Function.update_self]
    by_cases hi : i ∈ A a
    · have hparent : ∀ k ∈ insert j (A a), u a.castSucc k = u' a.castSucc k := fun k hk ↦
        hu a.castSucc k (by simpa [decisionTags_castSucc, hi] using hk)
      have hdonor : ∀ k ∈ ({i, j} : Finset V), u (Fin.last n) k = u' (Fin.last n) k :=
        fun k hk ↦ hu (Fin.last n) k (by simpa [decisionTags_last, hi] using hk)
      simp only [checkedTransfer]
      rw [hparent j (mem_insert_self j _), hdonor j (by simp), hdonor i (by simp),
        hparent v (mem_insert_of_mem hv)]
    · have hvi : v ≠ i := fun h ↦ hi (by rw [← h]; exact hv)
      simp only [checkedTransfer, hvi, false_and, if_false]
      exact hu a.castSucc v (by simpa [decisionTags_castSucc, hi] using hv)
  · rw [Function.update_of_ne hca, Function.update_of_ne hca]
    exact hu c.castSucc v (by simpa [decisionTags_castSucc, hca] using hv)

/-- **An omitted decision (7.6).** If `f` reads argument `a` only at `A a` and the target `i` is
not there, the checked transfer changes nothing `f` reads, so on a vector of total mass one the
branched observable is the original and the event can be left out of the circuit.

Assumes: `TagDetermined f A`. -/
theorem samplingObservable_decisionBranch_of_not_mem [Fintype V] [DecidableEq V] {i : V} (j : V)
    {a : Fin n} {f : (Fin n → V → Bool) → ℝ} {A : Fin n → Finset V} (hf : TagDetermined f A)
    (hi : i ∉ A a) {p : (V → Bool) → ℝ} (hp : ∑ h, p h = 1) :
    samplingObservable (decisionBranch (checkedTransfer i j) a f) p =
      samplingObservable f p := by
  refine samplingObservable_decisionBranch_of_agree _ (fun w y ↦ hf _ _ fun c v hv ↦ ?_) hp
  by_cases hca : c = a
  · rw [hca, Function.update_self]
    rw [hca] at hv
    exact checkedTransfer_of_ne j (fun h ↦ hi (by rw [← h]; exact hv)) _ _
  · rw [Function.update_of_ne hca]

/-! ### Support counts and weights -/

/-- The weight `∑_a ∑_{v ∈ A_a} w(v)` of a tag state. -/
def tagWeight (w : V → ℝ) (A : Fin n → Finset V) : ℝ :=
  ∑ c, ∑ v ∈ A c, w v

/-- **The support count `Z = ∑_a |A_a|`** of the note's §8. -/
def tagCount (A : Fin n → Finset V) : ℕ :=
  ∑ c, (A c).card

/-- With unit weights the tag weight is the support count. -/
theorem tagWeight_one (A : Fin n → Finset V) : tagWeight (fun _ ↦ 1) A = tagCount A := by
  simp [tagWeight, tagCount]

/-- Adding one element to a set raises a nonnegative sum by at most that element's weight. -/
theorem sum_insert_le_add [DecidableEq V] {s : Finset V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (j : V) : ∑ v ∈ insert j s, w v ≤ ∑ v ∈ s, w v + w j := by
  by_cases hj : j ∈ s
  · rw [insert_eq_of_mem hj]
    linarith [hw j]
  · rw [sum_insert hj]
    linarith

/-- The weight of the decision tags, argument by argument. -/
theorem tagWeight_decisionTags [DecidableEq V] (w : V → ℝ) (i j : V) (a : Fin n)
    (A : Fin n → Finset V) :
    tagWeight w (decisionTags i j a A) =
      ∑ c, ∑ v ∈ (if c = a ∧ i ∈ A a then insert j (A a) else A c), w v +
        ∑ v ∈ (if i ∈ A a then {i, j} else ∅), w v := by
  rw [tagWeight, Fin.sum_univ_castSucc]
  simp only [decisionTags_castSucc, decisionTags_last]

/-- **An omitted decision leaves every tag weight unchanged.** -/
theorem tagWeight_decisionTags_of_not_mem [DecidableEq V] (w : V → ℝ) {i : V} (j : V)
    {a : Fin n} {A : Fin n → Finset V} (hi : i ∉ A a) :
    tagWeight w (decisionTags i j a A) = tagWeight w A := by
  rw [tagWeight_decisionTags]
  simp only [hi, and_false, if_false, sum_empty, add_zero]
  rfl

/-- **A decision raises a nonnegative tag weight by at most `w(i) + 2w(j)`.** The checker `j` joins
argument `a`, and the new parent carries `{i, j}`. -/
theorem tagWeight_decisionTags_le [DecidableEq V] {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (i j : V)
    (a : Fin n) (A : Fin n → Finset V) :
    tagWeight w (decisionTags i j a A) ≤ tagWeight w A + (w i + 2 * w j) := by
  by_cases hi : i ∈ A a
  · rw [tagWeight_decisionTags]
    simp only [hi, and_true, if_true]
    have hcoord : ∀ c, ∑ v ∈ (if c = a then insert j (A a) else A c), w v ≤
        ∑ v ∈ A c, w v + if c = a then w j else 0 := by
      intro c
      by_cases hc : c = a
      · have htags : (if c = a then insert j (A a) else A c) = insert j (A a) := if_pos hc
        have hextra : (if c = a then w j else 0) = w j := if_pos hc
        rw [htags, hextra, hc]
        exact sum_insert_le_add hw j
      · have htags : (if c = a then insert j (A a) else A c) = A c := if_neg hc
        have hextra : (if c = a then w j else 0) = 0 := if_neg hc
        rw [htags, hextra, add_zero]
    have hpair : ∑ v ∈ ({i, j} : Finset V), w v ≤ w i + w j := by
      have h := sum_insert_le_add (s := {j}) hw i
      rw [sum_singleton] at h
      linarith
    have hsum : ∑ c, (∑ v ∈ A c, w v + if c = a then w j else 0) = tagWeight w A + w j := by
      rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ a), tagWeight]
    linarith [sum_le_sum fun c (_ : c ∈ univ) ↦ hcoord c]
  · rw [tagWeight_decisionTags_of_not_mem w j hi]
    linarith [hw i, hw j]

/-- **A coalescence does not raise a nonnegative tag weight**: the union of two supports weighs at
most their sum. -/
theorem tagWeight_coalesceTags_le [DecidableEq V] {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {a b : Fin n} (hab : a ≠ b) (A : Fin n → Finset V) :
    tagWeight w (coalesceTags a b A) ≤ tagWeight w A := by
  have hcoord : ∀ c, ∑ v ∈ coalesceTags a b A c, w v ≤
      ∑ v ∈ A c, w v + ((if c = b then ∑ v ∈ A a, w v else 0) -
        if c = a then ∑ v ∈ A a, w v else 0) := by
    intro c
    by_cases hca : c = a
    · have hcb : c ≠ b := fun hcb ↦ hab (hca.symm.trans hcb)
      have htags : coalesceTags a b A c = ∅ := by rw [coalesceTags_apply, if_pos hca]
      have hleft : (if c = b then ∑ v ∈ A a, w v else 0) = 0 := if_neg hcb
      have hright : (if c = a then ∑ v ∈ A a, w v else 0) = ∑ v ∈ A a, w v := if_pos hca
      rw [htags, hleft, hright, sum_empty, hca]
      linarith
    · by_cases hcb : c = b
      · have htags : coalesceTags a b A c = A a ∪ A b := by
          rw [coalesceTags_apply, if_neg hca, if_pos hcb]
        have hleft : (if c = b then ∑ v ∈ A a, w v else 0) = ∑ v ∈ A a, w v := if_pos hcb
        have hright : (if c = a then ∑ v ∈ A a, w v else 0) = 0 := if_neg hca
        rw [htags, hleft, hright, hcb]
        have hunion := sum_union_inter (s₁ := A a) (s₂ := A b) (f := w)
        have hinter : 0 ≤ ∑ v ∈ A a ∩ A b, w v := sum_nonneg fun v _ ↦ hw v
        linarith
      · have htags : coalesceTags a b A c = A c := by
          rw [coalesceTags_apply, if_neg hca, if_neg hcb]
        have hleft : (if c = b then ∑ v ∈ A a, w v else 0) = 0 := if_neg hcb
        have hright : (if c = a then ∑ v ∈ A a, w v else 0) = 0 := if_neg hca
        rw [htags, hleft, hright]
        linarith
  have hsum : ∑ c, (∑ v ∈ A c, w v + ((if c = b then ∑ v ∈ A a, w v else 0) -
      if c = a then ∑ v ∈ A a, w v else 0)) = tagWeight w A := by
    rw [sum_add_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq', if_pos (mem_univ b),
      if_pos (mem_univ a), sub_self, add_zero, tagWeight]
  linarith [sum_le_sum fun c (_ : c ∈ univ) ↦ hcoord c]

/-- **One decision adds at most three coordinate occurrences** (the note's §8). -/
theorem tagCount_decisionTags_le [DecidableEq V] (i j : V) (a : Fin n) (A : Fin n → Finset V) :
    tagCount (decisionTags i j a A) ≤ tagCount A + 3 := by
  have h := tagWeight_decisionTags_le (w := fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) i j a A
  simp only [tagWeight_one] at h
  exact_mod_cast (by linarith : (tagCount (decisionTags i j a A) : ℝ) ≤ tagCount A + 3)

/-- **A coalescence does not raise the support count.** -/
theorem tagCount_coalesceTags_le [DecidableEq V] {a b : Fin n} (hab : a ≠ b)
    (A : Fin n → Finset V) : tagCount (coalesceTags a b A) ≤ tagCount A := by
  have h := tagWeight_coalesceTags_le (w := fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) hab A
  simp only [tagWeight_one] at h
  exact_mod_cast h

/-- **The rate of the decisions that are not omitted.** Argument `a` meets a decision at every
target `i ∈ A_a` and every checker `j`, at rate `r i j`. -/
def decisionRate [Fintype V] (r : V → V → ℝ) (A : Fin n → Finset V) : ℝ :=
  ∑ c, ∑ i ∈ A c, ∑ j, r i j

/-- **The decision rate is at most `D Z`** when the outgoing rates of every target sum to at most
`D`, the note's (8.1). -/
theorem decisionRate_le [Fintype V] {r : V → V → ℝ} {D : ℝ} (hD : ∀ i, ∑ j, r i j ≤ D)
    (A : Fin n → Finset V) : decisionRate r A ≤ D * tagCount A := by
  calc decisionRate r A ≤ ∑ c, ∑ _i ∈ A c, D :=
        sum_le_sum fun c _ ↦ sum_le_sum fun i _ ↦ hD i
    _ = D * tagCount A := by
      rw [tagCount, Nat.cast_sum, mul_sum]
      refine sum_congr rfl fun c _ ↦ ?_
      rw [sum_const, nsmul_eq_mul, mul_comm]

/-- **A tag state is ancestral material.** On a genome of `L` coordinates the pairs
`(coordinate, argument)` with the coordinate in the argument's tag are a set of ancestral material
of `Descent.Coalescent.FiniteGenomeAncestry`: loci crossed with sampled arguments. -/
def tagMaterial {L : ℕ} (A : Fin n → Finset (Fin L)) :
    Coalescent.FiniteGenomeAncestry.Material L n :=
  univ.biUnion fun c ↦ (A c).image fun v ↦ (v, c)

/-- **The support count is the size of the ancestral material.** -/
theorem card_tagMaterial {L : ℕ} (A : Fin n → Finset (Fin L)) :
    (tagMaterial A : Coalescent.FiniteGenomeAncestry.Material L n).card = tagCount A := by
  rw [tagMaterial, card_biUnion]
  · exact sum_congr rfl fun c _ ↦ card_image_of_injective _ fun v v' h ↦ (Prod.ext_iff.mp h).1
  · intro c _ c' _ hcc'
    refine disjoint_left.mpr fun vc hvc hvc' ↦ hcc' ?_
    obtain ⟨v, -, rfl⟩ := mem_image.mp hvc
    obtain ⟨v', -, hv'⟩ := mem_image.mp hvc'
    exact (Prod.ext_iff.mp hv').2.symm

/-- **At most `L n` coordinate occurrences on `n` arguments**, the material count bound of
`Descent.Coalescent.FiniteGenomeAncestry` read for tags. -/
theorem tagCount_le_mul {L : ℕ} (A : Fin n → Finset (Fin L)) : tagCount A ≤ L * n := by
  rw [← card_tagMaterial]
  exact (card_le_univ _).trans (by simp)

end Descent.Pangenome.AncestralLocality

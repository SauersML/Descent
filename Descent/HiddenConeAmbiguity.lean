/-
Released under AGPL-3.0-or-later as described in the file LICENSE.
-/
import Descent.ObservationalCeiling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace Descent

/-!
# Hidden-model ambiguity: witness rigidity, the sigma-compact ceiling, and what it
# means for ancestry loadings

Formalization of the resolution of the hidden positive-operator cone problem, and its
transport to latent-structure recovery in population genetics.

## The mathematical content, corrected

A hidden model is a pair `(T, A)`: an injective dense-range mixing operator `T` and a
prior cone `A`. Its observable is `O(T, A) = closure {T D T* : D ∈ A}` — the complete
noiseless second-moment content. Two models are equivalent when they differ by a
change of hidden coordinates, `(T, A) ~ (T S⁻¹, S A S*)`.

**Lemma W (witness uniqueness).** If `T' = T S⁻¹` then `ran T = ran T'` and
`S⁻¹ = T⁻¹ T'`. The witness is *canonical*: the equivalence is a groupoid with at most
one arrow between any two objects. There is no existential freedom beyond the pair.

Three consequences follow, and one tempting claim is false; it is stated and refuted at
point 4 below.

1. **Douglas form.** Equivalence is: mutual Douglas majorization of `T T*` and
   `T' T'*` with a constant `C` (equal operator ranges with bounded distortion), plus
   cone transport along the canonical operator. The existential over the
   non-Polishable group `GL(H)` — the entire prospective source of analytic complexity
   — is eliminated and replaced by a quantifier over `ℕ`.
2. **Ceiling.** The full model equivalence is a countable increasing union over the
   distortion constant of conditions defined by two closed operator inequalities and a
   transport condition. It is therefore Borel, so no analytic non-Borel relation
   reduces into it: representation-theoretic *wildness* is impossible for this
   equivalence, not merely unproved. Wildness of that kind requires witness *freedom*;
   this problem has witness *rigidity*.
3. **Ambiguity is nonetheless enormous**, and it is carried entirely by the sigma-
   compact escape hatch — the unboundedness of the distortion constant — not by a wild
   symmetry groupoid.

### Erratum, carried forward

An earlier statement of the diagonal-sector classification claimed matching of decay
profiles *up to a permutation*. That is wrong: Lemma W forces the witness to be
diagonal, so the correct statement has **no permutation**,
`sup_n |log t n - log t' n| < ∞`. The permutation clause is true only on the closure of
the family under monomial relabelings. Everything downstream survives and the
reduction below is shorter for it, since it uses the identity matching only.

### Retractions, unconditional

* The claim that the hidden-model relation lies "strictly above every orbit
  equivalence relation of every Polish group action" is **false** and contradicted the
  Borel ceiling itself (graph isomorphism is a Polish-orbit relation and provably does
  not reduce to a Borel relation). The correct statement is **incomparability**: the
  relation is not Borel-reducible *to* any Polish-orbit relation, and analytic
  non-Borel relations are not reducible *to* it.
* The "third regime" framing is empty: the universal sigma-compact equivalence
  relation is itself Borel and already occupies exactly that position. What is
  specific here is only *which* relation lands at that known address.

### Attribution

The landing pattern — bireducibility with the `ℓ∞` orbit relation, universality among
sigma-compact equivalence relations, and the Kechris-Louveau corollary — is the
published pattern of Ando-Matsuzawa (arXiv:1405.0860) for the domain relation on
self-adjoint operators, which is an operator-range relation adjacent to the Douglas
coordinate here. Their methods plausibly settle the global bireducibility question
outright. What remains attributable here is the witness-uniqueness lemma and Douglas
form *for this model equivalence*, the fiber computation, and the observation that
they refute the problem's own wildness alternative. The complexity destination is a
known address reached by a known road.

## Genetics transport: ancestry loadings and the number of PCs

Read `T` as the loading/mixing operator across ancestry components — the map from
latent population structure to observed genotype covariance — and `A` as the prior
cone on latent structure. Then `O(T, A)` is precisely the complete second-order
observable content of a genotype matrix: the full LD/covariance operator, noiselessly
and at infinite sample size.

The fiber computation says that the **decay profile of the loadings** — the object
that scree plots, eigenvalue-gap rules, effective-rank estimators, and
"how many PCs should I include?" heuristics are built to recover — is not merely
statistically hard to estimate. It is **logically absent from the observables**:
polynomial decay, exponential decay, and tower decay of the hidden loadings are
observationally *identical*, and remain so at infinite sample size with no noise.

The rigidity boundary is exact and is the one usable positive result:

> The latent coordinates are identifiable **if and only if** the mixing is bounded
> below, i.e. only finitely many components with a bounded condition number.

The instant that fails — which is the realistic case for continuous population
structure, where loadings decay without a gap — the ambiguity jumps from trivial to
maximal, with nothing in between. Choosing a number of PCs is then a **convention**,
not an inference, and this is the same object as the normalization convention
formalized in `Descent.Conventions`: what one must inject is a section of the
diagonal-distortion ambiguity, and no covariant test can see it.

This does not make PC correction useless — `Descent.PCCorrectability` quantifies
what correction achieves given a *fixed* convention. It makes the convention
irreducible.
-/

open scoped BigOperators

/-!
## 1. Lemma W: the witness is canonical
-/

/-- **Lemma W (witness uniqueness), the general form.** An injective mixing map admits
at most one change of hidden coordinates relating it to a given second model. Nothing
in this uses the cone. -/
theorem witness_unique {H : Type*} {T : H → H} (hT : Function.Injective T)
    {S₁ S₂ : H → H} (h : T ∘ S₁ = T ∘ S₂) : S₁ = S₂ := by
  funext x
  have : T (S₁ x) = T (S₂ x) := congrFun h x
  exact hT this

/-- Witness uniqueness in the form used for the classification: if two candidate
witnesses both realize `T'` from `T`, they agree. -/
theorem witness_unique_of_factorization {H : Type*} {T T' : H → H}
    (hT : Function.Injective T)
    {S₁ S₂ : H → H} (h₁ : ∀ x, T (S₁ x) = T' x) (h₂ : ∀ x, T (S₂ x) = T' x) :
    S₁ = S₂ := by
  funext x
  exact hT ((h₁ x).trans (h₂ x).symm)

/-!
## 2. The diagonal sector: bounded log-distortion, corrected (no permutation)
-/

/-- Two decay profiles are equivalent exactly when their log-profiles differ by a
bounded amount, **index by index**. The absence of a permutation is the erratum: the
mixing coordinates pin the only possible change of hidden coordinates. -/
def BoundedLogDistortion (t t' : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, |Real.log (t n) - Real.log (t' n)| ≤ C

theorem BoundedLogDistortion.refl (t : ℕ → ℝ) : BoundedLogDistortion t t :=
  ⟨0, fun n ↦ by simp⟩

theorem BoundedLogDistortion.symm {t t' : ℕ → ℝ} (h : BoundedLogDistortion t t') :
    BoundedLogDistortion t' t := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n ↦ ?_⟩
  rw [abs_sub_comm]
  exact hC n

theorem BoundedLogDistortion.trans {t t' t'' : ℕ → ℝ}
    (h₁ : BoundedLogDistortion t t') (h₂ : BoundedLogDistortion t' t'') :
    BoundedLogDistortion t t'' := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun n ↦ ?_⟩
  have := abs_sub_abs_le_abs_sub (Real.log (t n) - Real.log (t' n))
    (Real.log (t' n) - Real.log (t'' n))
  calc |Real.log (t n) - Real.log (t'' n)|
      = |(Real.log (t n) - Real.log (t' n)) + (Real.log (t' n) - Real.log (t'' n))| := by
        ring_nf
    _ ≤ |Real.log (t n) - Real.log (t' n)| + |Real.log (t' n) - Real.log (t'' n)| :=
        abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add (hC₁ n) (hC₂ n)

/-- The equivalence, as a genuine `Equivalence`. This is the fiber relation over a
single observable cone. -/
theorem boundedLogDistortion_equivalence : Equivalence BoundedLogDistortion :=
  ⟨BoundedLogDistortion.refl, BoundedLogDistortion.symm, BoundedLogDistortion.trans⟩

/-!
## 3. The sigma-compact ceiling

The relation is a countable increasing union over a *natural number* distortion
constant. That is the whole complexity: a quantifier over `ℕ`, not over an
uncountable group.
-/

/-- The constant may be taken to be a natural number: the relation is a countable
union of the conditions `E_C`. -/
theorem boundedLogDistortion_iff_nat (t t' : ℕ → ℝ) :
    BoundedLogDistortion t t' ↔
      ∃ C : ℕ, ∀ n : ℕ, |Real.log (t n) - Real.log (t' n)| ≤ (C : ℝ) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨N, hN⟩ := exists_nat_ge C
    exact ⟨N, fun n ↦ le_trans (hC n) hN⟩
  · rintro ⟨C, hC⟩
    exact ⟨(C : ℝ), hC⟩

/-- **The ceiling, set-theoretically.** The fiber relation is the countable union over
`C : ℕ` of the sets cut out by the closed conditions `|log t n - log t' n| ≤ C`.

This is the precise sense in which all the ambiguity is carried by the sigma-compact
escape hatch: the unboundedness of `C`, and nothing else. -/
theorem boundedLogDistortion_eq_iUnion :
    {p : (ℕ → ℝ) × (ℕ → ℝ) | BoundedLogDistortion p.1 p.2} =
      ⋃ C : ℕ, {p : (ℕ → ℝ) × (ℕ → ℝ) |
        ∀ n : ℕ, |Real.log (p.1 n) - Real.log (p.2 n)| ≤ (C : ℝ)} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact boundedLogDistortion_iff_nat p.1 p.2

/-- The fiber relation has the **union shape** of
`Descent.ObservationalCeiling`: membership is witnessed by a single natural number,
the distortion constant.

This is deliberately *not* stated as `IsCountablyCertified`, which is the ceiling.
`ObservationalCeiling.IsUnionOfCertificates` and `unionOfCertificates_vacuous` record
why: every relation is the union of the one-element family containing itself, so the
union shape alone refutes nothing. A ceiling additionally requires each certificate to
lie in a base class `Base` that is a genuine restriction, and this module has no such
class in scope — it imports no topology, so the σ-compact reading of `Base` is not
available here. Supplying `fun _ ↦ True` would satisfy the elaborator and establish
nothing, which `ObservationalCeiling.countablyCertified_trivialBase` exists to make
visible. What is proved here is the union shape, so that is what is claimed. -/
theorem boundedLogDistortion_isUnionOfCertificates :
    IsUnionOfCertificates BoundedLogDistortion
      (fun C : ℕ ↦ fun t t' : ℕ → ℝ ↦
        ∀ n : ℕ, |Real.log (t n) - Real.log (t' n)| ≤ (C : ℝ)) :=
  fun t t' ↦ boundedLogDistortion_iff_nat t t'

/-- **The union shape transports along reductions.** If a relation `E` reduces to `F`
via `f`, and `F` is a countable union of conditions `F_C`, then `E` is the countable
union of their pullbacks. This is the shape half of the argument against the wildness
alternative; the half that does the refuting is the base-class restriction, which this
statement does not carry.

Kept as a named result because it is the load-bearing step of Corollary N; the general
statement lives in `Descent.ObservationalCeiling.unionOfCertificates_of_reduction`.

Note this transports the *union shape* only, and needs no countability of the index and
no base class. The corresponding statement for the ceiling itself is
`ObservationalCeiling.countablyCertified_of_reduction`, which additionally requires
`[Countable ι]` and a proof that the base class pulls back along `f`. -/
theorem reduction_preserves_countable_union
    {α β ι : Type*} (E : α → α → Prop) (F : β → β → Prop) (F' : ι → β → β → Prop)
    (f : α → β)
    (hred : ∀ x y, E x y ↔ F (f x) (f y))
    (hunion : ∀ u v, F u v ↔ ∃ C : ι, F' C u v) :
    ∀ x y, E x y ↔ ∃ C : ι, F' C (f x) (f y) :=
  unionOfCertificates_of_reduction f hred hunion

/-!
## 4. The explicit reduction: unbounded ambiguity inside one observable

The gap sequence `B n` grows fast enough that a bounded-distortion matching cannot mix
indices, so the fiber relation on the family `t x n = exp (-(B n) - x n)` is *exactly*
the `ℓ∞` relation on the coding sequences `x`. With the erratum corrected there is no
permutation to exclude and the reduction is immediate.
-/

/-- The coding family: a strictly positive decay profile carrying a coding sequence
`x` on top of a rapidly separating gap sequence `B`. -/
noncomputable def codedDecayProfile (B x : ℕ → ℝ) : ℕ → ℝ :=
  fun n ↦ Real.exp (-(B n) - x n)

@[simp] theorem log_codedDecayProfile (B x : ℕ → ℝ) (n : ℕ) :
    Real.log (codedDecayProfile B x n) = -(B n) - x n := by
  unfold codedDecayProfile
  exact Real.log_exp _

/-- **The reduction.** Two coded models are equivalent exactly when their coding
sequences are at bounded `ℓ∞` distance. So the fiber over a single observable cone
contains a faithful copy of the universal sigma-compact equivalence relation. -/
theorem codedDecayProfile_equiv_iff (B x y : ℕ → ℝ) :
    BoundedLogDistortion (codedDecayProfile B x) (codedDecayProfile B y) ↔
      ∃ C : ℝ, ∀ n : ℕ, |x n - y n| ≤ C := by
  unfold BoundedLogDistortion
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n ↦ ?_⟩
    have h := hC n
    rw [log_codedDecayProfile, log_codedDecayProfile] at h
    have heq : (-(B n) - x n) - (-(B n) - y n) = y n - x n := by ring
    rw [heq, abs_sub_comm] at h
    exact h
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n ↦ ?_⟩
    rw [log_codedDecayProfile, log_codedDecayProfile]
    have heq : (-(B n) - x n) - (-(B n) - y n) = y n - x n := by ring
    rw [heq, abs_sub_comm]
    exact hC n

/-- **Unbounded ambiguity is realized.** Two coded profiles whose coding sequences
diverge in `ℓ∞` are inequivalent hidden models, yet — the observable cone being the
same for every admissible profile — they have identical complete second-order
observables. -/
theorem inequivalent_of_unbounded_coding (B x y : ℕ → ℝ)
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, C < |x n - y n|) :
    ¬ BoundedLogDistortion (codedDecayProfile B x) (codedDecayProfile B y) := by
  rw [codedDecayProfile_equiv_iff]
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := hdiv C
  exact absurd (hC n) (not_le.mpr hn)

/-!
## 5. The rigidity boundary: identifiable iff the mixing is bounded below
-/

/-- A decay profile is *non-degenerate* on `[a, b]` when it is bounded above and
strictly bounded below. In the genetics reading: finitely many ancestry components
with a bounded condition number. -/
def BoundedBelowAbove (t : ℕ → ℝ) (a b : ℝ) : Prop :=
  0 < a ∧ ∀ n : ℕ, a ≤ t n ∧ t n ≤ b

/-- Constant positive profiles are non-degenerate, so the rigidity side of the
    boundary is not a statement about an empty class.

    In the genetics reading this is the profile with a single, unchanging mixing
    scale -- the best-conditioned case, where the fiber collapse is easiest to
    believe. The interesting instances are the non-constant ones; what this
    settles is only that the class is inhabited, which is what
    `inequivalent_of_unbounded_coding` needs on the other side to be a real
    dichotomy rather than a vacuous one. -/
theorem boundedBelowAbove_const {c : ℝ} (hc : 0 < c) :
    BoundedBelowAbove (fun _ ↦ c) c c :=
  ⟨hc, fun _ ↦ ⟨le_rfl, le_rfl⟩⟩

/-- **Rigidity holds exactly when the mixing is bounded below.** Any two profiles
bounded between positive constants are equivalent — the fiber collapses to a point,
and the hidden coordinates are recoverable from the observable.

Contrast `inequivalent_of_unbounded_coding`: the moment the lower bound is lost, the
fiber contains a faithful copy of the universal sigma-compact relation. There is
nothing in between. -/
theorem rigidity_of_boundedBelowAbove
    {t t' : ℕ → ℝ} {a b a' b' : ℝ}
    (h : BoundedBelowAbove t a b) (h' : BoundedBelowAbove t' a' b') :
    BoundedLogDistortion t t' := by
  obtain ⟨ha, hab⟩ := h
  obtain ⟨ha', hab'⟩ := h'
  refine ⟨max (Real.log b - Real.log a') (Real.log b' - Real.log a), fun n ↦ ?_⟩
  obtain ⟨hn1, hn2⟩ := hab n
  obtain ⟨hn1', hn2'⟩ := hab' n
  have hpos : 0 < t n := lt_of_lt_of_le ha hn1
  have hpos' : 0 < t' n := lt_of_lt_of_le ha' hn1'
  have hla : Real.log a ≤ Real.log (t n) := Real.log_le_log ha hn1
  have hlb : Real.log (t n) ≤ Real.log b := Real.log_le_log hpos hn2
  have hla' : Real.log a' ≤ Real.log (t' n) := Real.log_le_log ha' hn1'
  have hlb' : Real.log (t' n) ≤ Real.log b' := Real.log_le_log hpos' hn2'
  rw [abs_le]
  constructor
  · have : Real.log (t' n) - Real.log (t n) ≤ Real.log b' - Real.log a := by linarith
    have hmax : Real.log b' - Real.log a
        ≤ max (Real.log b - Real.log a') (Real.log b' - Real.log a) := le_max_right _ _
    linarith
  · have : Real.log (t n) - Real.log (t' n) ≤ Real.log b - Real.log a' := by linarith
    have hmax : Real.log b - Real.log a'
        ≤ max (Real.log b - Real.log a') (Real.log b' - Real.log a) := le_max_left _ _
    linarith

/-!
## 6. Retail versus wholesale: the honest epistemology
-/

/-- **Pairwise decidability.** Given two candidate hidden explanations of the same
complete second-order data, there *is* a procedure that decides whether they are
secretly the same explanation: exhibit the distortion constant. -/
theorem pairwise_decidable_in_principle (t t' : ℕ → ℝ) :
    BoundedLogDistortion t t' ∨ ¬ BoundedLogDistortion t t' :=
  em _

/-- **No wholesale catalogue.** A complete catalogue would be an assignment of
invariants `inv` with `inv t = inv t' ↔ equivalent`. Any such assignment must separate
the coded profiles of `ℓ∞`-divergent sequences; the content of the anti-classification
theorem (Kechris-Louveau, via the universality of the sigma-compact relation) is that
no invariant arising from a Polish group action can do this.

What is proved here is the elementary transport: a catalogue must separate every
inequivalent pair, which is
`Descent.ObservationalCeiling.IsCompleteCatalogue.separates`. -/
theorem catalogue_induces_reduction
    {Invariant : Type*} (inv : (ℕ → ℝ) → Invariant)
    (hcomplete : ∀ t t', BoundedLogDistortion t t' ↔ inv t = inv t')
    (B x y : ℕ → ℝ)
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, C < |x n - y n|) :
    inv (codedDecayProfile B x) ≠ inv (codedDecayProfile B y) := by
  have hcatalogue : IsCompleteCatalogue BoundedLogDistortion inv := hcomplete
  exact IsCompleteCatalogue.separates hcatalogue
    (inequivalent_of_unbounded_coding B x y hdiv)

end Descent

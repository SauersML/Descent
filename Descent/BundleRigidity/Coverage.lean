/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Coverage, peeling, the core, and Theorem A

This module is **self-contained: it imports only Mathlib**.

## The objects

For a family of continuous modulus curves `m j : T → ℝ` and a set `S` of parameters:

* the **coverers** of a value `v` in `S` are the parameters of `S` some branch of which
  produces `v`;
* the **single window** `W S` is the interior of the set of positive values covered *at
  most once* from within `S`;
* the **peelable set** `peelSet S` is the set of parameters having a branch landing in the
  single window — it is **open**, being a finite union of preimages of an open set;
* **peeling** removes it: `peel S = S \ peelSet S`;
* the **core** of `K` is the largest subset of `K` that peeling does not shrink.

## Why the core is defined coinductively rather than by transfinite iteration

The source defines the core by iterating `peel` from `K` through the ordinals — `S₀ = K`,
`S_{α+1} = peel S_α`, intersections at limits — and then proves a **stabilization lemma**
(Lemma 1): the chain is eventually constant, because a strictly decreasing transfinite
chain of closed sets in a second-countable space must be countable.

Here the core is instead defined as the union of all `S ⊆ K` with `S ⊆ peel S`: the
**greatest post-fixed point**. The two agree, because `peel` is monotone
(`peel_mono`) and Knaster–Tarski applies. Taking the coinductive definition as primary has
two concrete payoffs:

* **Lemma 1 is not needed.** Stabilization is what makes the transfinite iteration
  well-defined; the greatest post-fixed point needs no ordinals at all, so no
  second-countability and no cardinality argument enter.
* **Theorem A becomes a one-step argument** rather than a transfinite induction. To show
  `supp κ ⊆ Core` one shows only that `supp κ` is *itself* peel-stable — a single
  application of the peeling lemma — and the union definition does the rest
  (`subset_core`). The successor and limit cases both disappear.

`core_subset_peel_core` is the fixed-point property that makes this legitimate, and its
proof is exactly where monotonicity is used.

## Theorem A

`support_subset_core` is Theorem A in set-theoretic form: any subset of `K` that avoids its
own single window lies in the core. The measure-theoretic content — that the support of a
kernel element avoids its own single window — is the **peeling lemma**, and its hypothesis
appears here as `hpeel` rather than being assumed silently.

**What the peeling lemma does not need**, and this is worth recording because it dissolves
a pre-registered audit point: no analyticity, no monotonicity of the branches, no
measurable selection, and no subanalytic local finiteness. Single coverage makes `h ∘ c` a
legal test function and **diagonalizes** the operator; bundling enters only through the
uniform lower bound `Φ ≥ p_min > 0`. Several branches of one bundle **pool**, they never
trade.

## Attribution

The peeling construction is the classical **lightning-bolt argument** from the theory of
sums of weighted compositions (Diliberto–Straus, Marshall–O'Farrell, Ismailov). The
coinductive repackaging is a convenience, not a result.
-/

namespace Descent.BundleRigidity

open scoped BigOperators

variable {T : Type*} [TopologicalSpace T] {d : ℕ}

/-- A family of continuous modulus curves on a parameter space. -/
structure ModulusFamily (T : Type*) [TopologicalSpace T] (d : ℕ) where
  /-- The modulus curve of branch `j`. -/
  curve : Fin d → C(T, ℝ)

namespace ModulusFamily

variable (F : ModulusFamily T d)

/-- **The constant family**: every branch a constant modulus curve.

`ModulusFamily` had no exhibited inhabitant, so the coverage and window results
were quantified over a class nothing had been shown to belong to. Constants are
the right member to name: a constant branch covers a value either everywhere or
nowhere, which is the degenerate extreme the single-window construction is built
to exclude, and having it in hand says the exclusion is doing work. -/
def const (values : Fin d → ℝ) : ModulusFamily T d where
  curve := fun j ↦ ContinuousMap.const T (values j)

instance instNonempty : Nonempty (ModulusFamily T d) := ⟨const (fun _ ↦ 0)⟩

/-- **The coverers of `v` within `S`**: the parameters of `S` at which some branch takes
the value `v`. -/
def coverers (F : ModulusFamily T d) (S : Set T) (v : ℝ) : Set T :=
  {t | t ∈ S ∧ ∃ j, F.curve j t = v}

/-- **The single window** `W S`: the interior of the set of strictly positive values that
are covered at most once from within `S`.

Taking the interior is what makes the window open, which is what lets the peeled set be
open and the test functions of the peeling lemma be continuous. -/
def singleWindow (F : ModulusFamily T d) (S : Set T) : Set ℝ :=
  interior {v : ℝ | 0 < v ∧ (F.coverers S v).Subsingleton}

/-- **The peelable set**: parameters having some branch landing in the single window. -/
def peelSet (F : ModulusFamily T d) (S : Set T) : Set T :=
  ⋃ j, (F.curve j) ⁻¹' (F.singleWindow S)

/-- **One peeling step**. -/
def peel (F : ModulusFamily T d) (S : Set T) : Set T := S \ F.peelSet S

/-- **The core of `K`**: the largest subset of `K` that peeling does not shrink, as the
union of all peel-stable subsets. -/
def core (F : ModulusFamily T d) (K : Set T) : Set T :=
  ⋃₀ {S | S ⊆ K ∧ S ⊆ F.peel S}

/-- **A constant family covers a value everywhere in `S`.** If some branch sits at
`v`, every parameter of `S` is a coverer, so the coverer set is all of `S`. -/
theorem coverers_const_of_exists (values : Fin d → ℝ) (S : Set T) (v : ℝ)
    (hv : ∃ j, values j = v) :
    (const values).coverers S v = S := by
  ext t
  simp [coverers, const, ContinuousMap.const_apply, hv]

/-- **...or nowhere.** If no branch sits at `v`, no parameter is a coverer.

Together with the previous theorem this is the sense in which constants are the
degenerate extreme: the coverer set never depends on the parameter, so it is
never a singleton unless `S` itself is, and `singleWindow` therefore sees an
all-or-nothing condition. That is exactly the behaviour the peeling construction
is built to exclude, and having it proved says the exclusion is doing work
rather than guarding against nothing. -/
theorem coverers_const_of_not_exists (values : Fin d → ℝ) (S : Set T) (v : ℝ)
    (hv : ¬ ∃ j, values j = v) :
    (const values).coverers S v = ∅ := by
  ext t
  simp [coverers, const, ContinuousMap.const_apply, hv]

/-! ## Monotonicity, which is what makes the coinductive definition work -/

/-- More parameters can only produce more coverers. -/
theorem coverers_mono {S S' : Set T} (h : S ⊆ S') (v : ℝ) :
    F.coverers S v ⊆ F.coverers S' v := by
  rintro t ⟨htS, hj⟩
  exact ⟨h htS, hj⟩

/-- **The single window is antitone**: a larger set has more coverers, so fewer values are
singly covered. -/
theorem singleWindow_anti {S S' : Set T} (h : S ⊆ S') :
    F.singleWindow S' ⊆ F.singleWindow S := by
  apply interior_mono
  rintro v ⟨hv, hsub⟩
  exact ⟨hv, hsub.anti (F.coverers_mono h v)⟩

/-- The peelable set is antitone, for the same reason. -/
theorem peelSet_anti {S S' : Set T} (h : S ⊆ S') : F.peelSet S' ⊆ F.peelSet S := by
  intro t ht
  simp only [peelSet, Set.mem_iUnion, Set.mem_preimage] at ht ⊢
  obtain ⟨j, hj⟩ := ht
  exact ⟨j, F.singleWindow_anti h hj⟩

/-- **Peeling is monotone.** This is the hypothesis of Knaster–Tarski and the reason the
greatest post-fixed point exists. -/
theorem peel_mono {S S' : Set T} (h : S ⊆ S') : F.peel S ⊆ F.peel S' := by
  rintro t ⟨htS, htP⟩
  exact ⟨h htS, fun hc ↦ htP (F.peelSet_anti h hc)⟩

/-- Peeling only removes points. -/
theorem peel_subset (S : Set T) : F.peel S ⊆ S := fun _ ht ↦ ht.1

/-- **The peelable set is open**, being a finite union of preimages of an open set under
continuous maps. This is what lets a measure vanishing on it have support in the
complement. -/
theorem isOpen_peelSet (S : Set T) : IsOpen (F.peelSet S) := by
  apply isOpen_iUnion
  intro j
  exact (F.curve j).continuous.isOpen_preimage _ isOpen_interior

/-! ## The core -/

/-- The core is contained in `K`. -/
theorem core_subset (K : Set T) : F.core K ⊆ K := by
  apply Set.sUnion_subset
  rintro S ⟨hSK, _⟩
  exact hSK

/-- **Any peel-stable subset of `K` lies in the core.** This is the whole of the
coinduction, and it replaces the transfinite induction of the source. -/
theorem subset_core {K S : Set T} (hSK : S ⊆ K) (hstable : S ⊆ F.peel S) :
    S ⊆ F.core K :=
  Set.subset_sUnion_of_mem ⟨hSK, hstable⟩

/-- **The core is itself peel-stable**, so it is a genuine fixed point and peeling has
nothing left to remove. Monotonicity of `peel` is exactly what this proof consumes. -/
theorem core_subset_peel_core (K : Set T) : F.core K ⊆ F.peel (F.core K) := by
  apply Set.sUnion_subset
  rintro S ⟨hSK, hstable⟩
  refine hstable.trans (F.peel_mono ?_)
  exact Set.subset_sUnion_of_mem ⟨hSK, hstable⟩

/-- Consequently peeling the core returns the core exactly. -/
theorem peel_core_eq (K : Set T) : F.peel (F.core K) = F.core K :=
  le_antisymm (F.peel_subset _) (F.core_subset_peel_core K)

/-! ## Theorem A -/

/-- **Theorem A, in set-theoretic form.**

If `S ⊆ K` and no branch of any point of `S` lands in `S`'s own single window, then
`S ⊆ Core K`.

The hypothesis `hpeel` is exactly what the peeling lemma delivers for `S = supp κ` when
`L κ = 0`: the kernel element vanishes on the open peelable set, so its support avoids it.
Carrying it as a hypothesis rather than assuming it silently is the point — the
measure-theoretic input is visible in the signature.

Note what has disappeared relative to the source's proof. There is **no transfinite
induction**: no successor step, no limit step, and no appeal to the stabilization lemma.
The coinductive definition of the core absorbs all three, and what remains is the single
observation that `S` is peel-stable. -/
theorem support_subset_core {K S : Set T} (hSK : S ⊆ K)
    (hpeel : ∀ t ∈ S, ∀ j, F.curve j t ∉ F.singleWindow S) :
    S ⊆ F.core K := by
  refine F.subset_core hSK ?_
  intro t htS
  refine ⟨htS, ?_⟩
  simp only [peelSet, Set.mem_iUnion, Set.mem_preimage]
  rintro ⟨j, hj⟩
  exact hpeel t htS j hj

/-- **Corollary A1.** If the core of every compact set is empty, then no non-zero kernel
element can have compact support: its support would have to sit inside an empty set.

Stated here in the form the coverage side supplies — an empty core forces the support to
be empty. The passage from "support empty" to "the measure is zero" is measure theory and
belongs with the operator, not here. -/
theorem eq_empty_of_core_empty {K S : Set T} (hSK : S ⊆ K)
    (hpeel : ∀ t ∈ S, ∀ j, F.curve j t ∉ F.singleWindow S)
    (hcore : F.core K = ∅) : S = ∅ :=
  Set.subset_eq_empty (F.support_subset_core hSK hpeel) hcore

/-! ## Uniqueness of the coverer, and what is not proved here -/

/-- **On the single window the coverer is unique.** This is what makes `c v` well defined
and `h ∘ c` a legal test function in the peeling lemma — the step that diagonalizes the
operator. -/
theorem coverer_unique {S : Set T} {v : ℝ} (hv : v ∈ F.singleWindow S)
    {t₁ t₂ : T} (h₁ : t₁ ∈ F.coverers S v) (h₂ : t₂ ∈ F.coverers S v) : t₁ = t₂ :=
  (interior_subset hv).2 h₁ h₂

/-! ## What this module does not establish

A `PeelingHypotheses` structure used to sit here with three `Prop`-valued fields, and its
docstring claimed "anything derived from them carries them in its type". **Nothing was
derived from them** — no declaration in this development ever took the structure as an
argument. The claim was aspirational and false, and the structure is removed.

It could not have been otherwise: a field of type `Prop` states nothing. `massFloor : Prop`
is a variable ranging over propositions, satisfiable by `True`; it does not assert that
`Φ ≥ p_min > 0`. So such a field can neither be discharged (there is nothing to prove) nor
honestly cited as an external theorem (it names none).

The three inputs the peeling lemma actually needs, stated here as prose because prose is
what an unformalized input deserves:

* **Lemma 2, continuity of the coverer.** On a component of the single window the unique
  coverer depends continuously on the value, by compactness — any subsequential limit of
  `c vₙ` lies in `C_S v`, which `coverer_unique` shows is a singleton. Not formalized.
* **Support and open sets.** A measure vanishing on an open set has support disjoint from
  it. Standard measure theory, not formalized here.
* **The mass floor** `Φ ≥ p_min > 0`, which is the only place bundling enters: branches of
  one bundle pool, never trade.

What *is* proved in this module is the topological and order-theoretic skeleton —
`peel_mono`, `isOpen_peelSet`, `core_subset_peel_core`, `support_subset_core`,
`coverer_unique` — and those carry no hypotheses beyond their explicit arguments. -/

end ModulusFamily

end Descent.BundleRigidity

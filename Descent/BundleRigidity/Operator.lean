/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The bundle modulus operator, its mass identity, and symmetric families

This module is **self-contained: it imports only Mathlib**. It deliberately does not
import any other `Descent` module, so it can be read, checked and built on its own.

*On the import style, since it changed and the reason is not obvious from the diff.* This
module and its siblings originally began `import Mathlib`, pulling the whole library at
once. That requires the root `Mathlib.olean`. **Do not revert to the wholesale form**, for
three reasons, in increasing order of importance:

1. *cost.* The aggregate import makes every builder pay for the whole library, and
   targeted imports are why the rest of `Descent` builds in minutes instead of
   descending into thousands of Mathlib targets.
2. *single point of failure — the real argument.* The wholesale form made these modules'
   buildability depend on a **global artifact that nothing else in the corpus depended
   on**. When the root olean went missing, every other module still built and these
   eleven alone could not — and because they were the only ones affected, the fact went
   unnoticed for a long time while being reported as two separate problems ("these
   modules are never checked" and "the root is missing"), which were one problem. The
   targeted form puts this directory on the same footing as everything around it, so the
   next time the root is absent **nobody has to notice that these modules are special.**
3. *these modules are now foundational.* Files outside this directory are being wired to
   depend on them, so their import structure is load-bearing rather than local.

That the wholesale form would work whenever the root olean is present is not an argument
for it; reason 2 is about what happens the next time it is absent.

## What is here

A **bundle family** on a parameter space `T` is a finite list of atoms `atom j t` with
masses `mass j t > 0` summing to one, standardized so that `∑ mass j t * atom j t = 0`
and `∑ mass j t * atom j t ^ 2 = 1`. One parameter `t` fixes every atom and every mass
simultaneously — that is what *bundle* means, and it is the entire source of rigidity.
The atoms cannot be reweighted one at a time.

The **modulus curve** is `modulusMap j t = |atom j t ^ 2 - 1|`, the value taken by
`|U|` for `U = X² - 1`. The family's **transfer measure** at `t` is
`TT t = ∑ j, mass j t • δ (modulusMap j t)`, and the operator studied here sends a
measure `κ` on parameters to `L κ = ∫ TT t dκ t`.

Measures are represented here **by the linear functionals they induce on continuous test
functions** — the Riesz picture. A measure is `κ : C(T, ℝ) →ₗ[ℝ] ℝ`. This is the right
level for everything in this module: the operator, its adjoint, the mass identity and the
symmetry theorem are all statements about pairing against test functions, and the Riesz
picture makes them short and complete rather than long and partial. The support-side
statements, which genuinely need measures as set functions, live in the companion
`Coverage` and `Peeling` modules and are stated there with their analytic inputs named.

In this picture the adjoint comes first and the operator is defined from it:
`coTransfer f t = ∑ j, mass j t * f (modulusMap j t)` is `L*`, and `L κ = κ ∘ L*`.

## Attribution — what is classical here and what is not

**Almost none of the machinery below is new, and this docstring is written so that no
later reader can mistake it for new.**

Bundle rigidity is the **measure-side dual of the classical theory of sums of weighted
compositions**: functions of the form `∑ p_j · (f ∘ m_j)`, studied by
**Diliberto and Straus**, by **Marshall and O'Farrell**, and by **Ismailov**. The peeling
argument formalized in the companion module is the classical **lightning-bolt argument**
— a path through the coincidence structure must close up before it can carry anything —
and the product-one cycle criterion of Theorem D is the standard **closed-path criterion**
of that literature, transported to weighted analytic branch maps in one variable.

What is genuinely new in this development, and all that should ever be claimed for it:

1. **the setting**: tied weights with moving analytic atoms. The classical theory takes
   the composition maps as given and the weights as free; here one parameter moves the
   atoms and their masses together, and the masses are pinned by the standardization
   identities. That case is not covered by the classical results;
2. **the complete `d = 2` solution**, with the peeling chain `P k = k / (2 * k + 1)`.
   That is formalized with no unproved hypotheses at all in the companion `TwoAtom`
   module;
3. **the tilt observation**: tilting by `|X| ^ (2θ)` moves only amplitudes and never
   phases, so oscillatory decay is bought once for every tilt simultaneously.

And one honest admission, which is a result of record rather than a gap to be filled
later: **there is no if-and-only-if criterion on wild cores.** An empty core is
sufficient for rigidity; no necessary-and-sufficient condition is claimed, here or
anywhere in this development.

## A structural limitation, recorded rather than fixed

The surrounding theory assumes **independent coordinates**. In the application domain
linkage disequilibrium is central, and dependence would break the
product-of-characteristic-functions step that the associated Cramér-type argument rests
on. This is a structural limitation of the method, not a generalization waiting to be
written. It is carried below as the named field `independentCoordinates` of
`StandingHypotheses`, so that any statement relying on the modelling reading has it in
its signature rather than in prose.
-/

namespace Descent.BundleRigidity

open scoped BigOperators

variable {T : Type*} [TopologicalSpace T] {d : ℕ}

/-! ## The bundle family -/

/-- A **bundle family** with `d` atoms over a parameter space `T`.

At parameter `t` the family puts mass `mass j t` on the value `atom j t`. The four
standing identities say the masses are positive, form a probability vector, and
standardize the atom values to mean zero and variance one. All of them hold *at every
parameter simultaneously*, which is what ties the atoms into a bundle: no single atom can
be moved without moving the rest. -/
structure BundleFamily (T : Type*) [TopologicalSpace T] (d : ℕ) where
  /-- The value of atom `j` at parameter `t`, jointly continuous in `t`. -/
  atom : Fin d → C(T, ℝ)
  /-- The mass of atom `j` at parameter `t`, jointly continuous in `t`. -/
  mass : Fin d → C(T, ℝ)
  /-- Every atom carries strictly positive mass. This is the hypothesis that makes the
  peeling lemma's lower bound `Φ ≥ p_min` available. -/
  mass_pos : ∀ (j : Fin d) (t : T), 0 < mass j t
  /-- The masses form a probability vector at every parameter. -/
  mass_sum : ∀ t : T, ∑ j, mass j t = 1
  /-- Standardization: mean zero at every parameter. -/
  mean_zero : ∀ t : T, ∑ j, mass j t * atom j t = 0
  /-- Standardization: variance one at every parameter. -/
  var_one : ∀ t : T, ∑ j, mass j t * atom j t ^ 2 = 1

namespace BundleFamily

/-- **The symmetric two-atom family**, and with it the fact that the fifteen
theorems taking a `BundleFamily` parameter are about something.

`BundleFamily` bundles four `Prop` fields holding at every parameter
simultaneously, so a theorem taking one is conditional on a caller producing all
four at once. Until a closed term of the type exists, none of those theorems is
known to be non-vacuous — which is the difference between a hypothesis and a
class with no members.

Rademacher: two atoms at `+1` and `-1`, each of constant mass `1/2`. The four
identities are then arithmetic and hold at every `t` because nothing here
depends on `t`. This is the smallest family satisfying the standing identities:
one atom cannot have mean zero and variance one at once, since mass `1` forces
the atom to `0` and then the variance is `0`.

Constant in `t` on purpose. What is being discharged is inhabitation, and a
`t`-dependent witness would suggest the results below turn on the parameter
space, which they do not. -/
noncomputable def rademacher (T : Type*) [TopologicalSpace T] : BundleFamily T 2 where
  atom := ![ContinuousMap.const T (1 : ℝ), ContinuousMap.const T (-1 : ℝ)]
  mass := ![ContinuousMap.const T (1 / 2 : ℝ), ContinuousMap.const T (1 / 2 : ℝ)]
  -- `<;>` and not `;`: `simp` closes some of these four outright and leaves the
  -- rest as numerals, and a bare `; norm_num` fails with "no goals to be solved"
  -- on the ones it closed.
  mass_pos j _ := by fin_cases j <;> norm_num
  mass_sum _ := by simp [Fin.sum_univ_two] <;> norm_num
  mean_zero _ := by simp [Fin.sum_univ_two] <;> norm_num
  var_one _ := by simp [Fin.sum_univ_two] <;> norm_num

instance {T : Type*} [TopologicalSpace T] : Nonempty (BundleFamily T 2) :=
  ⟨rademacher T⟩

variable (F : BundleFamily T d)

/-- The **modulus curve** of atom `j`: `|atom j t ^ 2 - 1|`, the value taken by `|U|`
where `U = X ^ 2 - 1` is the centered square of the standardized value. -/
noncomputable def modulusMap (F : BundleFamily T d) (j : Fin d) : C(T, ℝ) :=
  ⟨fun t ↦ |F.atom j t ^ 2 - 1|,
    (((F.atom j).continuous.pow 2).sub continuous_const).abs⟩

@[simp] theorem modulusMap_apply (j : Fin d) (t : T) :
    F.modulusMap j t = |F.atom j t ^ 2 - 1| := rfl

/-- **Modulus values are non-negative**, so the operator really does land on `[0, ∞)`. -/
theorem modulusMap_nonneg (j : Fin d) (t : T) : 0 ≤ F.modulusMap j t := abs_nonneg _

/-! ## The adjoint operator `L*` -/

/-- **The adjoint `L*`**, as a map on test functions:
`(L* f) t = ∑ j, mass j t * f (modulusMap j t)`.

Equivalently this is the pairing of `f` against the transfer measure
`TT t = ∑ j, mass j t • δ (modulusMap j t)`. Everything in this file is a statement about
this one expression. -/
noncomputable def coTransfer (F : BundleFamily T d) (f : C(ℝ, ℝ)) : C(T, ℝ) :=
  ⟨fun t ↦ ∑ j, F.mass j t * f (F.modulusMap j t),
    continuous_finset_sum _ fun j _ ↦
      (F.mass j).continuous.mul (f.continuous.comp (F.modulusMap j).continuous)⟩

@[simp] theorem coTransfer_apply (f : C(ℝ, ℝ)) (t : T) :
    F.coTransfer f t = ∑ j, F.mass j t * f (F.modulusMap j t) := rfl

/-- `L*` is linear in the test function. -/
noncomputable def coTransferₗ (F : BundleFamily T d) : C(ℝ, ℝ) →ₗ[ℝ] C(T, ℝ) where
  toFun := F.coTransfer
  map_add' f g := by
    ext t
    simp only [coTransfer_apply, ContinuousMap.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  map_smul' c f := by
    ext t
    simp only [coTransfer_apply, ContinuousMap.smul_apply, RingHom.id_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

@[simp] theorem coTransferₗ_apply (f : C(ℝ, ℝ)) : F.coTransferₗ f = F.coTransfer f := rfl

/-- **`L*` fixes the constant function `1`.** This is the standardization identity
`∑ mass j t = 1` and nothing else, and it is the whole content of the mass identity. -/
@[simp] theorem coTransfer_one : F.coTransfer 1 = 1 := by
  ext t
  simp only [coTransfer_apply, ContinuousMap.one_apply, mul_one]
  exact F.mass_sum t

/-! ## The operator `L` and the mass identity (0.4) -/

/-- **The bundle modulus operator `L`.** A measure on parameters, represented as a linear
functional on `C(T, ℝ)`, is sent to the measure on modulus values obtained by pushing each
parameter to its transfer measure and integrating: `L κ = ∫ TT t dκ t`, which in the
Riesz picture is exactly precomposition with `L*`. -/
noncomputable def transfer (F : BundleFamily T d) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) :
    C(ℝ, ℝ) →ₗ[ℝ] ℝ :=
  κ.comp F.coTransferₗ

@[simp] theorem transfer_apply (κ : C(T, ℝ) →ₗ[ℝ] ℝ) (f : C(ℝ, ℝ)) :
    F.transfer κ f = κ (F.coTransfer f) := rfl

/-- **The mass identity (0.4): `L` preserves total mass.**

`(L κ) [0, ∞) = κ T`. In the Riesz picture the total mass of a measure is its value on the
constant function `1`, and the identity is immediate from `L* 1 = 1`, which is the
statement that the bundle masses sum to one.

This is the foundation of the whole development: it is what makes the operator
mass-preserving rather than merely positive, and it is the reason a kernel element must be
a signed measure of total mass zero. It is also what kills the Rademacher point in
Theorem E. -/
theorem transfer_one (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : F.transfer κ 1 = κ 1 := by
  rw [transfer_apply, coTransfer_one]

/-- **Corollary of the mass identity: every kernel element has total mass zero.**

If `L κ = 0` then `κ T = 0`. So the kernel of `L` consists entirely of signed measures
with cancelling positive and negative parts — no positive measure other than zero is ever
in the kernel, and in particular `L` is injective on the *cone* of positive measures of a
fixed total mass as soon as it is injective on differences. -/
theorem mass_eq_zero_of_mem_ker {κ : C(T, ℝ) →ₗ[ℝ] ℝ} (hκ : F.transfer κ = 0) :
    κ 1 = 0 := by
  rw [← F.transfer_one κ, hκ, LinearMap.zero_apply]

/-! ## Point masses, and Lemma 4 -/

/-- The Dirac measure at `t`, in the Riesz picture: evaluation at `t`. -/
def diracAt (t : T) : C(T, ℝ) →ₗ[ℝ] ℝ where
  toFun f := f t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem diracAt_apply (t : T) (f : C(T, ℝ)) : diracAt t f = f t := rfl

/-- **Two parameters with the same transfer measure**, i.e. `TT t₁ = TT t₂` tested against
every continuous function. -/
def SameTransfer (F : BundleFamily T d) (t₁ t₂ : T) : Prop :=
  ∀ f : C(ℝ, ℝ), F.coTransfer f t₁ = F.coTransfer f t₂

/-- A parameter has the same transfer as itself.

    Reflexivity is the witness, and it is the sharp one: at
    `t₁ = t₂` the conclusion `F.transfer (diracAt t₁ - diracAt t₂) = 0` is the
    trivial instance, so Lemma 4 has content exactly when the caller supplies
    `t₁ ≠ t₂` -- which is why the informal statement says "two DISTINCT
    parameters". Nothing here establishes that a distinct such pair exists for
    any particular family; that is what makes non-rigidity a property of `F`. -/
theorem sameTransfer_refl (F : BundleFamily T d) (t : T) : F.SameTransfer t t :=
  fun _ ↦ rfl

/-- **Lemma 4.** If two distinct parameters have the same transfer measure then their
difference of point masses is a kernel element. This is the cheapest possible source of
non-rigidity: an exact coincidence of whole bundles. -/
theorem transfer_dirac_sub_eq_zero {t₁ t₂ : T} (h : F.SameTransfer t₁ t₂) :
    F.transfer (diracAt t₁ - diracAt t₂) = 0 := by
  ext f
  simp only [transfer_apply, LinearMap.sub_apply, diracAt_apply, LinearMap.zero_apply]
  rw [h f, sub_self]

/-! ## Theorem B: symmetric families

The most important theorem here for the application. If the family is invariant under a
continuous involution `τ` of the parameter space, then the kernel of `L` always contains
every `τ`-odd measure, and the only remaining question is rigidity of the quotient family
on `T / τ`.
-/

/-- Pullback of test functions along a continuous self-map of the parameter space. -/
noncomputable def pullback (τ : C(T, T)) : C(T, ℝ) →ₗ[ℝ] C(T, ℝ) where
  toFun f := f.comp τ
  map_add' _ _ := by ext t; rfl
  map_smul' _ _ := by ext t; rfl

@[simp] theorem pullback_apply (τ : C(T, T)) (f : C(T, ℝ)) (t : T) :
    pullback τ f t = f (τ t) := rfl

/-- **`τ` is a symmetry of the family**: `TT ∘ τ = TT`, tested against every continuous
function. This is exactly the hypothesis of Theorem B. -/
def IsSymmetry (F : BundleFamily T d) (τ : C(T, T)) : Prop :=
  ∀ (f : C(ℝ, ℝ)) (t : T), F.coTransfer f (τ t) = F.coTransfer f t

/-- **A checkable sufficient condition for `IsSymmetry`**: `τ` permutes the atoms,
matching masses to masses and modulus values to modulus values.

This is the form in which the hypothesis is actually verified for a concrete family — for
the diploid genotype family the involution is `q ↦ 1 - q` and the permutation is the
reversal of the three genotype classes. -/
theorem isSymmetry_of_perm (τ : C(T, T)) (σ : Equiv.Perm (Fin d))
    (hmass : ∀ (j : Fin d) (t : T), F.mass j (τ t) = F.mass (σ j) t)
    (hmod : ∀ (j : Fin d) (t : T), F.modulusMap j (τ t) = F.modulusMap (σ j) t) :
    F.IsSymmetry τ := by
  intro f t
  simp only [coTransfer_apply]
  exact Fintype.sum_equiv σ _ _ fun j ↦ by rw [hmass j t, hmod j t]

/-- A measure is **`τ`-odd** when pulling back along `τ` negates it. -/
def IsTauOdd (τ : C(T, T)) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  κ.comp (pullback τ) = -κ

/-- A measure is **`τ`-even** when it is invariant under pullback along `τ`. -/
def IsTauEven (τ : C(T, T)) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  κ.comp (pullback τ) = κ

/-- **Theorem B (i): every `τ`-odd measure is in the kernel of `L`, always.**

No hypothesis on the family beyond `IsSymmetry`; no analyticity, no coverage condition,
nothing about the core. The proof is one line of algebra: `L* f` is `τ`-invariant because
`TT ∘ τ = TT`, and a `τ`-odd measure annihilates every `τ`-invariant function.

**This is the detector.** Any search for kernel elements that works only with
`L*`-functionals and reports nothing on a symmetric family is inconsistent with this
theorem and is therefore broken. It is the positive control every rigidity search must
pass before its null results mean anything. -/
theorem transfer_eq_zero_of_tauOdd {τ : C(T, T)} (hsym : F.IsSymmetry τ)
    {κ : C(T, ℝ) →ₗ[ℝ] ℝ} (hodd : IsTauOdd τ κ) :
    F.transfer κ = 0 := by
  ext f
  have hinv : pullback τ (F.coTransfer f) = F.coTransfer f := by
    ext t; exact hsym f t
  have h := congrArg (fun L ↦ L (F.coTransfer f)) hodd
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h
  rw [hinv] at h
  simp only [transfer_apply, LinearMap.zero_apply]
  linarith

/-- The `τ`-even part of a measure. -/
noncomputable def evenPart (τ : C(T, T)) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : C(T, ℝ) →ₗ[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (κ + κ.comp (pullback τ))

/-- The `τ`-odd part of a measure. -/
noncomputable def oddPart (τ : C(T, T)) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : C(T, ℝ) →ₗ[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • (κ - κ.comp (pullback τ))

/-- **Every measure splits into its `τ`-even and `τ`-odd parts.** -/
theorem evenPart_add_oddPart (τ : C(T, T)) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) :
    evenPart τ κ + oddPart τ κ = κ := by
  ext f
  simp only [evenPart, oddPart, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The even part is even, provided `τ` is an involution. -/
theorem isTauEven_evenPart {τ : C(T, T)} (hinv : ∀ t : T, τ (τ t) = t)
    (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : IsTauEven τ (evenPart τ κ) := by
  ext f
  have hff : pullback τ (pullback τ f) = f := by ext t; simp [hinv t]
  simp only [evenPart, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  rw [hff]
  ring

/-- The odd part is odd, provided `τ` is an involution. -/
theorem isTauOdd_oddPart {τ : C(T, T)} (hinv : ∀ t : T, τ (τ t) = t)
    (κ : C(T, ℝ) →ₗ[ℝ] ℝ) : IsTauOdd τ (oddPart τ κ) := by
  ext f
  have hff : pullback τ (pullback τ f) = f := by ext t; simp [hinv t]
  simp only [oddPart, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, smul_eq_mul]
  rw [hff]
  ring

/-- **Theorem B (ii), first half: `L` only sees the even part.**

`L κ = L (κ_+)`. Combined with `transfer_eq_zero_of_tauOdd` this is the statement that the
odd directions are entirely invisible to the operator. -/
theorem transfer_eq_transfer_evenPart {τ : C(T, T)} (hsym : F.IsSymmetry τ)
    (hinv : ∀ t : T, τ (τ t) = t) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) :
    F.transfer κ = F.transfer (evenPart τ κ) := by
  have hodd := F.transfer_eq_zero_of_tauOdd hsym (isTauOdd_oddPart hinv κ)
  ext f
  -- No `hsplit` at `f` here: after `ext`, `f : C(ℝ, ℝ)`, whereas `evenPart τ κ` eats
  -- `C(T, ℝ)`. The split is only ever needed at `F.coTransfer f`, which is where `h1`
  -- applies it.
  have hz : κ (F.coTransfer f) = evenPart τ κ (F.coTransfer f) := by
    have h1 : evenPart τ κ (F.coTransfer f) + oddPart τ κ (F.coTransfer f)
        = κ (F.coTransfer f) := by
      have := congrArg (fun L ↦ L (F.coTransfer f)) (evenPart_add_oddPart τ κ)
      simpa using this
    have h2 : oddPart τ κ (F.coTransfer f) = 0 := by
      have := congrArg (fun L ↦ L f) hodd
      simpa using this
    rw [h2, add_zero] at h1
    exact h1.symm
  simpa using hz

/-- **Theorem B (ii), second half: the kernel is the odd measures plus the even kernel,
and the two summands meet only at zero.**

A measure is in the kernel exactly when its even part is, and its odd part is
unconditionally in the kernel. So

`ker L = {τ-odd measures} ⊕ (ker L ∩ {τ-even measures})`,

and the second summand is the kernel of the quotient operator — see
`tauEven_eq_of_agree_on_symmetricFns` below for why even measures are the same thing as
measures on `T / τ`. -/
theorem mem_ker_iff_evenPart_mem_ker {τ : C(T, T)} (hsym : F.IsSymmetry τ)
    (hinv : ∀ t : T, τ (τ t) = t) (κ : C(T, ℝ) →ₗ[ℝ] ℝ) :
    F.transfer κ = 0 ↔ F.transfer (evenPart τ κ) = 0 := by
  rw [F.transfer_eq_transfer_evenPart hsym hinv κ]

/-- The odd and even summands intersect only in zero. -/
theorem eq_zero_of_tauOdd_of_tauEven {τ : C(T, T)} {κ : C(T, ℝ) →ₗ[ℝ] ℝ}
    (hodd : IsTauOdd τ κ) (heven : IsTauEven τ κ) : κ = 0 := by
  ext f
  have h1 := congrArg (fun L ↦ L f) hodd
  have h2 := congrArg (fun L ↦ L f) heven
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h1
  simp only [LinearMap.comp_apply] at h2
  simp only [LinearMap.zero_apply]
  linarith [h1, h2]

/-- A test function is **`τ`-invariant** when it descends to the quotient `T / τ`. -/
def IsInvariantFn (τ : C(T, T)) (f : C(T, ℝ)) : Prop := ∀ t : T, f (τ t) = f t

/-- **`L*` always lands in the `τ`-invariant test functions.** This is `TT ∘ τ = TT`
restated, and it is the reason the operator factors through the quotient. -/
theorem isInvariantFn_coTransfer {τ : C(T, T)} (hsym : F.IsSymmetry τ) (f : C(ℝ, ℝ)) :
    IsInvariantFn τ (F.coTransfer f) := fun t ↦ hsym f t

/-- **`τ`-even measures are exactly measures on the quotient `T / τ`**, in the only sense
needed here: an even measure is determined by its values on `τ`-invariant test functions.

Together with `isInvariantFn_coTransfer` this is the reduction the application needs. For
a symmetric family, `L` is blind to odd directions and factors through the quotient, so
**the entire identifiability question is rigidity of the quotient family**. For the
diploid genotype family at allele frequency `q`, the involution is `q ↦ 1 - q`, the odd
directions are exactly the relabelling of which allele is called minor — a gauge freedom,
not an ambiguity in the science — and the real question is rigidity on `(0, 1/2]`, which
is what Theorem E settles for `d = 2`. -/
theorem tauEven_eq_of_agree_on_symmetricFns {τ : C(T, T)} (hinv : ∀ t : T, τ (τ t) = t)
    {κ κ' : C(T, ℝ) →ₗ[ℝ] ℝ} (hκ : IsTauEven τ κ) (hκ' : IsTauEven τ κ')
    (hagree : ∀ f : C(T, ℝ), IsInvariantFn τ f → κ f = κ' f) : κ = κ' := by
  ext f
  -- Split `f` into its `τ`-invariant and `τ`-anti-invariant parts.
  set g : C(T, ℝ) := (2 : ℝ)⁻¹ • (f + pullback τ f) with hg
  set h : C(T, ℝ) := (2 : ℝ)⁻¹ • (f - pullback τ f) with hh
  have hsum : g + h = f := by ext t; simp [hg, hh]; ring
  have hginv : IsInvariantFn τ g := by
    intro t
    simp only [hg, ContinuousMap.smul_apply, ContinuousMap.add_apply, pullback_apply,
      smul_eq_mul, hinv t]
    ring
  -- The odd part is antiinvariant under the pullback, and that computation is what makes
  -- BOTH functionals vanish on it. It was written out once per functional, identically.
  have hodd : pullback τ h = -h := by
    ext t
    simp only [hh, pullback_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
      ContinuousMap.neg_apply, smul_eq_mul, hinv t]
    ring
  have vanishes_on_odd : ∀ L : C(T, ℝ) →ₗ[ℝ] ℝ, IsTauEven τ L → L h = 0 := by
    intro L hL
    have h1 := congrArg (fun M ↦ M h) hL
    simp only [LinearMap.comp_apply] at h1
    rw [hodd, map_neg] at h1
    linarith
  have hkh : κ h = 0 := vanishes_on_odd κ hκ
  have hk'h : κ' h = 0 := vanishes_on_odd κ' hκ'
  calc κ f = κ (g + h) := by rw [hsum]
    _ = κ g + κ h := map_add _ _ _
    _ = κ' g + κ' h := by rw [hagree g hginv, hkh, hk'h]
    _ = κ' (g + h) := (map_add _ _ _).symm
    _ = κ' f := by rw [hsum]

end BundleFamily

/-! ## The standing modelling limitation, in prose

A `StandingHypotheses` structure used to sit here with `independentCoordinates : Prop` and
`realizedPanel : Prop`, described as "carried explicitly so that they appear in the
signature of anything that uses them". **Nothing used them**, so they appeared in no
signature, and a `Prop`-valued field could not have carried the meaning anyway — it states
nothing and is satisfiable by `True`.

The limitation itself is real and stays recorded here:

**Independent coordinates.** The associated Cramér-type argument factors a characteristic
function as a product over coordinates. Under linkage disequilibrium that factorization
fails, so the argument does not apply to the case the application cares about most. This is
a structural limitation of the method rather than a gap awaiting work — and note that the
`Freshness` module exists precisely because of it, replacing the product step with a
telescope valid for any coupling.

**Realized panels.** The rigidity statements here are about finite realized panels, not
continuous mixing measures. Nothing in this module is stated for the continuum, and the
`d = 2` results in `TwoAtom` are the only complete continuum case in this development. -/

end Descent.BundleRigidity

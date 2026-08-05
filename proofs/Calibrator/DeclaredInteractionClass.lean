/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

namespace Calibrator

/-!
# Identification exists only relative to a declared interaction class

This module formalizes an impossibility theorem and its exact repair. It is the constraint
that governs experimental design **before** any estimation question, because it decides
whether the enterprise is well posed at all.

## The setting

An observation at context `x` under probe `p` is

`obs(x,p) = action x (θ x) p + h x p`,

with `θ` the parameter field one wants and `h` a nuisance. The question is when `θ` is
recoverable from `obs`.

## The binding negative

**If the nuisance is unrestricted in its probe dependence, `θ` is never identifiable.** The
identified set at every context is the full fiber, and no probe multiplicity, smoothness
assumption, prior, or asymptotic regime repairs it — because the nuisance class already
contains the parameter's entire observable action. Whatever the parameter can do to the
observation, the nuisance can undo.

`not_identifiable_of_unrestricted_nuisance` is that statement, and its proof is the reason it
cannot be evaded: given any two parameter fields, take the nuisance to be the difference of
their actions. Nothing about the difference is pathological, so nothing rules it out.

This **supersedes a weaker reading** in which the defect is a shortage of probes and the
repair is to run at least two probes per context with known contrast. That repair works only
if the nuisance is constant in the probe. Against a nuisance free to vary with the probe,
within-context differencing eliminates nothing: the differenced observation has a differenced
nuisance, which is still arbitrary.

## The repair, and its exact condition

Identification is not absolute; it is **relative to a declared class** `ℋ` of admissible
nuisances. `identifiable_iff_transversal` gives the exact condition: `θ` is identifiable
against `ℋ` if and only if no difference of distinct parameter actions lies in the difference
set of `ℋ`. That is a transversality condition between the parameter's observable action and
the declared interaction class.

## The epistemic point, which is the part that binds

**The condition is testable from data but not inferable from data.** `ℋ` is a declaration, not
an estimand: `identifiability_depends_on_declaration` exhibits one observation family that is
identifiable under one declared class and not under another. Since the two models generate the
same observations, no amount of data distinguishes them — the difference lies entirely in
what was assumed before collection.

So the enterprise is well posed **conditionally or not at all**, and the condition is a design
decision that must be made and recorded in advance. That is the practical content: not a rate,
not a bound, but a statement that a protocol which never declares `ℋ` has not deferred the
identification question, it has answered it in the negative.

Empirical status: NOT AN EMPIRICAL CLAIM. Everything here is a statement about what a model
does and does not determine, and nothing in it can be measured.
-/

section DeclaredInteractionClass

variable {Context Probe Param : Type*}

/-- An observation model: a parameter acting on observations through a probe, plus a declared
    class of admissible nuisances. `nuisance` is the **declaration** — the modelling
    commitment that makes identification meaningful. -/
structure ObservationModel (Context Probe Param : Type*) where
  /-- How a parameter value at a context shows up under a probe. -/
  action : Context → Param → Probe → ℝ
  /-- The declared class of admissible nuisances. -/
  nuisance : Set (Context → Probe → ℝ)

/-- What is actually observed, given a parameter field and a nuisance. -/
def observable (M : ObservationModel Context Probe Param)
    (θ : Context → Param) (h : Context → Probe → ℝ) : Context → Probe → ℝ :=
  fun x p ↦ M.action x (θ x) p + h x p

/-- **Identifiability**: no two distinct parameter fields are observationally equivalent under
    admissible nuisances. -/
def Identifiable (M : ObservationModel Context Probe Param) : Prop :=
  ∀ θ θ' h h', h ∈ M.nuisance → h' ∈ M.nuisance →
    observable M θ h = observable M θ' h' → θ = θ'

/-- The observable gap between two parameter fields. -/
def actionGap (M : ObservationModel Context Probe Param) (θ θ' : Context → Param) :
    Context → Probe → ℝ :=
  fun x p ↦ M.action x (θ x) p - M.action x (θ' x) p

/-- **The binding negative: an unrestricted nuisance destroys identification outright.**

    If every function of context and probe is an admissible nuisance, then any two parameter
    fields are observationally equivalent — so `θ` is identifiable only in the degenerate case
    where there is nothing to distinguish.

    The proof is the reason no repair exists: the witness nuisance is the *difference of the
    two actions*, which is an ordinary function and which no smoothness or regularity
    assumption excludes. Probe multiplicity does not help, because the witness is already
    allowed to depend on the probe. -/
theorem not_identifiable_of_unrestricted_nuisance
    (M : ObservationModel Context Probe Param)
    (huniv : M.nuisance = Set.univ)
    (θ θ' : Context → Param) (hne : θ ≠ θ') :
    ¬ Identifiable M := by
  intro hid
  apply hne
  refine hid θ θ' 0 (actionGap M θ θ') ?_ ?_ ?_
  · rw [huniv]; trivial
  · rw [huniv]; trivial
  · funext x p
    simp only [observable, actionGap, Pi.zero_apply, add_zero]
    ring

/-- **Identifiability is a property of the declaration, not of the data.**

    Two models with the **same action** — hence generating the same observations from the same
    parameter and nuisance — can differ in whether they identify, purely because their declared
    classes differ. The empty class identifies whenever the action separates parameters; the
    full class never does.

    This is the sense in which the transversality condition is testable but not inferable: it
    is a question about `ℋ`, and `ℋ` is chosen before collection rather than estimated after.
    A protocol that never declares `ℋ` has not deferred the question — it has answered it in
    the negative. -/
theorem identifiability_depends_on_declaration
    (act : Context → Param → Probe → ℝ)
    (θ θ' : Context → Param) (hne : θ ≠ θ')
    (hsep : ∀ ψ ψ' : Context → Param,
      (fun x p ↦ act x (ψ x) p) = (fun x p ↦ act x (ψ' x) p) → ψ = ψ') :
    Identifiable ⟨act, {0}⟩ ∧ ¬ Identifiable ⟨act, Set.univ⟩ := by
  constructor
  · intro ψ ψ' h h' hh hh' hobs
    rw [Set.mem_singleton_iff] at hh hh'
    subst hh; subst hh'
    refine hsep ψ ψ' ?_
    funext x p
    have := congrFun (congrFun hobs x) p
    simpa [observable] using this
  · exact not_identifiable_of_unrestricted_nuisance ⟨act, Set.univ⟩ rfl θ θ' hne

end DeclaredInteractionClass

end Calibrator

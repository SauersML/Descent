/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.HeredityKernel

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Operational autonomy: an observation is autonomous exactly when its law predicts its next law

The spec is `ANCESTRAL_LOCALITY.md` §3, Theorem 2 of the research note "Ancestral locality" of
11 September 2026. Kernels `K : H → H → H → ℝ` on a finite state set, observations `π : H → O`,
the population map `reproduce`, the pushforward `pushforward` and hereditary autonomy
`HereditarilyAutonomous` (2.2) are those of `HeredityKernel`.

**Theorem 2.** `hereditarilyAutonomous_iff_pushforward_reproduce_determined`: for a kernel that
does not see the order of the parents, these are equivalent.
(i) `π` is hereditarily autonomous.
(ii) `π_# R_K(p)` depends only on `π_# p`: any two probability vectors with the same observed law
have next generations with the same observed law.

(i) ⇒ (ii) holds for every kernel and every vector. `pushforward_reproduce_of_kernelMass_fiber_eq`
says the observed next generation is `R_K̄(π_# p)`, and
`exists_transition_law_of_hereditarilyAutonomous` reads this as a transition law on observed laws.
(ii) ⇒ (i) needs only point masses and two-point mixtures, as in the note.
`pushforward_reproduce_pointMass` reads `K(x,x;π⁻¹(o))` off `δ_x`, so the diagonal masses depend
only on `πx`. `pushforward_reproduce_pairMidpoint` is the polarization
`R_K(½δ_x + ½δ_y)(B) = ¼K(x,x;B) + ¼K(x,y;B) + ¼K(y,x;B) + ¼K(y,y;B)`. With symmetry the cross
term is `½K(x,y;B)`, so it too depends only on `(πx, πy)`
(`kernelMass_fiber_eq_of_pushforward_determined`), and `hereditarilyAutonomous_iff` gives
autonomy.

**Consequence.** `exists_pushforward_eq_reproduce_ne_of_not_hereditarilyAutonomous`: when autonomy
fails, some two probability vectors have the same observed marginal and different next-generation
observed laws.

Scope. Symmetry is assumed as `∀ x y z, K x y z = K y x z`, and nothing else of a heredity kernel
is used: the rows of `K` need not be probability vectors. Probability vectors are the points of
`stdSimplex ℝ H`. The observation need not be surjective. The eight-state witness of §5.2, a
concrete instance of the consequence, is not restated here.

## Empirical status

None. The bodies here are finite sums of supplied kernel weights; the kernel, the observation and
the populations are supplied, and no measurement can bear on an identity between finite sums.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H : Type*} [Fintype H] {O : Type*} [DecidableEq O]

/-- **The observed next generation of an autonomous observation.** When `K̄` satisfies (2.2),
`π_# R_K(p) = R_K̄(π_# p)` for every vector `p`. -/
theorem pushforward_reproduce_of_kernelMass_fiber_eq [Fintype O] (K : H → H → H → ℝ)
    (π : H → O) (Kbar : O → O → O → ℝ)
    (hKbar : ∀ x y o, kernelMass K x y (fiber π o) = Kbar (π x) (π y) o) (p : H → ℝ) :
    pushforward π (reproduce K p) = reproduce Kbar (pushforward π p) := by
  funext o
  rw [pushforward_reproduce]
  simp only [hKbar]
  exact sum_sum_mul_comp_eq_sum_sum_pushforward π p fun a b ↦ Kbar a b o

/-- **An autonomous observation has a transition law**: some map on observed laws sends
`π_# p` to `π_# R_K(p)` for every vector `p`. -/
theorem exists_transition_law_of_hereditarilyAutonomous [Fintype O] {K : H → H → H → ℝ}
    {π : H → O} (h : HereditarilyAutonomous K π) :
    ∃ F : (O → ℝ) → O → ℝ, ∀ p : H → ℝ,
      F (pushforward π p) = pushforward π (reproduce K p) := by
  obtain ⟨Kbar, hKbar⟩ := h
  exact ⟨reproduce Kbar, fun p ↦
    (pushforward_reproduce_of_kernelMass_fiber_eq K π Kbar hKbar p).symm⟩

variable [DecidableEq H]

/-- The observed next generation from a point mass `δ_x` is the fiber mass `K(x,x;π⁻¹(o))`. -/
theorem pushforward_reproduce_pointMass (K : H → H → H → ℝ) (π : H → O) (x : H) (o : O) :
    pushforward π (reproduce K (pointMass x)) o = kernelMass K x x (fiber π o) :=
  (pushforward_reproduce K π _ o).trans
    (sum_sum_pointMass x fun a b ↦ kernelMass K a b (fiber π o))

/-- **Polarization of the observed next generation.** From `½δ_x + ½δ_y` the observed mass of
`π⁻¹(o)` is `¼K(x,x;B) + ¼K(x,y;B) + ¼K(y,x;B) + ¼K(y,y;B)` with `B = π⁻¹(o)`. -/
theorem pushforward_reproduce_pairMidpoint (K : H → H → H → ℝ) (π : H → O) (x y : H) (o : O) :
    pushforward π (reproduce K (pairMidpoint x y)) o =
      2⁻¹ * (2⁻¹ * (kernelMass K x x (fiber π o) + kernelMass K x y (fiber π o)) +
        2⁻¹ * (kernelMass K y x (fiber π o) + kernelMass K y y (fiber π o))) :=
  (pushforward_reproduce K π _ o).trans
    (sum_sum_pairMidpoint x y fun a b ↦ kernelMass K a b (fiber π o))

/-- **Operational invariance fixes the fiber masses.** If the observed law of every probability
vector determines the observed law of its next generation, and `K` is symmetric in the parents,
then `K(x,y;π⁻¹(o))` depends on the parents only through `πx` and `πy`. -/
theorem kernelMass_fiber_eq_of_pushforward_determined (K : H → H → H → ℝ)
    (hK : ∀ x y z, K x y z = K y x z) (π : H → O)
    (hdet : ∀ p ∈ stdSimplex ℝ H, ∀ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q →
      pushforward π (reproduce K p) = pushforward π (reproduce K q))
    {x x' y y' : H} (hx : π x = π x') (hy : π y = π y') (o : O) :
    kernelMass K x y (fiber π o) = kernelMass K x' y' (fiber π o) := by
  have hdiag : ∀ u u', π u = π u' →
      kernelMass K u u (fiber π o) = kernelMass K u' u' (fiber π o) := by
    intro u u' hu
    have h := congrFun (hdet _ (pointMass_mem_stdSimplex u) _ (pointMass_mem_stdSimplex u')
      (by rw [pushforward_pointMass, pushforward_pointMass, hu])) o
    rwa [pushforward_reproduce_pointMass, pushforward_reproduce_pointMass] at h
  have h := congrFun (hdet _ (pairMidpoint_mem_stdSimplex x y) _
    (pairMidpoint_mem_stdSimplex x' y')
    (by rw [pushforward_pairMidpoint, pushforward_pairMidpoint, hx, hy])) o
  rw [pushforward_reproduce_pairMidpoint, pushforward_reproduce_pairMidpoint] at h
  have hsym : ∀ u v, kernelMass K v u (fiber π o) = kernelMass K u v (fiber π o) :=
    fun u v ↦ Finset.sum_congr rfl fun z _ ↦ hK v u z
  have h1 := hdiag x x' hx
  have h2 := hdiag y y' hy
  rw [hsym x y, hsym x' y'] at h
  linarith

/-- **Theorem 2 (operational characterization).** For a kernel symmetric in the two parents, an
observation is hereditarily autonomous (2.2) exactly when `π_# R_K(p)` depends only on `π_# p`
for every probability vector `p`. -/
theorem hereditarilyAutonomous_iff_pushforward_reproduce_determined [Fintype O]
    (K : H → H → H → ℝ) (hK : ∀ x y z, K x y z = K y x z) (π : H → O) :
    HereditarilyAutonomous K π ↔
      ∀ p ∈ stdSimplex ℝ H, ∀ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q →
        pushforward π (reproduce K p) = pushforward π (reproduce K q) := by
  constructor
  · rintro ⟨Kbar, hKbar⟩ p _ q _ hpq
    rw [pushforward_reproduce_of_kernelMass_fiber_eq K π Kbar hKbar,
      pushforward_reproduce_of_kernelMass_fiber_eq K π Kbar hKbar, hpq]
  · intro hdet
    rw [hereditarilyAutonomous_iff]
    intro x x' y y' hx hy w
    simp only [blockMass, block_ker]
    exact kernelMass_fiber_eq_of_pushforward_determined K hK π hdet (Setoid.ker_def.mp hx)
      (Setoid.ker_def.mp hy) (π w)

/-- **Failure of autonomy is visible in populations.** For a symmetric kernel and an observation
that is not hereditarily autonomous, some two probability vectors have the same observed law and
next generations with different observed laws. -/
theorem exists_pushforward_eq_reproduce_ne_of_not_hereditarilyAutonomous [Fintype O]
    (K : H → H → H → ℝ) (hK : ∀ x y z, K x y z = K y x z) (π : H → O)
    (h : ¬ HereditarilyAutonomous K π) :
    ∃ p ∈ stdSimplex ℝ H, ∃ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q ∧
      pushforward π (reproduce K p) ≠ pushforward π (reproduce K q) := by
  by_contra hne
  push_neg at hne
  exact h ((hereditarilyAutonomous_iff_pushforward_reproduce_determined K hK π).mpr hne)

end

end Descent.Pangenome.AncestralLocality

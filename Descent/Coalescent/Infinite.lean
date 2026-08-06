/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Restriction
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# `𝓔` is the projective limit of the `𝓔ₙ`

Kingman's infinite coalescent lives on `𝓔`, the equivalence relations on `ℕ` (K-C section 2,
K-G section 7).  Both papers reach it the same way: `ρ_n : 𝓔 → 𝓔ₙ` restricts, the restrictions
are consistent (K-G (7.2)), and a process on `𝓔` is specified by giving compatible processes
on every `𝓔ₙ`.  K-C Theorem 3 and K-G section 7 then put a measure on `𝓔` by a projective
limit argument -- the "topological Kakutani-Nelson technique", in K-G's words.

That measure-theoretic step is not here, and `Descent.Coalescent.Program` says so.  What IS
here is the step underneath it, which is not measure theory at all: `𝓔` really is the
projective limit of the `𝓔ₙ` AS A SET.  A compatible family of finite relations determines
one relation on `ℕ`, and determines it uniquely.  Without that, "specify the process by its
restrictions" would not even be well posed; with it, what remains for Theorem 3 is exactly
the extension of a consistent family of MEASURES, and nothing about the state space.

The construction is the obvious one and the work is in making it total: `i` and `j` are
related when they are related in `ξ_N` for some `N` past both, and `rel_indep` says the
choice of `N` does not matter.  That is where compatibility is used, and it is used nowhere
else.

## Main results

- `restrictInf`: `ρ_n`, K-C (2.7).
- `restrictInf_restrict`: K-G (7.2) for the infinite maps, `ρ_{mn} ∘ ρ_n = ρ_m`.
- `rel_indep`: a compatible family gives the same answer at every large enough index.
- `ofCompatible`: the relation on `ℕ` a compatible family determines.
- `restrictInf_ofCompatible`: it restricts back to the family -- existence.
- `eq_ofCompatible`: and it is the only one that does -- uniqueness.
-/

namespace Coalescent

/-- `𝓔`, Kingman's state space for the coalescent proper: equivalence relations on `ℕ`. -/
abbrev EInf := Setoid ℕ

/-- **K-C (2.7): `ρ_n`**, the restriction of a relation on `ℕ` to `{1, …, n}`. -/
def restrictInf (n : ℕ) (R : EInf) : ER n := Setoid.comap (fun i : Fin n ↦ (i : ℕ)) R

theorem restrictInf_rel (n : ℕ) (R : EInf) (x y : Fin n) :
    (restrictInf n R).r x y ↔ R.r (x : ℕ) (y : ℕ) := Iff.rfl

/-- **K-G (7.2) for the infinite maps.**  Restricting to `n` and then to `m` is restricting
to `m`: the consistency that makes "a process on `𝓔` is its family of restrictions"
meaningful. -/
theorem restrictInf_restrict {m n : ℕ} (h : m ≤ n) (R : EInf) :
    restrict h (restrictInf n R) = restrictInf m R :=
  Setoid.ext fun _ _ ↦ Iff.rfl

/-- **A compatible family gives the same answer at every large enough index.**  This is the
only place compatibility is used, and it is what makes the limit relation well defined. -/
theorem rel_indep {ξ : ∀ n, ER n}
    (hcomp : ∀ (m n : ℕ) (h : m ≤ n), restrict h (ξ n) = ξ m)
    {i j M N : ℕ} (hiM : i < M) (hjM : j < M) (hiN : i < N) (hjN : j < N) :
    ((ξ M).r ⟨i, hiM⟩ ⟨j, hjM⟩ ↔ (ξ N).r ⟨i, hiN⟩ ⟨j, hjN⟩) := by
  have key : ∀ {P Q : ℕ} (hPQ : P ≤ Q) (hiP : i < P) (hjP : j < P) (hiQ : i < Q) (hjQ : j < Q),
      ((ξ P).r ⟨i, hiP⟩ ⟨j, hjP⟩ ↔ (ξ Q).r ⟨i, hiQ⟩ ⟨j, hjQ⟩) := by
    intro P Q hPQ hiP hjP hiQ hjQ
    have hres := hcomp P Q hPQ
    constructor
    · intro hr
      have : (restrict hPQ (ξ Q)).r ⟨i, hiP⟩ ⟨j, hjP⟩ := by
        rw [hres]
        exact hr
      have hcast : (restrict hPQ (ξ Q)).r ⟨i, hiP⟩ ⟨j, hjP⟩
          ↔ (ξ Q).r (Fin.castLE hPQ ⟨i, hiP⟩) (Fin.castLE hPQ ⟨j, hjP⟩) := Iff.rfl
      have hi : (Fin.castLE hPQ (⟨i, hiP⟩ : Fin P)) = (⟨i, hiQ⟩ : Fin Q) := Fin.ext rfl
      have hj : (Fin.castLE hPQ (⟨j, hjP⟩ : Fin P)) = (⟨j, hjQ⟩ : Fin Q) := Fin.ext rfl
      rw [hcast, hi, hj] at this
      exact this
    · intro hr
      have hcast : (restrict hPQ (ξ Q)).r ⟨i, hiP⟩ ⟨j, hjP⟩
          ↔ (ξ Q).r (Fin.castLE hPQ ⟨i, hiP⟩) (Fin.castLE hPQ ⟨j, hjP⟩) := Iff.rfl
      have hi : (Fin.castLE hPQ (⟨i, hiP⟩ : Fin P)) = (⟨i, hiQ⟩ : Fin Q) := Fin.ext rfl
      have hj : (Fin.castLE hPQ (⟨j, hjP⟩ : Fin P)) = (⟨j, hjQ⟩ : Fin Q) := Fin.ext rfl
      have hback : (restrict hPQ (ξ Q)).r ⟨i, hiP⟩ ⟨j, hjP⟩ := by
        rw [hcast, hi, hj]
        exact hr
      rw [hres] at hback
      exact hback
  rcases le_total M N with hMN | hNM
  · exact key hMN hiM hjM hiN hjN
  · exact (key hNM hiN hjN hiM hjM).symm

/-- **The relation on `ℕ` a compatible family determines.**  Two naturals are related when
they are related in any member of the family past both -- `rel_indep` says "any" is
unambiguous.

Empirical status: NOT AN EMPIRICAL CLAIM.  A construction of a relation on `ℕ` from a
consistent family of relations on its initial segments. -/
def ofCompatible (ξ : ∀ n, ER n)
    (hcomp : ∀ (m n : ℕ) (h : m ≤ n), restrict h (ξ n) = ξ m) : EInf where
  r i j := (ξ (max i j + 1)).r ⟨i, by omega⟩ ⟨j, by omega⟩
  iseqv := by
    constructor
    · intro i
      exact (ξ (max i i + 1)).iseqv.refl _
    · intro i j hij
      have := (ξ (max i j + 1)).iseqv.symm hij
      exact (rel_indep hcomp (by omega) (by omega) (by omega) (by omega)).mp this
    · intro i j k hij hjk
      have hij' : (ξ (max (max i j) (max j k) + 1)).r ⟨i, by omega⟩ ⟨j, by omega⟩ :=
        (rel_indep hcomp (by omega) (by omega) (by omega) (by omega)).mp hij
      have hjk' : (ξ (max (max i j) (max j k) + 1)).r ⟨j, by omega⟩ ⟨k, by omega⟩ :=
        (rel_indep hcomp (by omega) (by omega) (by omega) (by omega)).mp hjk
      have := (ξ (max (max i j) (max j k) + 1)).iseqv.trans hij' hjk'
      exact (rel_indep hcomp (by omega) (by omega) (by omega) (by omega)).mp this

/-- **Existence: the limit relation restricts back to the family.**  This is what makes
`ofCompatible` a projective limit and not merely a construction. -/
theorem restrictInf_ofCompatible (ξ : ∀ n, ER n)
    (hcomp : ∀ (m n : ℕ) (h : m ≤ n), restrict h (ξ n) = ξ m) (n : ℕ) :
    restrictInf n (ofCompatible ξ hcomp) = ξ n := by
  refine Setoid.ext fun x y ↦ ?_
  show (ξ (max (x : ℕ) (y : ℕ) + 1)).r ⟨(x : ℕ), by omega⟩ ⟨(y : ℕ), by omega⟩ ↔ (ξ n).r x y
  have hx : (x : ℕ) < n := x.isLt
  have hy : (y : ℕ) < n := y.isLt
  have h := rel_indep (ξ := ξ) hcomp (i := (x : ℕ)) (j := (y : ℕ))
    (M := max (x : ℕ) (y : ℕ) + 1) (N := n) (by omega) (by omega) hx hy
  have hx' : (⟨(x : ℕ), hx⟩ : Fin n) = x := Fin.ext rfl
  have hy' : (⟨(y : ℕ), hy⟩ : Fin n) = y := Fin.ext rfl
  rw [h, hx', hy']

/-- **Uniqueness: nothing else restricts to the family.**  Two relations on `ℕ` with the same
restrictions are equal, because any pair of naturals is inside some initial segment.  With
`restrictInf_ofCompatible`, this is the projective limit property in full, and it is what
K-C Theorem 3's measure-theoretic argument sits on top of. -/
theorem eq_ofCompatible {R S : EInf} (h : ∀ n, restrictInf n R = restrictInf n S) : R = S := by
  refine Setoid.ext fun i j ↦ ?_
  have hn := h (max i j + 1)
  constructor
  · intro hr
    have : (restrictInf (max i j + 1) R).r ⟨i, by omega⟩ ⟨j, by omega⟩ := hr
    rw [hn] at this
    exact this
  · intro hr
    have : (restrictInf (max i j + 1) S).r ⟨i, by omega⟩ ⟨j, by omega⟩ := hr
    rw [← hn] at this
    exact this

end Coalescent

end Descent

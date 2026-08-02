# Condensation: what a polygenic aggregate can and cannot forget

Eight Lean modules, one validation script. This document is the map: what is claimed,
what is proved, what is assumed, and what is borrowed.

The arc starts from a question about polynomial chaos and ends with a closed-form
population-genetic quantity that nobody was computing, a specific allele frequency at
which the standard diagnostic goes blind, and a bound on how far the Gaussian
polygenic-score apparatus may be extrapolated.

---

## 1. The one-line mechanism

A polygenic score is an aggregate of many small contributions, and every distributional
statement about it — the Gaussian score assumption, liability-threshold calibration,
the Berry–Esseen certificates already in `Calibrator.Probability` — rests on the claim
that *a low-influence aggregate of genotypes behaves as if the genotypes were Gaussian*.

At degree one this is true and quantitative. At diverging multiplicative degree it is
false, and the reason is not additive:

> A product of `m` independent standardized factors turns the **diagonal** data of the
> coordinate law — exactly the data that low influence suppresses *additively* — into
> an exponential separation of scale. Low influence controls additive resummation of
> diagonals. Nothing in the hypotheses controls their multiplicative accumulation.

The controlling object is the Mellin exponent `ψ(θ) = log E|x|^{2θ}` at the interior
point `θ = 1` — the size-bias point — not the jet at the origin, which is what cumulants
are. One line does all the work (`MellinProfile.tangency`):

```
I(s) ≥ s,  with equality iff s = E[x² log x²]
```

Take `θ = 1` in the Legendre supremum and use `ψ(1) = 0`. The diagonal is tangent from
below to *every* rate function, tangent exactly at the size-bias mean. Because
variance-normalized chaos probes values of size `~N` at cost `m·I(log N / m) ≥ log N`,
every independent-monomial design is pinned to `θ = 1`. Everything else is this read
three ways.

---

## 2. Modules

| module | contains |
|---|---|
| `Calibrator/ObservationalCeiling.lean` | the shared law: `ProbeBlindness`, `LeveledBlindness`, `IsCompleteCatalogue`, `IsCountablyCertified`, and the σ-compact ceiling transport. The five impossibility results below are instances of it, and contribute only their witness pairs |
| `Calibrator/Condensation.lean` | Tangency Lemma; `condensationConstant` `c_G = 2 − γ − log 2` with rigorous bounds; `gaussianJetVariance` `v_G = π²/2 − 4`; the sharp boundary `m* = log N / c`; the condensation-window law `N(0, Φ(w/√v))` |
| `Calibrator/CumulantBlindness.lean` | hidden-tilt cumulant matching to any order `K` (pigeonhole core); the diagonal-contraction bound `O(τ^{(r−2)/2})`; the non-characterization meta-theorems |
| `Calibrator/JetBarrier.lean` | the **trichotomy**: independent designs observe exactly `(c, v, lattice datum)`; lattice inflation `h/(1−e^{−h}) > 1`; chameleon calibration |
| `Calibrator/LocalToGlobalCoherence.lean` | expander frustration floor `1/2 − √5/6 > 0.127`; average-TV gap; twin impossibility for bounded-radius audits |
| `Calibrator/HiddenConeAmbiguity.lean` | Lemma W (witness uniqueness); bounded-log-distortion fiber; the σ-compact ceiling; the exact reduction; rigidity iff mixing bounded below |
| `Calibrator/LatentMechanismCollapse.lean` | head/tail collapse construction; minimal latent dimension is constantly `1`; Choquet repair |
| `Calibrator/PolygenicSpectroscopy.lean` | **the genetics**: closed-form Hardy–Weinberg Mellin drift, its anchors, the rare-variant divergence, the safe epistatic order, the hard-call lattice point |
| `Calibrator/CondensationUnification.lean` | ploidy guard, scale-invariance guard, and the five bridges to existing modules |
| `proofs/validation/condensation/check_condensation.py` | recomputes every constant twice and samples the phase transition |

---

## 3. The biology, as falsifiable statements

### 3.1 A new closed-form quantity

For a Hardy–Weinberg locus at alternative-allele frequency `q`, with `x` the
standardized genotype:

```
c(q) = E[x² log x²] = (1 − 2q)² · log( (1 − 2q)² / (2q(1−q)) )  +  4q(1−q) · log 2
```

`HardyWeinbergModel.mellinDrift_eq` proves this against the direct genotype sum, and
the validation script checks it numerically across the frequency spectrum. It is not a
moment and not a cumulant, and no bounded-order moment diagnostic determines it.

### 3.2 The safe epistatic order

`m*(N, q) = log N / c(q)` is the largest interaction order at which the Gaussian
genotype surrogate is valid for an aggregate of `N` disjoint terms. At `N = 10⁶`:

| `q` | `c(q)` | `m*` |
|---|---|---|
| 0.50 | 0.6931 | 19.9 |
| 0.2764 | 0.4159 | 33.2 |
| 0.20 | 0.4860 | 28.4 |
| 0.14 | 0.7313 | 18.9 |
| 0.05 | 1.8676 | 7.4 |
| 0.01 | 3.7554 | 3.7 |
| 0.001 | 6.1896 | 2.2 |
| 0.0001 | 8.5138 | 1.6 |

**The claim worth arguing about is the last row.** At MAF `10⁻⁴`, *pairwise* interaction
terms already exceed the safe order. A pairwise-epistasis model over ultra-rare variants
is past the condensation boundary, so its Gaussian-surrogate null — the one used to
calibrate interaction tests and set score percentiles — converges to a different limit,
and sample size does not repair it. The Gaussian side *condenses*, so the surrogate
under-disperses: such statistics are anticonservative in exactly the regime where the
literature can least check them empirically.

The additive apparatus is untouched and provably so
(`additive_score_subcritical_at_balanced_locus_proved`).

### 3.3 The drift-blind band

`c(q)` is **non-monotone**. It falls from `log 2 = 0.6931` at `q = 1/2` to a minimum
near `q ≈ 0.276` — where it is *exactly* `(3/5) log 2`, proved — then diverges as
`q → 0`, exceeding `c_G` already at `q = 1/256`, also proved. So the genotype drift
**crosses** the Gaussian constant, numerically near `q ≈ 0.140`.

At that crossing frequency the *first* observable is blind. The genotype law is
distinguished from its Gaussian surrogate only by the jet variance and the lattice
datum — the two quantities that no moment-based or cumulant-based method can compute.
This is why the trichotomy is a biological necessity, not a technical refinement: the
blind band sits squarely inside the frequency range that dominates real scores.

### 3.4 Hard calls are lattice; dosages are not

Hard-called genotypes take three values, so `log x²` has finite support. At the exact
frequency

```
q* = (2 − √2)/4 = 0.146447…
```

the three values of `log x²` form an **exact arithmetic progression** with span
`h = log(3 + 2√2) = 1.7627…` (proved: `(1 − 2q)² = 4q(1−q)` there). The law is lattice,
and the Poisson exceedance intensity is inflated by `h/(1 − e^{−h}) = 2.128…` relative
to any nonlattice law with the same 2-jet.

So hard calls and imputed dosages are not exchangeable at high epistatic order **even
after matching every moment** — a mechanism distinct from the `r²` attenuation in
`Calibrator.ImputationPortability`, which is a rescaling and is repaired by rescaling.
`standardizedSquare_scale_invariant` proves the whole observable triple is
rescaling-invariant, which is exactly why rescaling cannot repair it.

### 3.5 Two conventions, made explicit

* **Number of PCs.** The loading-decay profile is absent from the complete second-order
  observables; polynomial, exponential, and tower decay are observationally identical
  at infinite sample size with no noise. Identifiability holds **iff** the mixing is
  bounded below. Below that, the ambiguity jumps from trivial to maximal with nothing in
  between. `Calibrator.PCCorrectability` answers the right question — what correction
  achieves *given* a convention.
* **Number of GxE mechanisms.** Every smooth positive family of context-specific
  kernels factors exactly through a one-dimensional latent space, so the minimal latent
  dimension is constantly `1` and carries no information. The repair is the
  Choquet-boundary condition — in genetics, the archetypal-analysis requirement that
  mechanisms be extremal rather than interior blends.

---

## 4. Honesty labels

**Proved outright.** Tangency Lemma and its operational form; the constants and their
bounds (from mathlib's Euler–Mascheroni and `log 2` bounds); the phase-boundary
algebra; window monotonicity; the pigeonhole behind cumulant matching; the
diagonal-contraction bound and its vanishing; lattice inflation `> 1` and its
normalization; the frustration floor and the average-TV bound; both twin impossibility
theorems; Lemma W; the fiber equivalence relation, the σ-compact ceiling, the explicit
reduction, and the rigidity boundary; head/tail exactness and both positivity budgets;
minimal-dimension collapse; **all** of the genetics in §3.

**Carried as named hypotheses, visible at the type level.** Stone's local CLT and the
lattice local CLT (fields of `ChaosSpectroscopy`); Gnedenko–Kolmogorov triangular-array
convergence; the smoothness bookkeeping in the collapse construction (elliptic
regularity for the conditional eigenbasis, `C^k` convergence of the tail series).

**Deliberately understated.** The hidden-tilt construction is, under centering, a
mean-shift artifact — its letter stands, its force is reduced. The diagonal-contraction
bound is near-tautological relative to the class of criteria it quantifies over, which
we define ourselves. Neither is load-bearing.

**Not proved anywhere here.** That the conclusions survive linkage disequilibrium
*between* the loci entering one monomial. Every design used is disjoint-support, i.e.
the independent-design regime. Overlapping designs are the open direction, and in the
genetics reading overlap is exactly LD.

**Retracted, unconditionally.** The claim that the hidden-model relation lies "strictly
above every Polish-orbit equivalence relation" is false and contradicted its own Borel
ceiling; the correct statement is *incomparability*. The "third regime" framing is
empty — the universal σ-compact relation is itself Borel and already occupies that
position. An earlier permutation clause in the fiber classification was wrong; Lemma W
forces the witness to be diagonal, and the corrected statement has no permutation.

---

## 5. Attribution ledger

Recorded **before** any novelty claim, per the standing rule of two searches per
document.

* Ben Arous–Bogachev–Molchanov, *Limit theorems for sums of random exponentials*,
  PTRF **132** (2005) — the phase-transition mechanism and its two critical points.
  `condensationConstant` is an **evaluation** of their second critical point for
  `log g²` increments. It is not a new constant.
* Bovier–Kurkova–Loewe, Ann. Probab. **30** (2002) — the parallel REM fluctuation phase
  diagram; the same universality class. The window law is presented as at best a
  boundary-window refinement inside that framework, pending a line-by-line comparison.
* Huang–Austern–Orbanz, arXiv:2403.10711 — nearly optimal upper *and lower* bounds for
  Gaussian universality of approximately polynomial functions. The condensation
  counterexample lives in their lower-bound territory.
* Ando–Matsuzawa, arXiv:1405.0860 — the published landing pattern (bireducibility with
  the `ℓ∞` orbit relation, σ-compact universality, the Kechris–Louveau corollary) for
  the domain relation on self-adjoint operators, an operator-range relation adjacent to
  the Douglas coordinate. The complexity destination is a known address reached by a
  known road.
* Lubotzky–Phillips–Sarnak Ramanujan graphs, the eigenvalue bound on max-cut, and tree
  propagation are classical; §3 of the local-to-global module is in essence the analytic
  form of known Sherali–Adams integrality gaps for max-cut on expanders.
* Rosendal (universal `K_σ` relation) and Kechris–Louveau (`E₁` versus Polish orbits)
  are load-bearing citations, standard.

What remains ours after this ledger: the *completeness-of-blindness* formulation
(quantifying over designs rather than fixing a test law), the lattice-detection half of
the trichotomy, the twin packaging of the local-to-global construction, Lemma W and the
Douglas form for *this* model equivalence together with the refutation of the problem's
own wildness alternative, the convex-geometric head/tail repair of the collapse, and —
the part that actually matters here — the entire genetics transport in §3, which is new
because nobody had reason to compute `E[x² log x²]` for a genotype.

---

## 6. Reproducing

```bash
# Lean
lake build

# numerics: every constant twice, plus a sampled phase transition
python3 proofs/validation/condensation/check_condensation.py
```

The validation script exists for the reason `Calibrator.Identification` states: a Lean
`def` cannot be internally wrong, so the entire risk sits in whether a named quantity's
*formula* has the meaning its *name* claims. `hweMellinDrift` is computed both by direct
summation over the three diploid genotypes and by the closed form, and the two are
required to agree to `10⁻⁹`. `CondensationUnification.mellinDrift_uses_ploidy` ties the
standardization back to the corpus-wide `ploidy` constant, so drift between the new
quantities and the old ones is a compile error rather than a silent disagreement.

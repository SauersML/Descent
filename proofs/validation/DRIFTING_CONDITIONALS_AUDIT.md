# Trust audit: *Drifting Conditionals*

This audit applies four separate tests to the supplied manuscript:

1. **Kernel validity:** is there a Lean proof with no admissions or custom axioms?
2. **Evaluation validity:** is the stated result proved, rather than passed in as a premise?
3. **Intent validity:** do the hypotheses express the mathematical claim in the prose?
4. **Engineering validity:** is the result replayable and free of hidden domain conventions?

The finite-state results listed below are checked in
`Calibrator.DriftingConditional` and `Calibrator.DriftingConditionals`. They use no
`sorry`, `admit`, custom axiom, or native evaluator. The continuum claims remain outside the
trusted corpus until their analytic foundations and missing arguments are formalized.

## Results already repaired and proved

| Manuscript claim | Checked replacement | Repair |
|---|---|---|
| Frozen marks and population follow one transport | `transportMass_compose`, `transportedResponse_mul_population` | Finite kernels make the common forward equation exact. Empty destination cells are excluded by a proof, not totalized division. |
| Prevalence is conserved | `transportedResponse_prevalence_conserved` | The kernel normalization is explicit. |
| The marginal builds a reverse bridge | `reverseBridge_mass_preserving`, `transportedResponse_eq_reverseBridge_average` | Bayes reversal is constructed from the population and proved to normalize. |
| Forward reconstruction is non-expansive | `transportedResponse_mem_Icc`, `transportedResponse_dist_le` | A finite maximum principle proves the constant-one bound. `transportedResponse_add_const` proves sharpness. |
| Reconstruction has a tower law | `transportedResponse_compose` | Sequential and composed transport are proved identical. |
| A stationary marginal does not identify a conditional | `stationaryMarginal_does_not_identify_conditional` | Two explicit opposite response curves share one stationary population path. |
| Static threshold gauge | `indicator_lt_eq_of_strictMono`, `linkedCurve_identified_modulo_constants` | Strict monotonicity and the remaining additive gauge are explicit. |
| Dynamic threshold separation | `invariantAverage_eq_neg_of_affine_evolution` | The invariant weight, unit mass, generator, and finite dynamics are all visible hypotheses. |
| Constant forcing destroys separation | `constantForcing_conflates_threshold` | The exact unidentified combination is proved. |
| Continuous invariants collapse at a mixing limit | `continuousInvariant_eq_at_limit` | Continuity, invariance, convergence, and Hausdorff uniqueness are explicit. |
| Interior constant-one stability | `interiorError_sq_le_mul_endpoints`, `singleMode_interiorError_eq` | The finite spectral midpoint inequality and its equality case are proved without taking a logarithm of zero. |
| Forward spectral-gap contraction | `errorEnergy_forward_le`, `singleMode_errorEnergy_forward_eq` | Nonnegative weights, the rate lower bound, and the nonnegative horizon are explicit; a single mode proves sharpness. |
| OU parameter formulas have valid domains | `OUHorizon`, `ouVariance_nonneg`, `probitScaleFactor_pos` | Positive rate and nonnegative time prevent zero division and negative-time variance. The shared scale is proved nonzero instead of assumed. |

## Defects in claims labelled “proved here”

### Impossibility I.1: measurable images do not preserve dimension

The manuscript assumes only that `t ↦ c_t` is measurable and then says its image has dimension
at most `dim T`. That dimension assertion is false without a smooth or otherwise
dimension-controlled map; measurable maps can have space-filling images. The finite realization
by the state `T` is still a valid observation, but the dimension sentence is not its proof.

### Theorem 2: missing semigroup and domain hypotheses

The step “differentiate inside the finite-dimensional invariant space” needs a strongly
continuous semigroup and a finite-dimensional semigroup argument showing that the restricted
orbit lies in the generator domain. Self-adjointness alone does not justify the differentiation
as written. The conclusion is standard under the repaired hypotheses, but the supplied proof is
not complete at its stated hypotheses.

### Theorem 4: the rigidity proof has several unproved classification steps

The probit-rigidity argument is not line-by-line complete.

- Equation (2.4) is divided on a set where both the transformed argument and an affine
  denominator vary; zeros and component boundaries are not controlled.
- The assertion that one Möbius function is “the same for all `(a,b)`” does not follow merely
  because the left side is independent of those parameters.
- The exponential-versus-rational comparisons are asserted, not proved with their domains and
  exceptional cases.
- The claim that a power of a Möbius function forces only exponents `0` or `1` is not established.
- The quadratic case is dismissed by a moving-pole argument without proving that cancellation
  cannot occur.
- The affine and exponential “further strata” do not follow from the bounded-link argument by
  simply reading the same computation backwards.

There is also a notation collision: `a` denotes both the diffusion coefficient and the
single-index slope. Until these gaps are replaced by a complete functional-equation proof,
“probit is forced” is a conjectural classification, not a trusted theorem.

### Theorem 6: finite trigonometric witnesses do not yield an infinite-dimensional tangent space

At a trigonometric polynomial with `J` frequencies, the displayed Vandermonde argument proves
only a finite family of independent bracket values. Letting `J → ∞` while changing the base
curve does **not** prove that the Lie algebra is infinite-dimensional at any one point, nor that
such points form a dense set. A valid proof needs one smooth curve with infinitely many carefully
controlled frequencies, convergence in the chosen Fréchet topology, independence at that fixed
curve, and the infinite-dimensional support/tangency theorem. The manuscript supplies none of
these. This is the most serious proof-validity error among the results labelled “proved here.”

### Theorem 7: unsupported geometry of the discarded mode

The POD/Ky Fan identity is plausible under a trace-class orbit Gram operator. The further claim
that the next Pick eigenvector is “predominantly the `(d+1)`-th active mode” is false without
conditions on the spectral coefficients and gaps: arbitrary coefficient weights can make any
mode dominate. The precise Zolotarev constant also requires an operator-level theorem whose
hypotheses survive the diagonal congruence; it is not proved in the manuscript.

### Theorem 8: transport invariants require an invertible flow

Range and level-crossing data are preserved by a global increasing reparameterization. A generic
transport semigroup on an interval can hit a boundary or fail to be onto. The manuscript needs a
global flow of increasing bijections before claiming preservation of the full order structure.

### Theorem 9: the claimed gauge group is incomplete

Snapshots from one cyclic vector identify the generator only on that cyclic subspace. Its action
on the orthogonal complement is wholly invisible, so “nothing else is unidentified” is false for
the full generator. Eigenvector normalization/sign and repeated-eigenvalue basis choices must
also be separated from the clock and orbit-shift gauges. The finite Vandermonde reconstruction
can be valid after restricting the estimand to the cyclic subspace.

### Proposition 11: Rayleigh–Ritz does not make the whole trajectory second order

Quadratic eigenvalue error does not remove first-order eigenvector/subspace error from a
trajectory. Without a Galerkin orthogonality statement tailored to the observable and initial
condition, the trajectory generally has an `O(θ)` component. The asserted “second order iff
normal-with-gaps” boundary is therefore too strong.

### Theorem 15: zero error is an omitted equality case

The proof sets `f(t) = log ‖e_t‖²`. This is undefined when the error vanishes. The zero solution
also attains equality but has no one-atom spectral measure, contradicting the stated “iff.” The
finite Lean replacement avoids logarithms and states a valid single-mode sharpness result without
claiming an exhaustive equality classification.

### Proposition 16: a cutoff heuristic is not an exact recovery theorem

With only an ambient norm bound, the inequality
`λ_k ≤ log(R/ε)/(t_i-t*)` describes a chosen noise-amplification threshold. It does not prove that
all modes below it are stably recoverable and every mode above it is lost in a specified minimax
sense. Such a theorem needs a noise model, estimator, loss, and source regularity class.

### Theorem 17: the error budget drops terms

The displayed bound is not justified as written.

- Prevalence error does not contract, yet the first term contracts the entire observation error.
- Eigenvector and certified-subspace errors are absent from the generator term.
- The Hilbert-space inner product for subdensities is not consistently specified in the
  coefficient formula.
- Marginal silence prevents learning a mode's dynamics from the marginal, but a full conditional
  snapshot can still contain that mode; indistinguishability needs a joint data model, not only a
  projection argument.

The exact finite bridge and tower law are proved; this quantitative estimator is not.

### Proposition 18: the quotient estimate lacks the norms and lower bound it uses

A bound for `q/p` requires uniform control of `1/p`, plus norms in which multiplication and
division are continuous. “Bounded below” in prose and an unspecified `C(π)` do not determine the
claimed inequality.

### Proposition 19: the placement rule is only for a surrogate

The manuscript correctly labels surrogate adequacy as a derivation, but also says front-loading
follows from log-concavity in a broader form than is proved. The recursion needs differentiability,
boundary conditions, existence of a minimizer, and a separate monotonicity argument for the chosen
weight. It is not yet a theorem about Bayes-optimal placement.

### Proposition 20: continuous Pick and discrete Hankel spectra are not “exactly” identical

The continuous orbit Gram matrix has entries `γ_j γ_k /(λ_j+λ_k)`. A discretely sampled Hankel
matrix has entries formed from powers `exp(-λ_k δ)`. They are related representations of the same
modes, but they are different operators and do not have the same singular values in general.
Consequently the statement that compressibility and learnability have *one exact spectrum* is
false as written.

### Proposition 21: the observability rank condition is malformed

For a nonlinear finite-dimensional system, Hermann–Krener uses differentials of iterated Lie
derivatives of the output. The expression
`Dη ν · (ad_ℓ)^k` is not that construction and is not type-correct when the output is a measure.
A trusted result needs a finite-dimensional observation chart or a specified function space,
then the actual codistribution rank condition. The infinite-dimensional lift cannot be inferred
from the finite-dimensional slogan.

## Engineering and interpretation defects

- “Appears not to be in the literature” and “searched” are not reproducible without a search
  protocol, date, databases, and retained results. They must not support novelty or priority.
- Appendix A checks local algebra only. It does not validate the functional-equation,
  infinite-dimensional tangency, Zolotarev, inverse-problem, or observability arguments described
  as load-bearing.
- Several results alternate between densities, measures, response curves, and subdensities
  without fixing the ambient norm or proving that division by the marginal is legal.
- “Finite-dimensional realization” is used for invariant manifolds, parameterized orbits, and
  invariant linear subspaces. Those notions require separate definitions and minimality criteria.
- Claims imported “modulo a cited ingredient” are not proved results in this repository until the
  cited theorem is represented by a trusted Mathlib declaration with matching hypotheses or is
  proved locally. No local theorem should accept the desired ingredient as a hypothesis merely to
  obtain a clean kernel report.

## Trust boundary

The current trusted boundary is intentionally finite-state. It already captures the biological
content needed by the core: frozen-mark transport, prevalence conservation, the population-built
reverse bridge, exact tower reconstruction, non-expansion, stationary-marginal non-identification,
threshold gauge and dynamic separation, two-state ancestry decay, and finite spectral stability.

The continuum OU/probit invariance, probit rigidity, stochastic FDR classification, POD rate,
snapshot identification, parabolic backcasting, placement, and nonlinear observability claims
must remain labelled **unproved** until their missing analytic objects and arguments are added.
That is a smaller result than the manuscript advertises, but it is a trustworthy one.

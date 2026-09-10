# Exact conditional law and integrability of the simulator's accuracy ratio

**Scope correction:** these are conditional mathematical calculations. The
claim that they completed the user's requested simulation law is withdrawn;
see [AUDIT.md](AUDIT.md). Their connection to the intended experimental
expectation and normalization has not been established.

## 1. Experiment and meaning of expectation

The inspected generator is `gnomon/sims/ancestry_calibration/gen_real_pt.py`,
with genotype generation in `stream_geno.py`. The two local files match the
August 16 MSI snapshot byte for byte; hashes are in `source_contract.json`.

This derivation uses the mathematical sampling model: Gaussian causal effects
and independent Gaussian environmental draws, with the discrete choices sampled
according to their specified distributions. Conditional on upstream genotype
data and choices, the effect vector is β ~ N(0, I_k). We keep PCA and the external
P+T implementation as fixed deterministic maps of their inputs, including their
fixed internal seeds and numerical conventions.

A literal fixed-seed computer execution is deterministic. Averaging over a
specified finite seed set is a finite weighted sum of its defined outputs.
That machine distribution is different from the continuous Gaussian model in
this document; independence of ideal random draws is not a theorem about the
PRNG streams. In particular, the divergence result below concerns the continuous
model. This distinction must remain explicit in any executable equivalence claim.

Let U contain all effect-independent upstream choices: training location,
genotype matrices, causal sites, PCA inputs, cohort splits, and the internal
GWAS/selection split. Write p_θ(u) for its probability under demographic and
simulation inputs θ. This notation does **not** claim those probabilities have
already been computed. Although the code draws cohort splits after β, reordering
these independent ideal draws does not change this mathematical joint law.

For each held-out deme j, let C_j be its k-column causal design matrix,
centered columnwise within the held-out deme. The design may retain the exact
values of the fixed float32 preprocessing output, as the branch certificates
do; raw integer-column centering need not reproduce that rounding. The generator globally centers
and rescales genetic liability. Within-deme Pearson correlation removes that
common affine transformation, including the `1e-12` in its scale denominator.
Thus its correlation with `true_liab` equals its correlation with C_j β.
This cancellation is for the metric: the same epsilon must remain in the
training-label probabilities.

The score is learned from noisy binary `phenoA` labels and then reused. Final
phenotype labels do not enter the `true_liab` correlation. Environmental noise
still affects the metric through the learned score.

## 2. Marginalize training without assuming weights are independent of effects

Let I be the training-population fit rows, including both the inner GWAS rows
and the threshold-selection rows. Only their labels affect P+T. For fixed u and
β, define the exact normalized genetic liabilities L_i(β) from the generator,
the affine deme baselines b_i, and c(β) by

\[
\frac1n\sum_{i=1}^n
\Phi\!\left(\frac{c(\beta)+b_i+L_i(\beta)}{\sigma_e}\right)=K.
\]

Here σ_e = 1 and K = 0.15 in the recovered runs. For label vector
y ∈ {0,1}^I, set

\[
p_i(\beta)=\Phi((c(\beta)+b_i+L_i(\beta))/\sigma_e),\qquad
\ell_y(\beta)=\prod_{i\in I}p_i(\beta)^{y_i}
                              (1-p_i(\beta))^{1-y_i}.
\tag{1}
\]

The labels outside I integrate out to one. Let s_j(u,y) be the centered
deployed score on held-out deme j, obtained by executing the prescribed learner
on u,y. Conditional on u,y, this vector is fixed. Its weights need not be a
simple marginal-GWAS formula: clumping, threshold selection, tie handling,
orientation, and PLINK's score conventions are retained in this map.

The posterior effect density on this branch is

\[
f_{u,y}(\beta)=\phi_k(\beta)\ell_y(\beta)/Z_{u,y},\qquad
Z_{u,y}=\int_{\mathbb R^k}\phi_k(\beta)\ell_y(\beta)\,d\beta.
\tag{2}
\]

Using the unweighted Gaussian prior after fixing the learned score would
generally give a different answer. Conditioning on the finite input labels
makes this dependence explicit.

For this mathematical probit model, ℓ_y is continuous, strictly positive, and
at most one. The root c exists uniquely and varies continuously: the left side
is continuous and strictly increasing in c with limits zero and one. Even the
code's bracket [-20,20] contains this root for `phenoA`. Indeed, |b_i| ≤ 0.7
and the empirical mean of L_i² is at most one. At least 15/16 of the rows have
|L_i| ≤ 4. Chebyshev's inequality for a standard normal gives Φ(-4) ≤ 1/16,
so the mean probability at c = -20 is at most 31/256 < 0.15; at c = 20 it is
at least 225/256 > 0.15. Continuity of the root follows from these bounds and
strict monotonicity. Consequently 0 < Z_{u,y} ≤ 1, and f_{u,y} is locally
bounded below by a positive constant everywhere.

This argument does not turn floating-point underflow or external process
failures into ideal Gaussian probabilities. It describes the stated ideal
label model and successful deterministic learner branches.

## 3. Exact readout on a branch

Define

\[
B_j=C_j^\top C_j,\qquad a_j=C_j^\top s_j,\qquad v_j=s_j^\top s_j.
\]

On its domain v_j > 0 and βᵀB_jβ > 0, direct expansion of sample Pearson
correlation gives

\[
R_j^2(\beta)=\frac{(a_j^\top\beta)^2}
                         {v_j\,\beta^\top B_j\beta}.
\tag{3}
\]

No population approximation, Gaussian genotype assumption, or large-cohort
limit enters (3). The sample normalization factors cancel. For source S and
target T, with nonzero source covariance,

\[
Q_T(\beta)=\frac{R_T^2(\beta)}{R_S^2(\beta)}
=\frac{v_S}{v_T}
  \frac{(a_T^\top\beta)^2(\beta^\top B_S\beta)}
       {(a_S^\top\beta)^2(\beta^\top B_T\beta)}.
\tag{4}
\]

For a valid branch with v_S,v_T > 0, rank(B_S),rank(B_T) > 0, and a_S ≠ 0,
the excluded hyperplanes/nullspaces have Gaussian measure zero. Equation (4)
is finite almost surely, but its expectation need not be finite.

## 4. Complete branch finiteness criterion

Assume the valid-branch conditions above and density (2). Let r_S and r_T
denote the ranks of B_S and B_T. Then:

| Condition | Expected target/source ratio on this branch |
| --- | --- |
| a_T = 0 | Exactly zero |
| a_T ≠ 0 and r_S = 1 | Finite; bounded by a fixed reciprocal source accuracy |
| r_S ≥ 2 and a_T is not a scalar multiple of a_S | +∞ |
| r_S ≥ 2 and a_T = κ a_S ≠ 0 | Finite iff r_T ≥ 3 or ker(B_T) ⊆ ker(B_S) |

The rows exhaust the valid cases. Invalid branches are undefined, not zero.

**Proof, rank-one source.** Write B_S = λuuᵀ with λ > 0 and unit u.
Because a_S belongs to the range of B_S, a_S = γu with γ ≠ 0. Then (3)
gives the constant R_S² = γ²/(v_S λ) > 0 almost surely. Since R_T² ≤ 1,
the ratio is bounded by v_S λ/γ².

**Proof, nonparallel vectors.** In the source-zero hyperplane
H = {β : a_Sᵀβ = 0}, nonparallelism ensures there is a β with a_Tᵀβ ≠ 0.
Since r_S ≥ 2, H is not contained in ker(B_S). The union of these two proper
linear subspaces cannot cover H. Choose β₀ ∈ H with a_Tᵀβ₀ ≠ 0 and
β₀ᵀB_Sβ₀ > 0. Also β₀ᵀB_Tβ₀ > 0: C_Tβ₀ = 0 would force a_Tᵀβ₀ = 0.

In a sufficiently small ball about β₀ the continuous factor

\[
\frac{v_S(a_T^\top\beta)^2(\beta^\top B_S\beta)}
     {v_T(\beta^\top B_T\beta)}\ f_{u,y}(\beta)
\]

has a positive lower bound c. Choose orthonormal coordinates with transverse
coordinate z = a_Sᵀβ / ||a_S||. Integrating over a small cylinder in this
ball bounds the expectation below by a positive constant times
∫_{-ε}^{ε} z⁻² dz = +∞. Tonelli applies because the integrand is nonnegative.
Removing H itself, a null set, does not remove this divergence.

**Proof, parallel vectors.** Cancellation in (4) gives

\[
Q_T(\beta)=\frac{v_S\kappa^2}{v_T}
                  \frac{\beta^\top B_S\beta}{\beta^\top B_T\beta}.
\tag{5}
\]

If ker(B_T) ⊆ ker(B_S), finite-dimensional spectral decomposition gives
B_S ≤ c B_T for some finite c, so (5) is bounded.

If r_T ≥ 3, decompose β = z+w orthogonally into range(B_T) and ker(B_T).
Let λ_* > 0 be the smallest positive eigenvalue of B_T. Under the unweighted
standard Gaussian law,

\[
\frac{\beta^\top B_S\beta}{\beta^\top B_T\beta}
\leq\frac{\|B_S\|_{op}}{\lambda_*}
          \left(1+\frac{\|w\|^2}{\|z\|^2}\right),\qquad
E\frac{\|w\|^2}{\|z\|^2}=\frac{k-r_T}{r_T-2}.
\]

The last identity follows by independence and radial Gaussian integration:
E||z||⁻² = 1/(r_T-2). Since ℓ_y ≤ 1 and Z_{u,y} > 0, integrability also
holds under (2), with the displayed prior bound divided by Z_{u,y}.

Finally suppose r_T ≤ 2 and ker(B_T) is not contained in ker(B_S). Choose
β₀ in ker(B_T) with β₀ᵀB_Sβ₀ > 0. In a neighborhood of β₀, numerator and
posterior density are bounded below, whereas βᵀB_Tβ ≤ ||B_T||op ||z||².
The transverse integral contains ∫₀^ε ρ^{r_T-3} dρ, which diverges for
r_T ≤ 2. This proves necessity and completes the classification.

The classification is robust to the learning likelihood, not independent of
learning: it uses exactly the positive continuous likelihood of each finite
label branch. Conditioning on a source-accuracy cutoff would change that
likelihood/domain and invalidate the unmodified pole argument.

## 5. A fully evaluated shared-effect witness

Take two centered causal columns with all four pairs of signs represented
equally. In the source, a tag column equals causal column 1; in the target,
the same tag locus equals causal column 2. Deploy the same score weight of
one on that tag in both populations. This is a fixed genotype/score example,
not a claim that P+T selects it in the recovered experiment.

For β₁,β₂ independent N(0,1),

\[
R_S^2=\frac{\beta_1^2}{\beta_1^2+\beta_2^2},\qquad
R_T^2=\frac{\beta_2^2}{\beta_1^2+\beta_2^2},\qquad
Q_T=(\beta_2/\beta_1)^2.
\]

The Gaussian direction is uniform on the circle. Transforming its angle gives

\[
P(Q_T\leq x)=\frac2\pi\arctan\sqrt{x},\qquad
f_Q(x)=\frac1{\pi\sqrt{x}(1+x)},\quad x>0.
\]

This is F(1,1), consistent with the
[SciPy F-distribution definition](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.f.html).
Direct integration gives the exact truncated first moment

\[
E[Q_T\mathbf1_{Q_T\leq L}]
=\frac2\pi(\sqrt L-\arctan\sqrt L)\longrightarrow+\infty.
\tag{6}
\]

Each accuracy has expectation 1/2 by symmetry, so their ratio of expectations
is one, while the expectation of their ratio is infinite. This directly
demonstrates why replacing the requested expectation by that ratio is invalid.

## 6. Distance law and demographic mixture

Let T_d(u) be the demes at distance d from the training deme. On a successful
branch with all required correlations defined almost surely, put

\[
\overline Q_d(u,y,\beta)=\frac1{|T_d(u)|}
                         \sum_{T\in T_d(u)}Q_T(u,y,\beta).
\]

Let A_d(u,y) indicate that the distance exists, P+T succeeds, and the branch
has the required nondegenerate score/causal matrices and a_S ≠ 0. We do not
assign failed/undefined runs a numerical ratio. With the nonnegative integral
understood in the extended sense, define

\[
P_d=\sum_u p_\theta(u)\sum_y A_d(u,y)Z_{u,y},
\]

\[
N_d=\sum_u p_\theta(u)\sum_y A_d(u,y)
       \int\phi_k(\beta)\ell_y(\beta)
                      \overline Q_d(u,y,\beta)\,d\beta.
\tag{7}
\]

The expectation matching this conditional reporting rule is **N_d/P_d** when
P_d > 0, allowing +∞. For arbitrary upstream spaces replace the outer sum
by its probability integral. When P_d = 0 the expectation is undefined.
If a pipeline applies additional effect-dependent failure or retention rules,
their indicators must stay inside these integrals. The retained historical
file subset does not supply such a retention law.

For the finite discrete-genome model with fixed cohort size and deterministic
PCA/P+T maps, the observable upstream states u and labels y have finite support:
the number of base positions, alleles, genotype entries, subsets and splits is
finite. Continuous ancestry times can be integrated into p_θ(u). Consequently
the distance mean is finite iff every positive-weight valid branch has a
finite mean for each target at that distance. One positive-weight divergent
branch makes N_d infinite. Distance zero is identically one whenever defined.
This finite-mixture conclusion is not asserted for arbitrary infinite upstream
mixtures without a separate uniform integrability argument.

Equation (7) is an exact reduction, not a calculation of p_θ or an efficient
solver. No finite numerical grid/chain expectation is claimed from writing it.

## 7. The remaining demographic and executable bridge

For the ideal standard diploid coalescent, the ancestral event rates are
1/(2N_j(t)) per lineage pair in deme j, backward migration M_jk(t) per lineage,
and the prescribed recombination rate at eligible links. Piecewise demographic
events act at their specified times. Event densities multiply these rates by
the survival factors exp(-∫ total_rate dt); summing and integrating complete
ancestral histories produces the genealogy law. These conventions follow the
[msprime ancestry documentation](https://tskit.dev/msprime/docs/stable/ancestry.html),
[ploidy documentation](https://tskit.dev/msprime/docs/latest/legacy.html), and
[migration definitions](https://tskit.dev/msprime/docs/stable/demography.html).
They provide a route to p_θ, but the full derivation/evaluation is not supplied
by existing unascertained two-locus moments.

Two implementation details prevent casually replacing this with a simpler
biallelic covariance model:

* The generator calls `sim_mutations` without a mutation model. The documented
  default is discrete-site JC69, permitting repeated mutations. Its mutation
  law must retain the allele/table information used by genotype encoding.
  See the [msprime API](https://tskit.dev/msprime/docs/stable/api.html) and
  [matrix mutation model](https://tskit.dev/msprime/docs/stable/mutations.html).
* `stream_geno.py` sums the two haploid **allele indices** into its dense causal
  and PCA data, while BED writing clips that sum to [0,2]. At multiallelic
  sites those inputs can differ. Formula (3) allows separate causal and score
  data, but a biological predictor must reproduce this code or explicitly
  define and validate a changed experiment.

The recovered metadata omits the causal matrices, effect draws, and selected
weight vectors. It also does not fully pin historical numerical dependencies
and the PLINK2 binary. This prevents reconstructing those particular branches
from the summaries or asserting bit-for-bit historical equivalence.

[SUPPORT.md](SUPPORT.md) gives an ideal-model support argument by a
different route: construct genotype/label branches,
execute the unmodified P+T code with pinned binaries/packages, and certify the
nonparallel covariance geometry exactly. Their positive probabilities suffice
to evaluate (7) as +∞ at every positive distance, without calculating those
probabilities numerically, if that support argument and idealization apply.
This does not establish the requested experimental law or settle which
normalization belongs in it. Demographic integration and a justified connection
to the experimental target remain outstanding.

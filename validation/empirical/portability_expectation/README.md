# Expected accuracy ratio for the recovered simulator

The target is the expected **within-run target/source held-out squared-correlation
ratio**, averaged over demes at each distance, as in
[the recovered figure](../portability_ci/README.md). All random causal effects,
training labels, and genotypes belong inside that expectation.

[DERIVATION.md](DERIVATION.md) derives the exact conditional ratio, marginalizes
the finite training-label outcomes with their correct effect-dependent
probabilities, and proves a complete finiteness criterion for each fixed
genotype/training-label branch of the stated continuous Gaussian model.

The result for the specified continuous Gaussian model is **one at distance
zero and infinite at every positive distance**, for both the chain and grid.
[SUPPORT.md](SUPPORT.md) proves that constructed genotype/label panels have
positive probability under the demographic generator and connects them to
successful executions of the recovered P+T routine. Exact rational geometry
certificates cover all nine chain targets and all 35 grid targets.

Near-zero random source accuracy makes the mean ratio diverge. Neither an
infinite variance of effects nor a positive probability of an undefined metric
is necessary. This explains why a finite observed curve and finite bootstrap
intervals do not establish a finite theoretical expectation of the ratio.

This is an analytical result with checked numerical branch certificates, not
a Lean-checked end-to-end theorem. It uses the recovered default of 150 causal
variants and the pinned preprocessing/learner execution. A finite machine-seed
average is a different distribution; no infinite mean is asserted for a finite
set of finite machine outputs. Historical environment equivalence is not proved.

## Verification

From this directory, run the deterministic verification with the figure bundle's
NumPy dependency:

```sh
uv run --with-requirements ../portability_ci/requirements.txt python check_derivation.py
uv run --with-requirements ../portability_ci/requirements.txt python verify_branch_witnesses.py
```

The script uses exact rational arithmetic to compare direct sample correlations
with the matrix formula and to check finite and divergent geometry examples.
It separately checks the Gaussian witness's truncated mean by deterministic
quadrature. These checks validate consequences of the derivation; they do not
replace its proof or establish the simulator's genotype-support condition.
The second script independently checks the archived actual learner outputs,
causal preprocessing, exact covariance determinants, and a common effect
direction that cancels source covariance while preserving target covariance.
No simulation is fitted, and no recovered accuracy is used to derive the law.

`verification.json` and `branch_verification.json` record the checks.
`branch_witnesses.tar.gz` contains both complete genotype/design/label/score
panels, certificates, weights, p-values, PLINK logs, and the unmodified source
files as archived replay inputs. `source_contract.json`
records the inspected source hashes and scope.

To reconstruct the branch witnesses on MSI, use the versions in
`requirements-branch.txt` and the PLINK binaries pinned in the certificates.
The following uses the snapshot source; the archive's `source/` directory is
also a hash-identical input to `--source` after extraction:

```sh
python certify_pt_branch.py \
  --source /projects/standard/hsiehph/sauer354/.snapshot/snapshot_2026-08-16_00_00_00_UTC/gnomon/sims/ancestry_calibration \
  --demography serial1d --output /path/to/new/serial1d-witness
python certify_pt_branch.py \
  --source /projects/standard/hsiehph/sauer354/.snapshot/snapshot_2026-08-16_00_00_00_UTC/gnomon/sims/ancestry_calibration \
  --demography grid2d --output /path/to/new/grid2d-witness
```

## Limits and remaining theory

1. Formalize the support argument, ratio integrability theorem, and connection
   to the checked learner branches. These mathematical proofs are written out,
   but have not been checked by Lean.
2. For other, finite endpoints, calculate the demographic branch weights and the
   Gaussian integrals, with a proved error bound if numerical evaluation is
   used. The formula alone is not an evaluated input-to-curve predictor.
3. Establish any desired bit-for-bit historical executable claim. The
   archived Python source is recovered; historical dependency and PLINK binary
   versions are not completely pinned.

The existing bootstrap figure remains a description of the recovered runs.
A ratio of expected accuracies, a source-accuracy cutoff, and a capped
ratio are different estimands; this derivation does not substitute any of them.

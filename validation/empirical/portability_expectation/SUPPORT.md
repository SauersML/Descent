# Applying the divergence theorem to both demographic configurations

## Result and scope

For the continuous Gaussian-effect/probit-label model defined in
[DERIVATION.md](DERIVATION.md), with the recovered default 150 causal variants
and the checked P+T implementation, the expected reported distance ratio is

\[
E[\overline Q_d\mid\text{distance exists and the readout is defined}]
=\begin{cases}
1,&d=0,\\
+\infty,&d=1,\ldots,9\quad\text{(serial1d)},\\
+\infty,&d=1,\ldots,10\quad\text{(grid2d)}.
\end{cases}
\]

This conclusion combines an analytical positive-support argument with exact
rational certificates for successful executions of the unmodified recovered
P+T routine. It is not a Lean-checked end-to-end proof. It concerns a continuous
sampling model with the fixed numerical preprocessing and learner described
below; it is **not** a claim of an infinite average over finitely many machine
seeds, nor a numerical expectation for the historical seed list.

## 1. Construct a successful branch, without fitting an accuracy model

`certify_pt_branch.py` constructs one genotype/label panel for each cohort layout:

| Configuration | Individuals | Source test | Each target test | Variants | Causal variants |
| --- | ---: | ---: | ---: | ---: | ---: |
| serial1d | 7,250 | 2,500 | 125 | 600 | 150 |
| grid2d | 13,750 | 2,500 | 125 | 600 | 150 |

The training population is deme zero. Place 30 biallelic variants at distinct
integer positions in each of the 20 five-megabase chunks, with no other mutated
sites. All 600 columns satisfy the PCA and causal-pool frequency thresholds.
There are fewer candidates than either reservoir's capacity, so both reservoirs
retain every column, in order. Choose the first 150 as the ordered causal subset.

The construction uses a fixed RNG to generate a compact genotype witness and
a fixed rule to choose its binary labels. **These are witness construction
choices, not the probability law being attributed to the demographies.** The
next section proves that these resulting arrays are in the support of the
actual ideal demographic generator.

The script imports the archived `gen_real_pt.py` and `stream_geno.py` unchanged
after checking their hashes. It uses their cohort layout, BED writer and
`real_pt` function, with the same PCA formula, two GWAS threads, and 2 GB PLINK
memory. Source fit/test is 2,500/2,500, and the learner makes its own prescribed
2,000/500 internal GWAS/threshold-selection split.

Both executions succeeded: 600 usable GWAS rows, 600 clumped variants, five
selected score variants, selected threshold 0.01. The selection AUCs were
0.7279 for the chain and 0.7205 for the grid. These numbers establish a
successful learner branch; they are not used to estimate any expected curve.

The certificates pin the binaries and Python packages used. They preserve the
actual float32 causal-centering output as a fixed design matrix and the actual
returned score values. The mathematical effect vector is subsequently varied
continuously, and correlation is evaluated in real arithmetic. In particular,
the proof does not silently equate float32-centered causal columns with exact
integer-column centering, or numerical Pearson correlation with exact real
arithmetic near a singular denominator.

## 2. Each constructed panel has positive demographic probability

The two specified coalescent demographies ultimately bring lineages into a
common finite-size ancestor. With finitely many samples and finite chromosome
length, there is positive probability of a complete genealogy with finite
branch lengths, strictly positive terminal branches, and no recombination in a
chunk. For example, survival over the finite demographic epochs followed by a
finite sequence of coalescences in the common ancestor has a product of positive
survival and transition probabilities. We only need a set of such histories
of positive measure, not any one exact vector of coalescence times.

Conditional on any such genealogy, the following JC69 mutation event has
strictly positive probability:

1. At each of the 30 specified variant positions choose ancestral allele A.
2. Realize each dosage row by two haploid alleles: 0 as AA, 1 as AG, 2 as GG.
   On a terminal branch whose sample needs G, place exactly one A-to-G mutation;
   on terminal branches whose sample needs A, place none.
3. Place no mutations on internal branches or at any other base in the chunk.

All terminal branches have positive length, the mutation rate is positive,
the genome and total branch length are finite, and the A-to-G jump has positive
JC69 probability. Each required finite Poisson event therefore has positive
probability. Repeated independent terminal mutations to G are allowed by the
finite-sites mutation model. Since A is ancestral and G is the only derived
allele, `genotype_matrix()` uses indices 0 and 1 as required, and the BED clipping
does not change any dosage in this witness.

Integrating a strictly positive conditional mutation probability over the
positive-probability genealogy event preserves positivity. Taking the product
over the 20 chunks also preserves positivity. This proves positive probability
for the **particular constructed genotype matrix**, despite its being extremely
unrepresentative of a typical demographic draw. No approximation by independent
SNPs is imposed on the original demographic law.

Deme zero has positive probability as the training location. The prescribed
balanced cohort split and ordered causal subset each have positive probability
under the ideal discrete choices. PCA and its internal seed are then fixed.
Finally, every finite source-fit label pattern has strictly positive likelihood
at every finite β under the probit noise model, by (1) in DERIVATION.md. Thus the
successful learner branch has positive joint probability, and its posterior
effect density has the local positivity used in the divergence theorem.

This support argument uses the documented finite-sites JC69 model, including
recurrent mutations; see the
[msprime mutation documentation](https://tskit.dev/msprime/docs/stable/mutations.html).
It would have to be re-established for a changed model, such as one that
forbids recurrent mutations. It is not an assertion that a finite PRNG seed
family reaches every ideal genotype array.

## 3. Exact geometry certificates

For the source, a nonzero 2-by-2 determinant of two differences between held-out
causal-design rows proves that its first two causal columns have centered rank
two. Hence rank(B_S) ≥ 2.

For each target, the certificate computes

\[
h_{j,l}=n_j\sum_i C_{j,il}s_{j,i}
                     -\left(\sum_i C_{j,il}\right)\left(\sum_i s_{j,i}\right)
\]

for causal columns l = 0,1. This is n_j times the corresponding coordinate of
a_j. The determinant h_{S,0}h_{T,1} − h_{S,1}h_{T,0} is nonzero for **all nine
chain targets and all 35 grid targets**. Each score has positive variance.
The calculations convert binary floating-point values to their exact rational
values and use rational arithmetic; there is no numerical-rank tolerance or
near-zero threshold in these certificates.

Equivalently, the common effect direction with first coordinates
(−h_{S,1}/h_{S,0}, 1) and all other coordinates zero cancels source covariance
while leaving every target covariance nonzero. Rank two keeps source genetic
variance positive there. The same direction therefore witnesses the
source-denominator singularity for every positive distance in that panel.

Section 4 of DERIVATION.md now gives infinite conditional mean for every
target ratio on this branch. At each positive distance, averaging finitely many
nonnegative ratios preserves divergence. The branch has positive demographic
probability, so averaging over the remaining genotypes, labels and training
locations also preserves divergence. Conditioning on defined reporting divides
by a positive probability and cannot make this numerator finite.

## 4. What this answers

The ideal model does have an exact answer for the requested expectation: its
positive-distance entries are infinite. Thus a finite smooth curve cannot be
the mean of this unmodified ratio in that model. Even a very long finite batch
can entirely miss the rare branches responsible for this result. The theorem
does not quantify how many runs would encounter them or predict the typical
observed curve.

A finite-seed implementation has its own discrete law and rounding behavior.
The checked binary identities and source hashes are recorded, but the full
historical environment and a seed probability law were not recovered. Those
limitations prevent converting this analytical result into an assertion about
every bit-for-bit historical execution.

Other estimands remain legitimate research targets: expected target accuracy
is bounded between zero and one; a ratio of expected accuracies is finite when
its source expectation is positive; a ratio conditioned on R_S² ≥ ε is bounded
by 1/ε. They are different laws. None is silently substituted for the quantity
in the current ratio plot.

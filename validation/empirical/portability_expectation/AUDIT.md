# Correction to the claimed completion

The claim that an exact law for the requested simulation portability curve had
been achieved is withdrawn. The infinity annotation on the recovered-run figure
has also been removed. No input-to-curve expectation law has been established.

## What was actually done

The work derived the squared-correlation ratio as a function of continuous
Gaussian effects after conditioning on genotype data and training labels.
It analyzed integrability near a zero source covariance. Two artificial
genotype/label panels were passed through the recovered P+T learner, and exact
rational calculations verified the relevant geometry for their 44 targets.
A written support argument relates such panels to an ideal finite-sites
coalescent/mutation model.

Those checks do not evaluate the original demographic law, estimate the
probability of the constructed panels, or validate an expected portability
curve against the recovered simulation runs. The external learner was run;
the full demographic simulator was not run to produce those panels.

## The scope errors

1. The target expectation and conditioning were not established before choosing
   to average ratios with a random estimated source accuracy. Fixing the source
   normalization, averaging accuracies before normalizing, and averaging sample
   ratios are different mathematical targets.
2. The analysis replaced the seeded numerical experiment by independent ideal
   draws, continuous effects, and a real-arithmetic metric combined with fixed
   numerical preprocessing and learner outputs. This is an explicit hybrid
   model, but equivalence to the requested experimental law was not proved.
3. A rare-denominator argument was promoted to completion of the scientific
   task. It does not explain or predict the distance-dependent curve the user
   asked about. Checking constructed covariance minors cannot supply that
   missing prediction.
4. The figure annotation and public status went beyond the evidence. The
   intervals were relabeled on the strength of the idealized argument before
   establishing that argument's applicability to the intended expectation.

An infinite expectation is possible even when individual ratios are finite.
Consequently a finite plot alone is not a mathematical disproof of the
conditional singularity argument. Conversely, a possible singularity is not
evidence that the requested simulation law has been solved. The conditional
calculations are retained as research notes, with that boundary explicit.

The archived certificates retain their original output text for provenance.
Their interpretation fields are superseded by this audit; the current verifier
reports only the constructed-panel geometry it actually checks.

## Completion criterion

Recover the experimental randomization and normalization rules; state precisely
what is averaged and what is conditioned on; derive its expectation from the
specified demographic, trait, environmental, sampling, and learner inputs;
and validate the resulting predictions. Any idealization needs a justified
connection to that experiment. No alternative normalization should be adopted
merely to obtain an easier answer.

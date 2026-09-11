# Descent

A Lean 4 formalization of genetic theory.

The three PGS portability questions are developed in
[OpenQuestions.lean](Descent/Program/OpenQuestions.lean). The proofs classify
individual-loss information and noise, give sharp attainable ranges at fixed
second moments and genetic inputs, characterize finite evolutionary/reporting
closure, and establish metric-ordering and decision-cost converses. Their domains
include arbitrary square-integrable loss for the information theorems and explicit
finite model classes for the sharp ranges. Gaussian loss noise is derived from
the Gaussian measure. The combined axiom audit is
[CheckThreeQuestions.lean](validation/code/CheckThreeQuestions.lean).

For exact results and limits of demographic prediction of polygenic score accuracy,
see [Universal portability](UNIVERSAL_PORTABILITY.md).

## Building

```sh
lake exe cache get
lake build Descent ValidationShared
```

## Contributing

All contributions are welcome.

## Spec
- Simulations must never be used to fit models. They are only for validating existing derivations.
- Only these three axioms are allowed: propext, Classical.choice, and Quot.sound

## License

Apache-2.0. See [LICENSE](LICENSE).

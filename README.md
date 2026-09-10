# Descent

A Lean 4 formalization of genetic theory.

The three PGS portability questions are developed in
[OpenQuestions.lean](Descent/Program/OpenQuestions.lean): exact individual-loss
moment and fitted-predictor decompositions, limits on identifying tagging versus
effect mechanisms, and source-threshold transport with application-dependent
decision costs. The results include the corrected sharp interval CV bound and
an explicit counterexample to inferring squared-bias variance from signed variance.
These proofs do not attribute the paper's empirical findings to a particular cause.

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

# Descent

A Lean 4 formalization of genetic theory.

## Building

```sh
lake exe cache get
lake build Descent ValidationShared
```

## Contributing

All contributions are welcome.

## License

Apache-2.0. See [LICENSE](LICENSE).

## Layout

`Descent/` is the corpus, in eight groups. `validation/` is the harness that
audits it: Lean detectors under `validation/code/`, and simulation, differential
and metamorphic batteries under `validation/empirical/`.

| Group | What is in it |
|---|---|
| `Foundations/` | Probability, the convention ledger, and the algebraic transport identities everything else instantiates |
| `Conditionals/` | Functional descent and its geometry: when a functional of a conditional law is a function of the label it is reported against |
| `Blindness/` | The observational ceiling and its instances -- probes that cannot separate two objects, and the witness pairs that prove it |
| `Decision/` | Finite minimax duality, Le Cam floors, and the certificate calculus |
| `Spectral/` | Operator, pencil and spectral machinery: Markov spectra, whitening, projection and shift bounds |
| `PopGen/` | Population-genetic models and their named quantities: demography, drift, selection, linkage disequilibrium, architecture |
| `Portability/` | The deployment layer -- polygenic score portability, calibration, and correctability |
| `Program/` | What the corpus concludes, and what it leaves open |

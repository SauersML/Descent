# Descent

A Lean 4 formalization of genetic theory.

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

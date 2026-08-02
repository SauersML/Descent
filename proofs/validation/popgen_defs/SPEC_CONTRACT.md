# Registration contract for validation specs

Every remaining definition is registered, not hand-coded. The six oracle
backends already exist; the work is declaring which one applies and with what
parameters.

## Output

One file per Lean source file, named `specs_<LeanFile>.py`, containing a single
module-level list `SPECS`. No `main()`, no printing, no execution at import.

```python
"""Specs for Calibrator/<LeanFile>.lean"""
import numpy as np
from scipy import stats

SPECS = [
    dict(
        name="liabilityAUCFromExplainedR2",
        source="PortabilityDrift.lean:2578",
        # EXACT transcription of the Lean body. Do not simplify, do not
        # "correct" it. If the Lean says `2 * F`, write `2 * F`.
        lean=lambda r2, K: float(stats.norm.cdf(np.sqrt(r2 / (2 * (1 - r2))))),
        # Ground truth, derived INDEPENDENTLY of the Lean formula.
        oracle=lambda r2, K: exact_auc(np.sqrt(r2), K),
        backend="B",                       # see table below
        domain={"r2": (0.01, 0.6, "log"), "K": (0.001, 0.5, "log")},
        rng=(0.5, 1.0),                    # range the NAME requires, or None
        note="no prevalence argument",
    ),
]
```

## Backends

| id | machinery | use for |
| --- | --- | --- |
| A | closed-form algebra, no sampling | identities, ratios, algebraic rearrangements |
| B | Gaussian / statistical Monte Carlo | AUC, power, R², Brier, calibration, ESS, estimator variance |
| C | coalescent (msprime) | F_ST, diversity, SFS, LD from genealogies |
| D | forward Wright–Fisher | drift, mutation-drift, migration, assortative mating |
| E | SLiM | anything involving selection |
| F | GWAS/PGS pipeline | portability, discovery power, sample overlap |

Prefer the cheapest backend that can actually decide the question. A is free; E
costs minutes per point.

## Rules

1. **Transcribe the Lean body literally.** The whole method depends on testing
   what is written, not what was meant. Quote the file and line.
2. **The oracle must be independent.** Deriving it by rearranging the Lean
   formula tests nothing. Use a textbook result, a direct simulation, or exact
   numerical integration.
3. **State the regime.** If the definition is only claimed for `m < s`, or for
   many demes, put that in `domain` and say so in `note`.
4. **If you cannot construct an independent oracle, do not invent one.** Emit
   the spec with `oracle=None` and a `note` explaining what would be needed.
   An honest gap is worth more than a circular test.
5. **A failing spec is not a finding.** In this project's own history roughly
   one flag in six was a broken oracle, not a broken definition — symmetric
   designs that could not detect the error, double-applied attenuation, clipped
   near-boundary probabilities, insufficient burn-in. Every failure is
   adjudicated by hand before it is reported.
6. Skip definitions that are projections, record builders, `Prop`-valued, or
   pure restatements of their arguments. Those are already classified out.

## Checklist per spec

- [ ] Lean body transcribed character-for-character
- [ ] oracle derived independently of that body
- [ ] domain covers the regime the definition claims, including its boundary
- [ ] a parameter the quantity is known to depend on but the signature omits is
      recorded in `note` (this single pattern accounts for six of the twenty
      defects found so far)

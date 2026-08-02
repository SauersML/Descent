# Simulation checks of `Calibrator/ImitationRigidity.lean`

`check_imitation.py` transcribes each definition from the module literally and
compares it against a simulation of the quantity its *name* claims to be. The
theorems in the module are machine-checked and so cannot be false; what these
checks can contradict is a name.

Run:

```
python3 proofs/validation/imitation_rigidity/check_imitation.py
```

Ground truth: exact linear algebra (numpy) for the spectral claims, a
first-order Markov haplotype simulation along a chromosome for the LD claims,
ridge regression on simulated genotypes for the spectator claim, and a
forward Wright–Fisher simulation for the allele-loss claims. Monte Carlo error
enters as an absolute tolerance computed from the simulation itself (across
haplotypes, which are independent, not across sites, which are not), so a noisy
estimate is not reported as a falsification.

## Falsified, and repaired

| Definition | Error | Fix |
| --- | --- | --- |
| `ridgeBalance` | took no variants-per-individual ratio, although the ridge fixed point depends on it; the resolvent functional came out 34% too large at aspect 0.3 (1.452 predicted against 0.957 simulated) | added the `aspect` argument; agreement is now 2×10⁻⁴ |

This is the missing-argument failure class that `scripts/check-identifications.py`
screens for statically: no constant repairs it, because the signature could not
express the dependence.

## Confirmed

| Claim | Result |
| --- | --- |
| `stationaryLDEntry` = correlation at separation `d` | matches simulated Markov haplotypes at ρ = 0.3, 0.6, 0.85, within Monte Carlo error |
| `ldHardEdge` = symbol minimum | exact to 1.7×10⁻¹⁶ |
| `ldHardEdge` = smallest eigenvalue of the LD matrix | 6×10⁻⁴ at 64 variants, approaching from above |
| `ldWhiteningGain` = harmonic mean of the symbol | exact to 2×10⁻¹⁶ |
| `ldPrecisionTrace` = `tr K⁻¹` | exact to 10⁻¹⁶ at every size and ρ tested (k = 8, 64, 512) — the finite-size formula, including the boundary correction, not just the limit |
| secular threshold = largest absorbable bump | exact to 10⁻¹⁶ against bisection on `λ_max(K + s vvᵀ) ≤ C₀`; the bump is inside the class at 0.99× and outside at 1.01× |
| per-individual resolvent entries do not self-average | variance stays ≈0.086 as n goes 100 → 800 with half the samples dropped out |
| genome-wide averages do self-average | `Var((1/n) tr R)` falls 7.3× when n grows 8× |
| spectator principle | deterministic-equivalent risk matches simulated ridge to 5×10⁻⁴ for an evaluation geometry in general position (‖[A,B]‖ = 5.0), i.e. non-commutation costs nothing |
| `alleleLossProbability` = Wright–Fisher loss probability | within 0.4% at scaled frequencies 0.004–0.01 and coalescent times 0.5–2, under the quarter-speed squared-Bessel correspondence |
| `informationCrossoverTime` = `x/2` | argmax of the absorption channel weight, to 10⁻⁶ |

The Wright–Fisher check is worth stating precisely, because it is the one place
the module touches a diffusion approximation rather than an identity: in
coalescent units (τ = generations / 2N) the frequency diffusion is the
squared-Bessel process of dimension zero run at a quarter speed, so the absorbed
mass `exp(-x/2t)` is evaluated at `t = τ/4`. That factor was checked, not
assumed.

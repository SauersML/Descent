# Cumulative wiring ledger

One row per mathematical result produced upstream, tracking whether it is (a) still
standing upstream, (b) actually present in this corpus and in what form, (c) attached to a
genetic statement, and (d) supported by anything beyond its own docstring.

**Read the STATUS and EVIDENCE columns together.** This corpus's house style carries
unverifiable analytic inputs as *named structure fields* rather than `sorry`s. That is
honest, but it means a theorem name in a file does not imply a proof of the mathematics —
it usually means a proof of a *consequence*, conditional on a field. The EVIDENCE column
distinguishes:

- **PROVED** — machine-checked from Mathlib, no analytic field on the path.
- **HYPOTHESIS** — the result itself is a structure field / named hypothesis; downstream
  corollaries may be proved but rest on it.
- **SIMULATED** — numbers exist in `proofs/validation/`, cited here.
- **ASSERTED** — prose in a docstring only; no definition, no theorem, no field.

There are **zero `sorry`s and zero `axiom`s** in the corpus (checked by grep; the only
matches for `sorry` are in `Identification.lean` prose about the policy itself).
Of 402 `Empirical status:` markers, 323 are `UNTESTED`, ~28 `DERIVED`, ~20 `VALIDATED`,
~8 `FALSIFIED`, 6 `CONDITIONALLY VALID`, 3 `VACUOUS`.

---

## The table

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 1 | **Maximal spectrum (Theorem S).** Closure of admissible-chaos limits at a prescribed polymorphic frequency family is the whole moment body. | standing | `EpistaticChaos.GenotypeChaosLimits.maximal_spectrum` (field, :1661); consequence `admissibility_alone_certifies_only_the_moment_body` (:1743); `CondensationUnification.moment_body_reached_at_every_drift` (:330) | Admissibility — high interaction order, low per-variant influence — certifies nothing beyond centering and a variance bound. A Gaussian null for any burden/kernel/window scan whose tested sets share variants is unjustified, at every allele-frequency spectrum. | HYPOTHESIS (field) + PROVED corollaries | The density claim is an analytic input, unproved and unsimulated. No script constructs a near-target design. |
| 2 | **Disjoint segment (Theorem D).** Disjoint designs realize exactly the Gaussian segment `{N(0,s²) : 0≤s²≤1}`. | standing | `GenotypeChaosLimits.disjoint_segment` (field, :1644); `gaussian_null_licensed_of_disjoint` (:1693), `geneBurden_gaussian_null` (:1707), `disjoint_limit_fourthCumulant_zero` (:1723); `CondensationUnification.disjoint_design_gaussian_null_below_condensation` (:278) | Gaussian null **licensed** for gene-based burden/kernel over non-overlapping genes, at every polymorphic frequency, with variance the only free parameter. Disjointness is *discharged* for `geneBurdenDesign` and *refuted* for `slidingWindowDesign` — both proved. | HYPOTHESIS (field) + PROVED corollaries; the design-side gating lemmas are PROVED | The limit theorem itself is an analytic input. No simulation. |
| 3 | **Non-soficity witness.** Two-pool product has limiting fourth cumulant `6` under every coordinate law. | standing | `GenotypeChaosLimits.twoPool_witness` (field, :1670); `twoPool_interaction_fourthCumulant` (:1858), `twoPool_fourthCumulant_ne_disjoint` (:1869), `twoPool_witness_not_a_disjoint_limit` (:1878), `sign_symmetry_does_not_license_disjoint_reduction` (:1909) | A two-pool (gene×gene, pathway×pathway) interaction statistic is non-Gaussian in the limit at **every** allele frequency; sign symmetry does not rescue it. Frequency-free, so it applies to rare-variant panels. | Arithmetic `9−3=6` PROVED; the identification of the limit as a product of two independent Gaussians is HYPOTHESIS | The CLT/independence step is a field. No simulation of κ₄→6, which would be cheap. |
| 4 | **Star versus cycle.** Profile invariants are star densities; the limit lives in cycle densities. Palindromic circulant pair: equal 2nd cycle densities (80 = 80), different 4th (1840 vs 1600). | standing | `EpistaticChaos` §StarVersusCycle: `palindromicCycleDensityA_two`/`B_two` = 80 (:2323,:2336), `palindromic_second_cycle_densities_equal` (:2348), `..._A_four` = 1840 (:2353), `..._B_four` = 1600 (:2368), `palindromic_fourth_cycle_densities_differ` (:2386), `recurrence_matching_leaves_fourth_cycle_density_free` (:2404), `palindromic_circulant_spectra_differ` (:2010); `CycleDeterminacy` (:2172), `cycle_preserving_resampling_is_a_calibration` (:2210), `no_moment_matching_calibration_off_temperedness` (:2227) | A permutation/resampling calibration that preserves the variant-recurrence profile has preserved **nothing the null depends on**. The prescription is to preserve cycle densities; the 4th is the first that bites in the quadratic sector. | **PROVED** in closed form. The numbers 80/80 and 1840/1600 are theorems, not simulations. `recurrence_matching_...` deliberately never uses its recurrence hypothesis — that *is* the content. | `cycleDensity` of a real design is connected to no estimator and no pipeline. `CycleDeterminacy` carries determinacy as a field. |
| 5 | **Vertex-Weight Law.** The only invariants a design can transmit are the two-jet, arithmetic type, symmetry, and cumulants of the squared law. | standing, **but superseded in form** | Two independent wirings: `PolygenicSpectroscopy.VertexWeightCompleteness` (structure, :1078) + `experiment_factors_through_invariants` (:1094), `hwe_observables_exhausted_by_invariants` (:1133), `CodingInvariants` (:1059); and `CondensationUnification.ObservableTower.vertex_weight` (field, :731) + `experiment_factors_through_channels` (:749), `complete_content_of_truncation` (:780) | Complete observable content of a genotype coding, at truncation depth one, is a four-element list — drift, jet variance, arithmetic type, symmetry — plus `E[x⁴]=1/(2q(1−q))` as the variance of floor two. Two panels agreeing floor-by-floor are indistinguishable by every admissible design at every interaction order. | HYPOTHESIS (field, twice) + PROVED corollaries | Unproved analytic input. **The naive 4-list is wrong on its own**: `CondensationUnification`:415–449 records that the correct statement is a recursion, `OA(ν) = {two-jet, arith type, symmetry} ∪ OA(law of x²)`. Anyone quoting the 4-list must also quote row 20. Two formalizations that are never linked. **Plus:** `PolygenicSpectroscopy` §4b compares this (an *observability* list) against Tower Rigidity's four data (a *separation* set) as "a strictly smaller sufficient set". Session 10's completeness/observability split makes that comparison invalid — the two lists are in different currencies. See reversal audit R2. |
| 6 | **Tower floor two.** `E[x⁶] = (E[x⁴])² + 10 E[x⁴] − 20` per locus; for a panel `M₆ =` that `+` dispersion of `1/(2q(1−q))`. | standing | `CondensationUnification.sixthMoment_eq_floorOne_plus_dispersion` (:924), `fourthMomentDispersion` (:907), `MafSpectrum` (:836), `centeredSquareThirdMoment_differs_of_sixth` (:980), `floorOne_match_does_not_transport_calibration` (:1005); `EpistaticChaos.hweCenteredSixthMoment_eq` (:939), `standardizedGenotype_sixth_moment` (:959) | A panel matched on M₄, mean `q` and mean `2q(1−q)` **still separates at M₆**. So MAF-spectrum matching is not sufficient for calibration transport between panels. | **PROVED + SIMULATED.** `validation/differential/heavy/h5_results.json`: identity verified, `max_abs_err = 9.09e-13`. Lead arm, 40 atoms, 1.6e7 draws/atom: M₆ gap predicted 43.876, measured 45.283 ± 4.872 → **9.30 SEM separation**, predicted−measured = −0.29 SEM. M₄ control gap −0.011 ± 0.022 = 0.49 SEM (correctly does not separate). Max arm: predicted 181.45, dispersions 781.3 vs 599.8. | The strongest row in the table. Only gap: the M₆ contrast is exposed in no pipeline, so the separation is not usable as a diagnostic. |
| 7 | **Tower Rigidity + kurtosis phase boundary.** Symmetry + `E[x⁴]=3` + two matched odd parts forces Gaussian; boundary at `E[x⁴] > 2`. | **standing as a separation result; its universality narration is REVERSED by Session 10 — see the reversal audit** | `CondensationUnification.TowerRigidity` (structure, :1541, `rigidity` field) + `redundant_invariant_of_matched_four` (:1574). Phase side PROVED: `standardizedGenotype_fourth_moment_ge_two` (:1388), `..._eq_two_iff` (:1403), `hwe_phase_inequality_off_balanced` (:1439), `phase_strict_iff_not_symmetric` (:1454), `hwe_rigidity_hypotheses_unsatisfiable` (:1482) | **NONE, in the forward direction** — and the corpus says so itself. For a genotype the hypotheses are jointly unsatisfiable: symmetry forces `q=1/2`, and `q=1/2` forces `E[x⁴]=2` against the Gaussian's 3. The usable direction is the converse test, via `standardizedSquare_never_symmetric` (:522): the floor-two odd part is nonzero at **every** polymorphic frequency, `q=1/2` included — so non-Gaussianity is decidable one floor up where floor-one symmetry goes dark. | Rigidity = HYPOTHESIS; phase boundary and the unsatisfiability = **PROVED** | The rigidity input is unproved and, applied to genotypes, vacuous by the corpus's own theorem. The converse (non-Gaussianity) test that *is* live is instantiated by nothing downstream. **Plus:** the prose framing this as "universality holds exactly when the coordinate law is Gaussian" (`CondensationUnification`:1292) is now **known false**. The Lean field is a *separation* statement and survives; the narration conflates separation with universality. See reversal audit R1. |
| 8 | **Scale sequence σ_k, doubly exponential.** `σ₁²=2`, `σ₂²=14`. | standing (quadrature evidence) | `CondensationUnification.ScaleSequence` (:1242). `scale_one_sq`/`scale_two_sq` are **fields**, but anchored by proved theorems `gaussianFloorOneScaleSq` (:1090), `gaussianFloorTwoFourthMoment` (:1098), `gaussianFloorTwoScaleSq` (:1107). `doubly_exponential` is a **numerical-input field**. Consequences PROVED: `sampleSize_doubly_exponential` (:1280), `no_escape_below_radius` (:1269) | The tower is observationally truncated at about floor three for any study that will ever be run: ≈4·10² samples at floor 3, 9·10⁴ at floor 4, 5·10⁹ at floor 5. | Anchors **PROVED**; growth law is quadrature, recorded in-docstring: Gauss–Hermite, 200 nodes, exact through floor 7 — `1.414, 3.742, 19.07, 294.1, 7.276e4, 4.699e9, 2.005e19`, logarithms doubling to 4 s.f. | **The quadrature numbers exist only in a docstring.** No script in `proofs/validation/` reproduces them. That is a reproducibility hole on the one numerical input the tower's truncation depends on. |
| 9 | **`E[x⁴]=1/(2q(1−q))`; blind frequency `(3−√3)/6`.** | standing | **PROVED throughout.** `PolygenicSpectroscopy.standardizedFourthMoment_eq` (:1216), `..._ge_two` (:1232), `..._eq_two_iff_half` (:1247), `..._ne_gaussian_at_half` (:1284); `CondensationUnification.hweStandardizedFourthMoment_eq_inv_hweGenotypeVariance` (:473), `gaussianKurtosisMaf := (3−√3)/6` (:580), `gaussianKurtosisMaf_genotypeVariance = 1/3` (:600), `standardizedGenotype_kurtosis_gaussian_at_blind_maf` (:617), `hweFloorOneScaleSq_eq_gaussian_at_blind_maf` (:1143), `gaussianKurtosisMaf_ne_half` (:1497) | At MAF ≈ **0.2113** a standardized genotype is kurtosis-indistinguishable from a Gaussian. Any interaction statistic relying on fourth-cumulant separation loses power there. | **PROVED**; the fourth-moment identity is checked in `validation/condensation/check_condensation.py` and the popgen batteries | The docstring itself (`CondensationUnification`:575–578) says the **consequence** is untested and calls it "the most directly falsifiable number this development produces". A power-loss simulation at MAF 0.2113 is cheap and unrun. |
| 10 | **RETRACTED: sliding-design coupling correction `2b²/(1−b²)`.** | **RETRACTED upstream** | Retraction **properly landed**. `CondensationUnification` §5j (:1587–1640) records it; `EpistaticChaos`:1113–1121, :1200 carry the matching note. `couplingVarianceInflation`, `boundedHub_does_not_bound_coupling`, and the rationals `13122/3439`, `11529602/485199` are **gone** — grep finds them only inside the retraction text. `validation/coupling/sliding_window_coupling.py` has the arm removed under a scoped retraction header with a do-not-resurrect note. | **NONE now.** `b` is a property of the coordinate law with no established design-level consequence. The file explicitly asserts neither miscalibration nor safety for sliding-window scans. What stands: `hweSignBias_eq` `E[x\|x\|]=(1−2q)²` for `q≤1/2` (:1150, PROVED), `hweSignBias_zero_iff_balanced` (:1201, PROVED), `signBias` as the correct *name* for what a symmetric law destroys. | Standing parts **PROVED** | **Open:** whether any admissible design exposes `b` at all. No replacement mechanism supplied. A **second** retraction rode with it — the jet-to-strip upgrade is false (the window channel probes the truncated second moment at tilt θ=1 whatever the tuning slope), which is what `JetBarrier` had already proved. |
| 11 | **Dyadic Mellin ladder.** Floor `k` carries the log-square hierarchy at scale `2^{k−1}`; explains the log-log-n reachable-floor law as dyadic scales against a polynomial sample budget. | new, probably conjectural | **NOT WIRED.** Two prose sentences reference a `log log n` reachable-floor cutoff (`PolygenicSpectroscopy`:1018, `CondensationUnification`:1369) and neither names a dyadic hierarchy or the scale `2^{k−1}`. No definition, no theorem, no field, no validation script. | ASSERTED (and only obliquely) | **Everything.** This is the result that would convert row 8's `doubly_exponential` numerical-input field into a *derived* consequence, making the reachable floor count computable from study size instead of read off a quadrature table. Highest-leverage missing row. |
| 12 | **Degradation as a cocycle.** Correctable part is a coboundary; irreducible part is the angle in the target metric. | standing | **PROVED.** `ProjectionShiftBounds.irreducibleDegradation` (:875), `irreducibleDegradation_le_rescaled` (:881), `rescaled_at_optimum_eq_irreducibleDegradation` (:900), splitting theorem (:933: degradation − angle = `(β'Bβ)(a−a*)²`), (:951), `recalibration removes the coboundary and only the coboundary` (:964) | Recalibration of a transported score removes mis-scaling **and only** mis-scaling. A rotated predictor's loss is the target-metric angle between the transported direction and the target optimum, scaled by target signal energy, and no scalar touches it. This is the formal content behind `MetricSpecificPortability.recalibration_easier_than_rediscovery`. | **PROVED** | Every definition carries `Empirical status: UNTESTED`. No simulation and no connection to a real transported-score workflow. |
| 13 | **Shared-correction spread law.** Energy-weighted variance of per-target optima. | standing, **with an author's own correction to the conjectured form** | **Two independent wirings, unlinked.** (a) `MetricSpecificPortability` §spread law: `targetCorrectionCurvature` (:1780), `targetCorrectionOptimum` (:1788), `sharedCorrectionConsensus` (:1796), `sharedCorrectionSpread` (:1803), `sharedCorrectionCost_eq_consensus_add_spread` (:1844), `sharedCorrectionSpread_le_cost` (:1876), `..._at_consensus` (:1887), `..._eq_zero_iff_agree` (:1936). (b) `PCCorrectability/ImitationCapacity` §SharedCorrection: `weightedMean` (:1712), `energyWeightedVariance` (:1718), `weighted_dispersion_eq` (:1735), `energyWeightedVariance_le` (:1746), `sharedCorrection_capacity_deficit` (:1764) | Multi-population deployment incompatibility becomes a **number computable from objects already in the corpus** — fit `a_i*` per target, take the weighted variance — instead of a program to be solved. Sharing costs exactly `V / load` of imitation capacity. | Identities **PROVED** (exact, not asymptotic) | **The measured numbers are missing.** The claimed measurements (sharing costs 1e-6–5e-3 of signal energy; rotation 8×–6000× more) appear **nowhere** in the corpus or in `proofs/validation/`; every definition is `UNTESTED`. `ImitationCapacity`:1697–1707 explains the ordering structurally and calls it "the reported ordering" — but nothing in this repo reports it. Also: the author records that the first conjecture (load-weighted variance of *exit levels*, second order) was **wrong in form**; the correct law is a variance of *corrections*, first order, exact. Two formalizations of one law that never reference each other = double-counting risk. |
| 14 | **Capacity invariant.** capacity × load = headroom. | standing | **PROVED.** `ImitationCapacity.imitationCapacity_mul_load_eq_headroom` (:1776); `EquiExit.imitationCapacity_eq` (:675); `sharedCorrection_capacity_deficit` (:1764) | Sharing perturbs the **numerator** — subtracts `V` from headroom, capacity falls by `V/load`, additively and boundedly. Rotation changes **which constraint binds**, hence the denominator — capacity moves by the ratio of loads, multiplicatively and unboundedly. Additive-and-tiny vs multiplicative-and-unbounded is a structural explanation, not a coincidence of scale. | **PROVED** | The empirical ordering it explains is unmeasured here (see row 13). |
| 15 | **Imitation LP.** Capacity is an LP value; rigidity is a normal-cone condition, **not** a symmetry condition. | standing | **PROVED throughout `ImitationCapacity`.** `BackgroundClass` (:225), `spikeLoad` (:256), `headroom` (:262), `imitationCapacity` (:320), `isNull_spiked_of_le_imitationCapacity` (:358), `imitationCapacity_eq_zero_of_active` (:435), `imitationCapacity_antitone_constraints` (:465), `traceWindow_rigid` (:803) and `traceWindow_every_level_detectable` (:818) refuting the symmetry conjecture by construction with a generic positive-definite `A` and no symmetry | Leave-one-chromosome-out is a **restriction of the background class**, not a variance fix, and antitonicity says which way and by how much: more constraints → smaller capacity → lower threshold. Rigidity without symmetry is a design instruction for study construction. The certificate is a constraint index the machine returns, not merely proves to exist. | **PROVED** | `BackgroundClass` is never instantiated from data: the constraint ceilings `κ_a` for a real GRM or LD panel are inputs nothing in the repo supplies. `validation/imitation_rigidity/` checks `ImitationRigidity.lean`, not `ImitationCapacity.lean` — the LP has **no** validation script. |
| 16 | **Threshold = capacity on the equi-exit class**; the existing spiked-covariance threshold is the estimation half with the imitation half silently zero. | standing | **PROVED.** `EquiExit` (:643, equi-exit as an explicit field, never an implicit convention), `imitationCapacity_eq` (:675), `certificateTest_null_control` (:727), `certificateTest_power` (:742) — the optimal test is **synthesized**, not shown to exist. Diagnosis of the existing threshold: `imitable_despite_positive_pcCorrectabilityMargin` (:1238, hypothesis deliberately unused), `not_isNull_of_demographicSpike_gt_budget` (:1269), `rigid_certificate_exceeds_ceiling_iff_pcCorrectabilityMargin_pos` (:1291), `bbpProxyThreshold_tendsto_zero` (:1315) | **A positive `pcCorrectabilityMargin` does not imply detectability.** Whenever the spike fits inside the trace-window budget the spiked covariance is a legal background and no test at any sample size separates it, however far the spike clears the spectral edge. The omission of headroom is **not conservative**. The existing margin is the right criterion only when the window is active at baseline (headroom = 0). | **PROVED**; estimation half **SIMULATED** (`validation/pc_correctability/`) | **Highest-priority live gap.** `map/correctability.rs` (untracked, 445 lines) computes `margin = bbp_spike − bbp_threshold` with **no headroom term** — it ships exactly the non-conservative omission this theorem names. Nothing in the repo measures headroom. |
| 17 | **The `m_eff` prohibition.** No weakly continuous functional of the spectral law determines a detection threshold. | standing | **PROVED.** `ImitationCapacity` §MeffProhibition: `MomentContinuousFunctional` (:1554), `blockSpectrum` (:1381), `inverseTraceCertificate` (:1399), `meff_moment_gap_le` (:1508), `meff_certificate_gap` (:1526), `certificate_not_momentContinuous` (:1580), `meffWitness_spectrum_pos` (:1614), `meff_prohibition_with_certificate` (:1647), `inverseTraceCertificate_tendsto_ldWhiteningGain` (:1430) | Cheverud–Nyholt and Li–Ji effective-marker counts **cannot** determine a detection threshold for multiple-testing correction. `tr K⁻¹` / `ldWhiteningGain` can, and for exactly the reason those cannot: it is edge-sensitive and not weakly continuous. Those two facts are one fact. | **PROVED + SIMULATED.** `validation/meff_prohibition/measured_output.txt`: at n=4/8/16, measured 1.8415/1.9679/1.9942 against certificate prediction 1.8/1.8889/1.9412 and m_eff prediction 0.9951/0.9989/0.9998. Certificate wins at every n (\|err\| 0.042/0.079/0.053 vs 0.846/0.969/0.994). Max moment gap 0.19968/0.11109/0.05882 against theoretical bound 0.2/0.11111/0.05882 — **the bound is tight**. | The prohibition is exactly as strong as the claim that the `m_eff` family lands inside `MomentContinuousFunctional`, and that membership is **asserted in prose, never instantiated** for Cheverud–Nyholt or Li–Ji. One instantiation closes it. |
| 18 | **Lower-bound calculus incompleteness.** Every fixed grade under-certifies a nonsmooth functional by a polynomial factor; the deficit is a modulus ratio. | standing | `PolygenicArchitecture` §NonsmoothSummaries (:455–570): `meanAbsoluteEffect` (:468), `meanAbsoluteEffect_sq_le_meanSquaredEffect` (:485), `nonsmoothSummaryRisk` (:511), `gradeCertifiedRisk` (:521), `certificateDeficit` (:531), `certificateDeficit_eq` (:536), `gradeCertifiedRisk_understates` (:543), `nonsmoothSummaryRisk_exceeds_polynomial` (:558) | Mean-absolute-effect and polygenicity summaries are logarithmic-rate estimable, so sample-size calculations for them derived from two-point, Assouad or Fano arguments are **polynomially optimistic**; for the two-point case the requirement is exponential in reciprocal accuracy where the certificate reports a power law. | Deficit algebra **PROVED** in a stated regime (crossing point supplied as a hypothesis, not dressed as an asymptotic) | The two *rates* are **definitions** carrying `UNTESTED` — the minimax content is stipulated by naming, not derived. What is proved is "a positive power beats a logarithm", which is true but weaker than the upstream claim. The modulus-ratio identification is prose only. And the section never connects to `effectivePolygenicity` (:170) in the same file, so "polygenicity summaries are logarithmic-rate estimable" is not wired to the corpus's own polygenicity definition. |

### Rows found by reading the corpus, not on the seed list

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 19 | **Hidden-cone: witness uniqueness + Borel ceiling.** Douglas form; equivalence is a countable increasing union, hence Borel; ambiguity carried by σ-compact escape, not a wild groupoid. | standing, **with two unconditional retractions and one erratum already landed in-file** | `HiddenConeAmbiguity`: `witness_unique` (:117), `witness_unique_of_factorization` (:125), `BoundedLogDistortion` (+ equivalence, :139–169), `boundedLogDistortion_eq_iUnion` (:197), `boundedLogDistortion_isUnionOfCertificates` (:218), `codedDecayProfile_equiv_iff` (:267), `inequivalent_of_unbounded_coding` (:290), `rigidity_of_boundedBelowAbove` (:315), `catalogue_induces_reduction` (:361) | The **decay profile of the loadings** — exactly what scree plots, eigenvalue-gap rules, effective-rank estimators and "how many PCs?" heuristics recover — is *logically absent from the observables*, at infinite sample size with zero noise. Polynomial, exponential and tower decay are observationally identical. Identifiable **iff** the mixing is bounded below; the instant that fails, ambiguity jumps from trivial to maximal with nothing in between. Choosing a number of PCs is a **convention**, not an inference. | **PROVED** | Retracted in-file and correctly: the claim that the relation lies "strictly above every Polish-orbit orbit equivalence relation" is **false** (replaced by *incomparability*); the "third regime" framing is **empty**. Erratum: the diagonal-sector classification has **no permutation** clause. Attribution note says Ando–Matsuzawa (arXiv:1405.0860) methods plausibly settle global bireducibility — unclaimed. |
| 20 | **Exposure correction.** Exposing a square cumulant of order ≥3 forces the second hub energy to diverge, so no hub bound survives. | standing | `CondensationUnification.ObservableTower.higher_cumulants_need_divergent_hub` (field, :738); corollary `boundedHub_exposes_no_higher_cumulant` (:764, PROVED) | If every variant is tested a bounded number of times, no cumulant of `x²` beyond the second is exposed, whatever the design does. This is what makes row 5's naive four-element list wrong and the recursion right. | HYPOTHESIS + PROVED corollary | Analytic input. **Naming hazard:** this "exposure correction" is a *different* object from the retracted "exposure claim" of row 10 and is easily confused with it in a grep. |
| 21 | **AR(1) whitening gain as the certificate value.** `traceWindowSpikeLoad → (1+ρ²)/(1−ρ²)`; capacity = headroom × (1−ρ²)/(1+ρ²). | standing | **PROVED.** `ImitationCapacity.traceWindowSpikeLoad` (:1000), `traceWindowSpikeLoad_tendsto_ldWhiteningGain` (:1007), `whitenedCapacity_closedForm` (:1023), `imitationCapacity_eq_whitenedCapacity` (:1034), `whitenedCapacity_strictAnti` (:1049), `inverseTraceCertificate_tendsto_ldWhiteningGain` (:1430) | LD decay sets the detection threshold in closed form: stronger LD (larger ρ) strictly lowers imitation capacity, so a more correlated panel is easier, not harder, to defend against stratification imitating a polygenic spike. | **PROVED + SIMULATED.** `validation/imitation_rigidity/README.md`: `ldWhiteningGain` = harmonic mean of the symbol exact to 2e-16; `ldPrecisionTrace = tr K⁻¹` exact to 1e-16 at k = 8, 64, 512 including the finite-size boundary correction; `ldHardEdge` = symbol minimum exact to 1.7e-16, and = smallest eigenvalue to 6e-4 at 64 variants approaching from above | None material. |
| 22 | **`ridgeBalance` — FALSIFIED and repaired.** | falsified upstream, repaired | `ImitationRigidity` (see `validation/imitation_rigidity/README.md`) | — | **SIMULATED falsification.** Took no variants-per-individual ratio although the ridge fixed point depends on it; the resolvent functional came out **34% too large at aspect 0.3** (1.452 predicted vs 0.957 simulated). Repaired by adding an `aspect` argument; agreement now 2e-4. | Kept as the precedent for the missing-argument failure class that `scripts/check-identifications.py` screens for statically — no constant repairs it, because the signature could not express the dependence. |
| 23 | **Spike constant and effective-marker count for PC correctability.** `demographicSpike = 4 F · m(n−m)/n`. **`F` is Nei's `G_ST`, NOT Hudson's `F_ST`** — see the correction block below. | standing; the arithmetic is sound, the estimator label was wrong, and the direction of the resulting user error is **the opposite of what was first reported** | `PCCorrectability/Threshold.lean:31`; the estimator is `Conventions.hudsonFst` (misnamed) | The sharp criterion `1 < M F² n` is the Patterson–Price–Reich boundary. | **VALIDATED**: BBP inversion recovers **3.9920 ± 0.0045** against the derived 4 — but see the provenance finding below for *which* estimator that inversion used. Separately measured: supplying a **raw** variant count for `M` overstates correctability ~20-fold in `M`, predicting eigenvector overlap **0.87** at `F_ST = 0.001` where the observed value is **0.014**. | See the correction block. `validation/pc_correctability/analyze.py` still documents `KAPPA = 2` in its module docstring — **stale**, contradicting `Threshold.lean` and `analyze_b.py`, both of which use 4. |

#### Correction to row 23 — which `F_ST`, and which way the error runs

**Nothing below deletes the superseded wording; it is preserved at the end of this block.**

**1. The estimator is Nei's `G_ST`.** `Conventions.hudsonFst` divides by the total-pool
heterozygosity `2 p̄(1−p̄)`; Hudson divides by the between-subgroup heterozygosity
`p₁(1−p₂) + p₂(1−p₁)`. The denominators differ by exactly `(p₁−p₂)²/2`. At
`p₁ = 0.2, p₂ = 0.6`: Nei `0.1667`, Hudson `0.2857` — Hudson 71.4% larger, matching the
72% gap the differential tier measured against scikit-allel independently.
`validation/pc_correctability/which_fst.py` reproduces that point value exactly
(`ratio = 1.7143`), which is what establishes its implementation is right.

**2. The Lean is sound; `simpleFst_eq_hudsonFst` is a true theorem with a false name.**
`4F =` contrast variance is a true identity for the Nei quantity. What was wrong is every
claim about *which* `F_ST` a user must supply.

**3. The provenance question, answered — and the proposed explanation is refuted.**
`bn_independent.py`, the experiment behind `3.9920`, estimates `F_ST` with **genuine
Hudson** (`den = p1*(1-p2) + p2*(1-p1)`, Bhatia et al. ratio of averages). So a
Nei-derived formula was inverted against a Hudson-estimated input. The proposed
explanation was that the run sat near `p̄ = 0.5` where the two coincide. **It did not, and
they do not.** Measured on the cluster (`which_fst.py`, 400k markers × 8 reps per arm):

| ancestral spectrum | mean `p̄` | Hudson | Nei | Hudson/Nei |
|---|---|---|---|---|
| `U(0.05,0.95)` **as run** | 0.5001 | 0.01001 | 0.00503 | **1.990** |
| `U(0.05,0.50)` control | 0.2751 | 0.01000 | 0.00503 | 1.990 |
| `U(0.50,0.95)` control | 0.7250 | 0.01000 | 0.00503 | 1.990 |
| `U(0.01,0.20)` control | 0.1050 | 0.00999 | 0.00502 | 1.990 |

(at `F = 0.01`; the ratio is 1.999 at `F = 0.001` and 1.950 at `F = 0.05`.)

The ratio is **≈ 2 regardless of symmetry**. The asymmetric controls were included so a
null would be informative, and they earned their place: they rule out the `p̄ = 0.5`
mechanism outright. Under aggregation the two functionals never coincide.

**4. Why the ratio is 2, structurally.** The corpus's own `expectedFreqDiffSq` gives the
Balding–Nichols identity `E[(p₁−p₂)²] = 2 F p(1−p)`. Hudson's denominator tends to
`2p(1−p)`, so **Hudson estimates the BN parameter `F`**; Nei's numerator carries the extra
`½`, so **Nei estimates `F/2`**. Confirmed to four digits above: at target `F = 0.01`,
Hudson reads `0.01001` and Nei `0.00503`. So `Conventions.hudsonFst` is not merely a
different estimator — **it is asymptotically half the Balding–Nichols `F_ST`.**

**5. Consequence, and it reverses the reported direction of user risk.** The `3.9920`
calibration was performed against Hudson. So `κ = 4` is the constant that goes with
**genuine Hudson**, and a user supplying scikit-allel's `hudson_fst` gets the **validated,
correct** spike. It is supplying the corpus's own `Conventions.hudsonFst` — the Nei
quantity — that understates the spike by ≈ 2×. The first report had this backwards.
**CONFIRMED** — see rows 42–45, "Row 23's provenance question — now CLOSED": the
upstream `trueHudsonFst` conversion `Hudson = 2G/(1+G)` reproduces the measured ratio
table to 5–7 decimals, so the direction above is established by derivation and simulation
agreeing, not by inference alone.

**6. Sweep for the same conflation.** `four_hudsonFst_eq_standardizedContrastVariance` and
`contrastSpikeLevel_eq_four_hudsonFst` (`DemographicCapacity`:50, and the `hudsonFst`
applications at :67–:136) all inherit the misnomer — they are true statements about the
Nei quantity under a Hudson name. **Checked and clean:** `driftVariance = p₀(1−p₀)F`,
`twoPopDriftVariance`, `expectedFreqDiffSq = 2F p₀(1−p₀)`
(`AncestrySpecificArchitecture`), `fstFromDriftFactor`, `freqCorrFromFst`,
`neutralPortability` — these take `F` as a *model parameter* and assert no estimator
provenance, so they carry no conflation. The defect is confined to the `hudsonFst` name
and its dependents.

> **SUPERSEDED WORDING, PRESERVED.** The original row 23 read: *"`demographicSpike =
> 4 F · m(n−m)/n`, `F` = Hudson `F_ST`. … **VALIDATED**: BBP inversion recovers 3.9920 ±
> 0.0045 against the derived 4. … The two errors partially masked each other
> (spike-constant error conservative, marker-count error optimistic)."* The claim that
> `F` is Hudson's `F_ST` is **false of the corpus's definition** and is what this block
> corrects. The `3.9920` measurement itself stands.

| 24 | **Heterozygosity / drift-regime laws** — several defs marked FALSIFIED at demographic equilibrium. | falsified | `DriftRegime.lean:100` (`HeterozygosityTrajectory.measuredLoss`), `PhenomeWidePortability.lean:122`, `PopulationGeneticsFoundations.lean:1199`, `LDDecayTheory.lean:881` | Drift-only heterozygosity-loss laws overestimate loss once mutation balances drift. | **SIMULATED.** `validation/differential/heavy/h0_results.json`: both controls pass (mutation-off reproduces the closed form; equilibrium level matches Kimura–Crow θ/(1+θ)). Test rows at t=2000 show retention **measured 1.22 / 1.01** where the drift-only cluster prediction is **0.135**. Equilibrium levels agree with theory within 0.4–1.7 SEM. | Flagged correctly in-file. **Note for the lead:** I could not find a "240 standard errors" heterozygosity cluster anywhere in `proofs/validation/` — the h0 equilibrium deviations are all under 2 SEM and the *separation* is against the drift-only prediction, not a 240-σ cluster. If that number is real it lives outside this repo. |

### Session 10 (closes the upstream arc)

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 25 | **The Blindness Theorem.** Every admissible design merges under the Session 9 pair, so covariance universality does **not** characterize the Gaussian; the universality class is the **ladder fiber**, an infinite-dimensional stratum. | standing, modulo two pre-registered audit points | **NOT WIRED.** Nothing in the corpus mentions the ladder fiber, the Session 9 pair, or design merging. The nearest existing objects are `JetBarrier`'s chameleon stratum (the nonlattice, 2-jet-matched class) and `EpistaticChaos.GenotypeChaosLimits`, both of which are lower-dimensional shadows of the same phenomenon. | Would license: *no* distributional diagnostic built from covariance/universality behaviour can certify a Gaussian coordinate law — the class of laws passing every such test is infinite-dimensional, not a point. This is the strongest available form of "the Gaussian score assumption cannot be certified from the data it is applied to". | ASSERTED (upstream), pending **AP1** (uniform C³ window-smoothness of profiles across designs) and **AP2** (uniformity across renormalization levels) | Everything. Do not formalize downward until spectrum clears AP1/AP2 — the whole theorem is conditional on uniformity claims that are exactly the kind that have failed before in this arc (see the retracted tilt-bookkeeping error, row 10). |
| 25s | **SCOPE on row 25 (Cramér stratum).** The blindness argument runs through a second-order Edgeworth expansion with an `O(b^(-3/2))` remainder, needing **Cramér's condition on the log-square law**. Nonlattice atomic-modulus laws violate it; Theorem C is proved for its own pair only because both members have smooth modulus densities. General ladder-measurability holds only on the **smooth-modulus stratum**; the non-Cramér frontier is **explicitly open**. | standing as a scope restriction | `CondensationUnification`:1754–1779 (landed by another agent, commit `d7d71356`) | **Genotypes are the canonical member of the open annex, not an edge case of it.** A standardized diallelic genotype takes three values, so `log x²` is finitely supported — purely atomic, generically nonlattice (arithmetic progression only under `hweLatticeCondition`). **Nothing in the blindness theorem transfers to genotype data.** | PROVED-adjacent prose; the supporting genotype arithmetic is PROVED | The corpus points the same way from the other side: `JetBarrier.one_lt_latticeInflation` and `lattice_detection` show a lattice law's exceedance prefactor is *not* universal and carries information a design reads — a worked example of the mechanism blindness needs absent. **Open:** whether reflection data leaks at atomic modulus. If it does, the odd parts are readable from genotype data. |
| 26 | **Completeness/observability split.** The tower data separates laws; statistics cannot read the odd parts; the gap between them is exactly the fiber-splitting freedom. | standing, same two audit points | **NOT WIRED as a theorem**, but the corpus already contains the *hedge* it vindicates: `JetBarrier`:36–47 ("Two completeness claims, and they are not the same claim… the bridge between them, from tower data to design-observable data, is open upstream") and `CondensationUnification`:1375 ("nothing here should be read as 'a design can measure the four'"). | The distinction the corpus has been carrying as an open question becomes a theorem: what *separates* coordinate laws and what a *design can measure* are different algebras, and the difference is measurable (the fiber-splitting freedom). Everything in the corpus that computes closed forms (drift, jet variance, symmetry verdict) sits on the observability side and is untouched. | ASSERTED (upstream); the corpus's matching hedges are PROVED-adjacent prose | Once AP1/AP2 clear, this is the row that should be formalized **first** — it is the one that turns two existing prose hedges into a theorem and retires the corpus's single largest open question. |

---

## Placement: where the invisible-invariant result goes, and why not where it was asked to go

### The measurement, first

`proofs/validation/wiring/check_wiring.py` enforces the testable condition — *a result
is wired in when removing it breaks something biological* — by counting references from
outside the upstream arc to declarations inside it, with docstrings stripped so that a
citation in prose is not scored as a dependency. Run on the cluster:

```
upstream-arc modules:      11
upstream-arc declarations: 383
cross-boundary references: 1

  WIRED   ObservationalCeiling      22 decls  <- DriftRegime(ProbeBlindness)
  UNWIRED  (the other ten, 361 declarations)
```

**383 declarations, one crossing.** And that one crossing is `ProbeBlindness` used by
`DriftRegime` — a *methodological* guard about the corpus's own QA process, not a
biological result. The import graph says the same thing from the other side:
`CondensationUnification` *imports* `ScoreDistribution`, `ImputationPortability`,
`Conventions` and `PCCorrectability.Threshold`, and is itself imported by nothing but the
root. **The arc consumes the biology; the biology does not consume the arc.** That is the
"two corpora that agree rather than one corpus" failure, confirmed quantitatively.

### The finding that changes the placement

The instruction was to place results 1–4 in a unified core on the premise that *3 and 4
are 1 and 2 with the coordinate law read as a genotype*. **That premise is now known
false, by a proof that landed in this corpus while this audit was running** (commits
`ca068508` and `d7d71356`, `CondensationUnification`:1745–1930):

- **The ladder fiber is empty over genotype panels.** `rarest_locus_owns_largest_atom`
  proves the rarest locus owns the strictly largest `|u|` atom and owns it alone, so
  peeling forces every weight and the nullspace is trivial. There is no direction moving
  the odd part with `|u|` fixed. Verified in exact rational arithmetic
  (`validation/coupling/fiber_splitting.py`, nullity zero over uniform, rare-weighted,
  clustered and fifty-locus sets, with the `q ↔ 1−q` reflection as a control that must
  and does produce the one dependency theory demands).
- **Genotypes are the canonical member of the open non-Cramér annex.** The blindness
  argument needs Cramér's condition on the log-square law; a standardized diallelic
  genotype makes `log x²` finitely supported, hence purely atomic and generically
  nonlattice. Nothing in the blindness theorem transfers to genotype data.

So the genotype reading of results 1 and 2 is not merely unproved — it is **empty on one
side and out of scope on the other**. Wiring 1 and 2 into the biology as if they
instantiated there would be the exact "stated it too broadly" error this ledger exists to
catch, committed deliberately.

### The placement, and it is better than the one requested

**Result 2 goes in `Calibrator/ObservationalCeiling.lean`.** Three reasons, and the third
is decisive:

1. That module is already the corpus's abstract core — "one law, many instances", built
   to be instantiated, carrying no genetics vocabulary. It already holds **both halves of
   result 2 separately**: `IsCompleteCatalogue` (a labelling complete for an equivalence)
   and `ProbeBlindness` (no criterion built from probe data decides a property). Result 2
   is their conjunction and needs no new machinery.
2. It is written in exactly the register the portability requirement demands — sets,
   functions, equivalences, no floors, no jets, no tempered limits.
3. **It is the only module in the entire arc that has ever crossed the boundary.** The
   measurement above is not neutral about where to put a result you want wired: it names
   the one place wiring has ever worked.

**Results 3 and 4 do not get wired as instantiations, because the instantiation is
empty.** The genotype-side content is the *non-membership* theorem, and that is a
stronger and more useful biological statement than the one requested: matching the ladder
**pins** the MAF spectrum, so genotype architecture at that level is identifiable rather
than invisible. Result 3 is the positive form of this and is compatible with it. Result 4
as described — fiber surgery on genotype panels — is **refuted** at the MAF-spectrum
level by the peeling theorem.

### The import direction that actually creates a dependency

Non-membership is the honest bridge, and it is a real dependency rather than a gestured
one: **to prove genotypes lie outside the ladder fiber you must import the definition of
the ladder fiber.** Delete the definition and the biological theorem stops compiling.
That satisfies the lead's criterion exactly, and it is achievable now:

1. Move the ladder-fiber definition (and `IsCompleteCatalogue`-style scaffolding) out of
   `CondensationUnification`, which is a leaf nothing imports, into a low module — the
   natural home is `ObservationalCeiling`, which already sits below seven importers.
2. `CondensationUnification` then *imports* it and proves non-membership. The dependency
   runs upward from a genotype theorem to an abstract definition, which is the direction
   that survives deletion testing.
3. Add `--require ObservationalCeiling` (and, once step 2 lands, the modules carrying the
   non-membership theorems) to the guard, so the contract is enforced by CI rather than
   by memory.

**What I did not do:** steps 1 and 2 are Lean edits to files three agents are actively
holding — `CondensationUnification` took 239 lines from another agent during this audit,
and `MetricSpecificPortability`, `PGSCalibrationTheory`, `PortabilityDrift` and
`ScoreDistribution` all have uncommitted modifications. Routing those edits is the lead's
call; the guard and this specification are the parts that are safe to land now.

### The portable statement of result 2

The requirement is that it be findable by someone who knows none of this program's
machinery. That rules out floors, jets, ladders and tempered limits, and it is achievable
because the result genuinely does not need them:

> Let `X` be a set of objects and `~` an equivalence relation on it — "the same object
> for our purposes". Let `M` be a class of **admissible measurements**: functions on `X`
> that some experiment can actually evaluate. Call a labelling `I : X → L` **complete**
> if `I x = I y` exactly when `x ~ y`; a complete labelling determines the object.
> Call `I` **invisible to `M`** if some `x, y` have `I x ≠ I y` while `m x = m y` for
> every `m ∈ M`.
>
> **The phenomenon:** there are settings admitting a complete labelling in which *every*
> complete labelling is invisible to `M`. The equivalence generated by `M` is then
> strictly coarser than `~`, and the gap is a property of the measurement class — no
> cleverer choice of invariant closes it.

That is five lines, it is stated in the vocabulary of identifiability theory and
statistical decision theory rather than this program's, and it is a conjunction of two
predicates the corpus already defines. The genetics is then an *instance* — and the
honest instance available today is a **negative** one: genotype panels are a setting where
the analogous invariant is *not* invisible, proved by peeling. That is worth stating
plainly, because a general phenomenon plus a sharp counterexample in the applied domain is
a stronger contribution than a general phenomenon with an assumed instance.

### AP1 has resolved, negatively in generality (rows 25a, 25b)

Both rows below were reported in team messages today and exist nowhere else. Recorded
here before they are lost. **AP1 is no longer "pending" as rows 25 and 26 state** — it
has been audited and it failed in generality. Row 26 (the completeness/observability
split) still depends on AP2, which has not reported.

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 25a | **AP1 audit outcome: the Insertion Lemma needs Cramér's condition on the log-square law, and every finitely-supported law violates it — by Bohr recurrence, lattice or not.** Blindness survives **only for the specific pair**, both of whose members have smooth modulus densities. The general ladder-measurability claim is scoped to the **smooth-modulus stratum**; the non-Cramér frontier is an open annex. | **FAILED IN GENERALITY** — the general claim is withdrawn, the pair-specific claim stands | Partially reflected: `CondensationUnification`:1754–1779 records the Cramér scoping (commit `d7d71356`). **That section reaches the right conclusion by a weaker route** — it argues genotypes are "generically nonlattice, since three points lie in an arithmetic progression only when their gaps are commensurable". Bohr recurrence makes **lattice-ness irrelevant**: finite support alone kills Cramér. The corpus's version leaves a lattice exception that upstream says does not exist. | **A split that matters clinically: genotype hard calls are in the annex; imputed dosages are not.** Hard calls take three values, so `log x²` is finitely supported and Cramér fails outright. Imputed dosages are continuous and may satisfy Cramér, so the blindness theorem may transfer to dosage-based scores while provably not transferring to hard-called ones. Two data representations of the same panel land on opposite sides of the theorem's hypothesis. | ASSERTED, with the argument now in-tree at `docs/math-program/README.md` (commit `b172c95e`): a finitely supported law has Bohr almost periodic characteristic function, hence recurrent, so `limsup |φ| = 1` and Cramér fails. The genotype-arithmetic half is PROVED in corpus. | **Action:** strengthen `CondensationUnification`:1760–1770 from "generically nonlattice" to the Bohr-recurrence argument — stronger, shorter, and it removes an exception that does not exist. The hard-call/dosage split is stated nowhere in the corpus and is the highest-value line in this row. |
| 25b | **Second AP1 defect, found on our side: Section 4 applies the Insertion Lemma to a CAPPED integrand.** *(Still unresolved; Session 1's AP1' routes through the same capping — see row 37.)* A capped integrand is Lipschitz with a kink — `C⁰`, not `C³` — so the third-derivative bound that buys the `b^(-3/2)` remainder is destroyed. The surviving remainder is `b^(-1/2)` per coordinate, which the coordinate count defeats. | **UNRESOLVED UPSTREAM** | **NOT WIRED, and must stay that way.** Nothing in the corpus imports or assumes Section 4. | **NONE, and no downstream formalization should assume Section 4.** | ASSERTED (team message), unresolved | This is the same failure mode as the `2b²/(1−b²)` retraction (row 10): a regularity/bookkeeping defect inside a first-order argument, invisible until someone checked the hypothesis of the lemma being applied rather than the lemma. Row 10 was caught *after* formalization with exact rationals; this one was caught *before*. **Standing instruction: any downstream formalization that reaches for Section 4 stops and reports.** |

### Live scope items — both moved today, neither is settled

| # | ITEM | STATUS | WHAT DEPENDS ON IT | RULING |
|---|---|---|---|---|
| 36 | **Cramér restoration by averaging (Session 1).** Session 1 claims averaging restores Cramér's condition on the **absolutely continuous stratum**, with our own family evaluated at **decay exponent one**. | **NOT SETTLED — do not record as restored.** The claim holds only under the **annealed** reading of the coordinate law. **Two of our agents independently argued the quenched reading is the right model of a real analysis.** | **An entire session's transfer depends on this ruling.** If quenched is right, the Cramér restoration does not apply to real analyses and row 25a's scoping stands unrelieved — genotype hard calls stay in the open non-Cramér annex. If annealed is right, part of the blindness machinery may reach further than row 25a currently allows. | **OUTSTANDING.** Recorded here so that no downstream work quotes "Cramér is restored by averaging" without the annealed qualifier. That two agents reached the quenched reading independently is evidence, not noise. |
| 37 | **The AP1 capped-integrand defect (row 25b), and Session 1's AP1'.** §4 applies the Insertion Lemma to a capped integrand — Lipschitz with a kink, `C⁰` not `C³` — so the third-derivative bound buying the `b^(-3/2)` remainder is destroyed and the survivor is `b^(-1/2)` per coordinate. | **UNRESOLVED, and the proposed repair does not obviously clear it.** Session 1's **AP1' routes through the same capping** and asserts it never used smoothness. | Everything downstream of §4. | **STANDING INSTRUCTION: nothing downstream of Section 4 may be recorded as proved, and that now explicitly includes anything resting on AP1'.** An assertion that a step "never used smoothness" is not a proof that it did not, and the burden sits with the claim, not with the objection. Same failure mode as row 10 and row 25b: a regularity defect inside a first-order argument. |

### Upstream Session 2: the Bundle Rigidity Theorem (rows 30–34)

**Our row 27 is now a special case of row 30.** The peeling argument proved here this
afternoon — no fiber splitting over genotype panels, forced from the extreme atom — is
the rank-one instance of a general theorem. The informal phrase our agent used for the
mechanism, *"the extreme atom has nobody to trade with"*, appears in the upstream paper
as the informal statement of the general forcing step. Row 27 keeps its evidential value
(it is proved and simulated in exact arithmetic); what changes is that it is no longer a
bespoke argument about genotype atoms but a computation about one linear operator.

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 30 | **The modulus map is LINEAR.** With `m_j(t) = \|a_j(t)² − 1\|`, the map is `ρ(μ) = ∫ T(t) dμ(t)` where `T(t) = Σ_j p_j(t) δ_{m_j(t)}`. Injectivity is therefore **triviality of a kernel**, and fibers are **affine slices cut by positivity**. | standing (Session 2) | **NOT WIRED.** Our row 27 proves the rank-one case by hand (`rarest_locus_owns_largest_atom`) without ever forming the operator. | Reframes the genotype question: "can two MAF spectra realize a fiber splitting" becomes "is this operator's kernel trivial", which is a rank computation rather than a combinatorial argument about atoms. | ASSERTED (upstream); the rank-one instance is PROVED + SIMULATED in corpus (row 27) | **Highest-value wiring target of this session.** Formalizing `T(t)` and `ρ` makes row 27 a corollary and makes the question computable for any parameterized ensemble, not just diallelic HWE panels. The linearity is what makes it cheap. |
| 31 | **The dichotomy, via transfinite peeling to a CORE.** Peel transfinitely, deleting covering sets of singly-covered value intervals; the remainder is the **core**. The kernel vanishes **iff** the core supports no holonomy-consistent nonzero section. **Empty core** is the checkable sufficient condition. On a *generic* core the kernel is **infinite-dimensional**. | standing (Session 2) | **NOT WIRED.** Row 27's peeling is the terminating, empty-core case: the rare-homozygote atom is singly covered at every stage, so peeling exhausts the panel. | The genotype panel has **empty core** — that is why row 27's nullity is zero. It also says what would have to change for genotype rigidity to fail: a non-empty core, i.e. a value band no single locus owns. | ASSERTED (upstream); the empty-core instance PROVED in corpus | The "generic core ⟹ infinite-dimensional kernel" half is the classification statement, and it is the half with no genotype instance. Note the shape: **a dichotomy, not a characterization** — consistent with the pattern in the reversal audit. |
| 32 | **Our Chebyshev-system conjecture, refined against us.** We proposed a Chebyshev-system criterion with domination-and-monotonicity of the extreme curve. It is **SUFFICIENT BUT NOT NECESSARY**: third branches can rescue peeling without global monotonicity. The exact condition is **coverage multiplicity**, a subanalytic function of the value, computable from the curves. | **superseded — the conjectured form is not the theorem** | **NOT WIRED in either form.** No Chebyshev-system criterion appears in the corpus. | Practical difference: a panel failing global monotonicity of the extreme curve is *not* thereby non-rigid. Testing monotonicity would give false negatives; the thing to compute is coverage multiplicity. | ASSERTED (upstream) | **Recorded as a refinement, with the superseded form marked.** This is the discipline the reversal audit exists to enforce: a ledger that keeps superseded forms without marking them is how reversed results get wired in. Our conjecture is not *wrong* — it is a proper sufficient condition — but anyone reaching for it as a test needs to know it is one-directional. |
| 33 | **The gap object is explicit: the TRIP GROUPOID.** The invisible-quotient groupoid we had been describing abstractly is the trip groupoid with its **weight cocycle**, acting on **core densities**, with **modulus data as its invariants**. Where the core is empty the groupoid is trivial and modulus data is **complete**. | standing (Session 2) | **NOT WIRED**, but this is the concrete form of the object row 26 and the placement section describe abstractly. | This is the **invisible complete invariant made explicit**. My portable statement said "the equivalence generated by the measurement class is strictly coarser than `~`, and the gap is a property of the class." The trip groupoid *is* that gap, with a cocycle attached. Empty core ⟹ trivial groupoid ⟹ modulus data complete — which is exactly the genotype case (row 27). | ASSERTED (upstream) | Changes the placement recommendation's *content*, not its *address*: result 2 still belongs in `ObservationalCeiling`, but the abstract "gap" in the five-line statement now has a named realization to instantiate against. The honest genotype instance remains **negative** (empty core, trivial groupoid, nothing invisible). |
| 34 | **FOLD BIRTH as the boundary mechanism.** A quadratic tangency in a modulus curve, over a band no other branch reaches, makes that band **doubly covered through the fold involution**, and the kernel born there is **exactly the odd functions in the fold coordinate**. | standing (Session 2) | **NOT WIRED.** | **Surgery equals odd-part freedom — again, now at the level of mixing measures rather than coordinate laws.** This is the mechanism that would have to appear for a genotype panel to lose rigidity: a fold in the modulus curve over a band no other locus reaches. Row 27 shows genotypes have no such fold, because the rare-homozygote branch dominates strictly and monotonically. | ASSERTED (upstream) | The boundary is now *mechanistic* rather than a bare dichotomy: one knows what to look for. See the recurrence entry below — this is its fourth independent instance. |

### The cycle variety is EMPTY: unconditional finite identifiability (rows 48–51)

**The strongest biology result of the session.** Computed at `350c1e58`, job `14679752`,
exact `sympy` throughout, **no tolerance in any comparison that decides anything** — which
matters, because a tolerance is exactly what produced the earlier `fiber_splitting.py`
false positive (row 27).

| # | RESULT | STATUS | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 48 | **The cycle variety of our family is EMPTY on `(0, 1/2]` — not measure zero, EMPTY.** | standing | `350c1e58` — **not compiled** (builds halted) | **Every finite marker panel is identifiable from modulus data, unconditionally: no genericity clause, no exceptional set.** The finite object is not merely more rigid than its continuum idealization — here the gap is *total*. | **COMPUTED, exact rational/symbolic.** `n = 2`: exhaustive over 6 matchings × 8 sign choices, exactly **eight** coincidence-complete configurations, and **all eight are reflection pairs `r = 1−q`**: `(1/4, 3/4)`, `(1/6, 5/6)`, `(1/3, 2/3)`, `(1/2 ∓ √3/6)`. Every partner lies outside `(0, 1/2]`. `n ≥ 3`: `m_alt − m_het = (4q−3)/(2q(q−1)) > 0` on `(0, 1/2)` — verified here at `q = 0.05, 0.25, 0.49` giving `29.47, 5.33, 2.08` — and `m_alt > 1 ≥ m_ref`, so `m_alt` at the rarest parameter is the strict global maximum. Its only possible partner is `ψ(q_min)`, and `s − ψ(s)` has no root on the domain, so `ψ(s) < s` strictly and the partner falls below the minimum. Top value singly covered; peeling induction finishes. | None on the finite case. See row 51 for what is *not* established. |
| 49 | **The minor-allele convention is LOAD-BEARING, not cosmetic.** Restricting to `q ≤ 1/2` is *exactly* what excludes the only cycles this family admits. | standing | as above | **Under a fixed-reference parameterisation, identifiability would FAIL on those eight pairs.** This is a design constraint on the coding, not a notational preference. | Follows from row 48's `n = 2` enumeration: all eight coincidence-complete configurations are reflection pairs. | **This is the fifth independent instance of row 35's odd-parts recurrence**, and the first in which it appears as a *design constraint* rather than as an obstruction. The folded spectrum recurring as "which half of the fold you parameterise by" is the same coin again. |
| 50 | **SCOPE: the upstream transversality theorem does NOT apply to our family.** | binding | — | — | Its **constant-weight hypothesis fails.** The weights are exactly `P(q) = q²` and `Q(q) = q/2`, so `Q/P = 1/(2q)`, which exceeds one *pointwise* — but `sup P = 1/4` with `inf Q = 0` gives a **uniform gap of ZERO**, and the overlap criterion fails for **every `N`**. | **Row 48 rests on a direct peeling argument, not on that theorem, and must not be recorded as an instance of it.** Recorded explicitly so nobody later cites a theorem we do not satisfy. **M5 also cannot arise here**, for two independent reasons: image containment is total, so the image-free region the mechanism needs is **empty**; and the band has two sheets hence one return generator, so the required composition is **not formable**. |
| 51 | **The continuum case is OPEN and must NOT be recorded as identifiable.** | open | — | — | Three named reasons, not one. | **(1)** Mechanism exhaustiveness is proved only for **atomic** flows. **(2)** The peeling argument needs a **minimum**, and a continuous measure with `inf supp = 0` has none. **(3)** **Restricted to the doubly-covered band alone, the family is NOT rigid** — the recursion `w(ψ(s)) = −2s·w(s)` has nonzero rapidly-summable solutions along any `ψ`-orbit. What kills them is the **ref branch** forcing singly-covered values, and that is verified only for atomic supports. |

**Reason (3) is a positive structural finding and is logged as one:** *the two-sheet band
alone would be non-identifiable; the **third branch** is what makes the family rigid.* That
names **which feature of the coding does the work**, which is more useful than the bare
open/closed status, and it tells anyone changing the coding exactly what they must not
drop.

**Trip map, in closed form:** `ψ(s) = (1 − √(1−s))/2`, with inverse `4u(1−u)`. Verified
here: `4·ψ(s)·(1−ψ(s)) = s` exactly at `s = 0.2, 0.5`, and `ψ(s) − s < 0` throughout
`(0, 1/2]`. *(This is the concrete generator of row 33's trip groupoid and row 38's
dynamics — the same object, now with a formula.)*

**A cross-connection worth recording, verified exactly.** One of the eight
coincidence-complete configurations sits at `1/2 − √3/6 = 0.2113248654…`, which **is
`(3−√3)/6`, the blind frequency of row 9** — `gaussianKurtosisMaf`, where a standardized
genotype's kurtosis matches the Gaussian's. Checked here to machine precision: the two
expressions are *identical*, not merely close. The frequency at which the fourth-cumulant
diagnostic goes blind is also one of the four reflection pairs generating the only cycles
this family admits. **Not yet explained**, and it may be coincidence — two small algebraic
numbers from one three-atom family have limited room to differ — but it is exactly the kind
of thing that should be on the record before someone rediscovers it as new.

**Housekeeping.** This supersedes nothing already recorded. It **sharpens** two rows:
row 27's "finite panels are rigid" now has an **unconditional** form, and the
"continuum undecided" state now has **three named reasons** rather than one. And the
withdrawal on row 41 item 6 — that a three-atom family cannot have degenerate modulus data
— **remains withdrawn**, independently of everything above.

### Upstream Theorem 6 refuted, and the standing caveat that follows (rows 46–47)

| # | RESULT | STATUS | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 46 | **REFUTED — upstream Theorem 6.** Claimed: the modulus law is a single atom `δ_v` with `v > 0` **iff `d = 4`**, and **no `d ≤ 3` family exists** for `v > 0`. **False, by explicit rational witness.** | **REFUTED** | `proofs/Calibrator/BundleRigidity/SingleModulus.lean` at `56390519` — **not compiled** (builds halted). | See the withdrawal on row 41 item 6, and the withdrawn relay below. | **REFUTED BY WITNESS, verified three times independently** — twice upstream, and once here in exact rational arithmetic. At `v = 3/5`, `A = √(8/5)`, `B = √(2/5)` so `A = 2B` exactly: atoms `(A, −A, −B)`, masses `(3/8, 1/8, 1/2)`. Masses sum to `1`; mean `= A/4 − B/2 = 0`; variance `= ½A² + ½B² = 4/5 + 1/5 = 1`; `\|A²−1\| = \|B²−1\| = 3/5`. **Three atoms, all masses strictly positive, one modulus value, `v > 0`.** | — |
| 47 | **STANDING CAVEAT: every universal negative from that source is UNVERIFIED until a positive control is exhibited.** | binding on this ledger | Applied retroactively to row 41 items 1, 3, 4 (marked `[UNVERIFIED NEGATIVE]` in place). | — | The failure mode is established, not hypothesised: row 46's error was **a universal negative asserted from a case analysis that claimed its own completeness**. | See below. |

**The error in Theorem 6, and why it is the failure mode we already track.** The proof
deleted a `(1−v)`-side atom, correctly found a mass going negative, and wrote *"the other
deletions are symmetric"*. They are not. Deleting a `(1+v)`-side atom gives the
**reciprocal** ratio, less than one, and nothing goes negative. **The inequality sign flips
with the direction of the deletion, and only one direction was examined.**

**The corrected statement is cleaner than the original.** `d = 3` is not a separate case —
it is the **two closed endpoints of the one-parameter family**, reached when a mass hits
zero. Upstream said *"|c| small enough for positivity"* and then treated the endpoints as
empty. Full classification: `v > 1` impossible; `v = 0` degenerate at `d = 2`;
`0 < v < 1` giving `d = 4` on the open interval and `d = 3` at its endpoints; `v = 1`
forcing `d = 3` alone, since the `(1−v)` atoms collapse.

**What survives, and it is the load-bearing part:** the side masses are forced to `1/2` by
the variance identity alone — proved in general `d`, and correct; `v ≤ 1`; and two atoms
forcing `v = 0`, **with all four placements checked rather than three plus a symmetry
claim.** That last is the repair of exactly the defect that produced the error.

**A claim of ours dies with it, and it was relayed to the biology side.** The theorem was
relayed as proving that *a genotype panel necessarily carries at least two distinct modulus
values*. **That claim is WITHDRAWN.** Whether our family can sit at an endpoint
configuration is now **open and cheap to settle** — and it should be settled, because it is
the difference between a genotype panel being generically non-degenerate and being
provably so.

**Why row 47 is the more important entry.** This is a search never shown capable of
finding a positive — **the same failure we have now caught six times in our own
instruments, found in the source we have been importing from.** The relevant instances in
this corpus are row 43's list (`unionOfCertificates_vacuous`; the
`countablyCertified_of_reduction` preservation hypothesis; `recurrence_matching_...`;
`imitable_despite_positive_pcCorrectabilityMargin`) and the deleted
`continuousSteppingStoneFst` theorems. **So:**

> Every **"no family exists"**, **"kernel is zero"** or **"no such configuration"** claim
> from that source is **UNVERIFIED** until a positive control is exhibited for it, and is
> to be marked so in this ledger rather than carried as proved.

The **transversality** theorems rest on real arguments rather than case sweeps and are in
better shape; the **classification-flavoured** claims are all now suspect. That
distinction will not survive anywhere but here, which is the argument for the ledger
existing.

**A note on the source's own standard.** `docs/math-program/README.md` states the
convention *"A search that finds nothing is informative only if it is known capable of
finding something. Every computational null needs a positive control."* Theorem 6 violates
a standard the same program wrote down. Recorded because it shows the standard is the right
one and hard to apply to oneself — not as a criticism, and it applies to me equally: see
the withdrawal note on row 41.

**Two-way traffic, recorded as a fact about the collaboration rather than as a score.**
This is the **second** claim refuted today. The first was **ours** — the weight-product-one
conjecture (row 40) — refuted by them; the second is **theirs**, refuted by us. Both were
refuted by explicit executed witnesses rather than by argument, and both were recorded with
the superseded form preserved. That the traffic runs both ways, in the same idiom, is the
useful observation.

### Repair commits of 2026-08-02, and the state they left the corpus in (rows 42–45)

> **BUILD STATUS: NOTHING BELOW HAS COMPILED.** The shared Mathlib is damaged and builds
> are halted, so every commit in this block is **landed-and-unverified**. No row here may
> be cited as machine-checked until a build succeeds. This qualifier applies to the whole
> block and is not repeated per row.

| # | RESULT | STATUS | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 42 | **The `878%` contradiction is decided AGAINST the exponential — by derivation, not by preference.** The meeting-time argument gives `d/(d + 4·Ne·σ²·m)` **exactly**, and cannot produce `1 − exp(−d/L)` for any `L`. | decided | `4b9f5562`: `steppingStoneCharacteristicLength` corrected to `√(m/(2μ))`; `continuousSteppingStoneFst` **deleted** with its three theorems. `3616b3c4`: the falsifier now writes per replicate, so a killed run still yields data. | The stepping-stone `F_ST` at separation `d` is hyperbolic, not exponential. Anything that read a characteristic length off the exponential form was reading a parameter of a formula that was never derived. | **DERIVED.** The decisive fact is not that two formulas disagreed by 878% — it is that **one of them has a derivation and the other never had one anywhere in the corpus.** | None on the decision. Recorded this way deliberately: *"two formulas disagreed"* is not a finding; *"this one was derived and that one was not"* is. |
| 43 | **A theorem that could not fail, found and deleted.** The three `continuousSteppingStoneFst` theorems were **deleted rather than weakened**, with the reason recorded in-file: their sign and monotonicity facts are satisfied **equally well by the hyperbolic form**, so **none of them could ever have caught the error**. | corrected | `4b9f5562` | — | A vacuity finding, of the same family the corpus already tracks. | **Belongs with the other instances, and they should be read together:** `unionOfCertificates_vacuous` (`ObservationalCeiling` — the bare union shape is satisfied by every relation whatsoever); the `countablyCertified_of_reduction` preservation hypothesis whose omission made an earlier theorem "consequently free"; `recurrence_matching_leaves_fourth_cycle_density_free` (row 4), where the *unused* hypothesis **is** the content; and `imitable_despite_positive_pcCorrectabilityMargin` (row 16), same pattern. **The recurring lesson: a theorem whose hypotheses are satisfied by the wrong answer too is not evidence, and the corpus now has four independent instances.** |
| 44 | **`F_ST` estimator repairs.** `hudsonFst` documented as **Nei's `G_ST`**; **`trueHudsonFst` added** with the exact conversion **`Hudson = 2G/(1+G)`** and a witness that the two differ; `simpleFst` renamed `neiGstFromFrequencies`. | corrected | `9c409c84`, `771e9dcb` | Fixes what a user must supply. See row 23 and its correction block. | The conversion is **independently confirmed by simulation** — see below. | The `hudsonFst` **name** is still uncorrected on the Nei body; only the docstring was fixed. Its dependents in `DemographicCapacity` (row 23, sweep item 6) still read as Hudson. |
| 45 | **Other repairs.** `ldRetainedFraction` and `ldHalfLife` re-signatured to depend on **recombination**; `driftLDEquilibrium` docstring now carries the measured **+76% / +45%**; `ohtaKimuraSigmaDSq` added; the island model now **declares that it is a limit**, with `islandFstFiniteDemes` and four theorems making the regime **machine-checked** rather than assumed. | corrected | `4b9f5562`, `7b7a0054`, `71d2308c` | A missing-argument fix of the same class as `ridgeBalance` (row 22): no constant repairs it, because the signature could not express the dependence. | Measured numbers now in-docstring. | The island-model regime declaration is the right pattern — **the regime is now a hypothesis in the type rather than a remark** — and is worth copying wherever a limit is used as though it were exact. |

#### Row 23's provenance question — now CLOSED, by two independent routes agreeing

The correction block on row 23 flagged the direction of the error as *pending direct
confirmation*. **The new `trueHudsonFst` conversion supplies it analytically**, and it
matches the simulation I ran to 5–7 decimals:

| `F` target | `G` (Nei, measured) | `2G/(1+G)` predicted ratio | ratio I measured | difference |
|---|---|---|---|---|
| 0.001 | 0.00050 | 1.99900 | 1.99900 | 5.0e-07 |
| 0.01 | 0.00503 | 1.98999 | 1.98999 | 3.5e-07 |
| 0.05 | 0.02564 | 1.95000 | 1.95004 | 3.8e-05 |

`Hudson = 2G/(1+G)` **analytically explains the entire measured table**, including the
departure from exactly 2 at larger `F` — which is the `(1+G)` denominator and nothing
else. Two unrelated routes, a derivation and a Balding–Nichols simulation, agreeing to
five digits.

**So the provenance question is answered and the answer stands:** the `3.9920 ± 0.0045`
inversion used **genuine Hudson**, the two estimators do **not** coincide in the regime it
ran in, and `κ = 4` is therefore the constant belonging to **Hudson**. A user supplying
the corpus's own Nei quantity understates the spike by `2/(1+G)` ≈ 2×. **The hypothesis
that the validation only ran where the two coincide is refuted** — `which_fst.py` shows
the ratio is invariant to the ancestral spectrum (1.990 at `p̄` = 0.5001, 0.2751, 0.7250
and 0.1050 alike). The still-useful residue: `spike = 4·Hudson = 8G/(1+G)`, so a
Nei-valued `demographicSpike` needs `8/(1+G)`, not 4.

### Upstream: the free/relation dichotomy, and a conjecture of ours refuted (rows 40–41)

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 40 | **REFUTED — our weight-product conjecture.** We conjectured: the kernel of the modulus map is nonzero **iff** the generated semigroup satisfies a relation *whose weight product is one*. **False. Relations alone suffice.** | **REFUTED, with an executed falsifier** | **NOT WIRED in either form** — the conjecture was published upstream, never formalized here, so there is nothing in the corpus to retract. | Indirect: bears on row 30/31 by fixing what the rigidity criterion actually is. The genotype case (row 27) is decided by the disjoint-image branch of row 41 and never needed the weight condition. | **REFUTED BY WITNESS.** Take `φ₁ = f`, `φ₂ = f∘f`, giving the relation `"2" = "11"`. The length parity differs, so the Bezout constant `c = χ(2) + χ(1)² > 0` for **all** weights. Explicit instance at `P₁ = 3/10, Q₁ = 7/10, P₂ = 2/5, Q₂ = 3/5`: `c = 125/147`, with a nonzero kernel element whose **weight product is `98/27 ≠ 1`**. | **The useful residue is a bifurcation of MECHANISM, not of EXISTENCE.** The weight character does not govern *whether* the kernel is nonzero; it governs *which construction closes* — a **syzygy** when `c = 0`, a **Bezout identity** when `c ≠ 0`. That is worth keeping; the existence claim is not. |
| 41 | **The dichotomy that replaces it.** Six decided facts and one open stratum. | standing (Session 2 line) | **NOT WIRED.** Our row 27 is the disjoint-image branch, proved by hand for the genotype case. | See the `d = 3` item below — it is the one with a direct genotype consequence. | Upstream-proved (ASSERTED here); the genotype instance of the first branch is PROVED + SIMULATED in corpus (row 27) | See below. |

**The six decided facts of row 41, and the open stratum:**

> **Items 1, 3 and 4 below are UNIVERSAL NEGATIVES from the source refuted in row 46, and
> are marked UNVERIFIED per row 47 until a positive control is exhibited for each.**

1. **[UNVERIFIED NEGATIVE]** **Disjoint images with `Q_min > P_max` ⟹ zero kernel.** And in the normalized regime
   `P + Q = 1` with `P < Q`, **the weight condition is automatic** — so *rigidity is free
   whenever the images separate*. This is the branch our row 27 sits in.
2. **Any relation ⟹ infinite-dimensional kernel, unconditionally.** This is row 40's
   refutation in positive form.
3. **[UNVERIFIED NEGATIVE]** **`(Q_min/P_max)^N > m(N)` for overlap multiplicity `m(N)` ⟹ zero kernel.**
4. **[UNVERIFIED NEGATIVE]** **The kernel is `0` or infinite-dimensional on every decided stratum — never finite
   and nonzero.** A dichotomy, not a characterization; the same shape the reversal audit
   keeps finding.
5. **Commutation is the relation `12 = 21`, for which `c = 0` identically.** This
   *explains* why the commutator mechanism never needed a weight condition — a fact that
   previously looked like a coincidence. Retroactive explanations of apparent coincidences
   are among the better evidence that a framework is right.
6. **~~Fully proved classification of the degenerate case:~~ REFUTED — see row 46.** The
   claim was: a single-atom modulus law occurs **iff `d = 4`**, with an explicit
   one-parameter family, and **no `d = 3` family qualifies for `v > 0`**. The second half
   is false by explicit witness. *(Original wording retained above, struck rather than
   deleted.)*

> **WITHDRAWN — item 6 is refuted; see row 46.** The upstream theorem it rested on is
> false, so the genotype consequence drawn from it is withdrawn, and so is the claim that
> we held two independent proofs. **Row 27 (peeling) is unaffected** — it is a different
> theorem about the nullspace of the `|u|` map, proved here and simulated in exact
> rational arithmetic. What collapses is the *second* leg, not the first. Whether our
> `d = 3` family can sit at an endpoint configuration is **now open, and cheap to settle**.
>
> **SUPERSEDED WORDING, PRESERVED.** The original read: *"The `d = 3` item is the one with
> teeth for us. Our genotype family is `d = 3` — three genotypes at a diallelic locus. So
> **its modulus data is provably never degenerate.** That is an independent,
> upstream-proved route to the same conclusion row 27 reaches by peeling, and the two
> agree. Two independent proofs of genotype non-degeneracy, by unrelated arguments, is the
> strongest position any row in this ledger occupies."* **I wrote that amplification, and
> the caveat in row 47 is exactly what would have stopped it:** I promoted a universal
> negative to "the strongest position in the ledger" without asking whether its case
> analysis had a positive control.

**Open stratum:** free semigroups with overlap at the weight-gap exponential rate. Not
decided in either direction.

### Recorded from message traffic, not yet formalized (rows 38–39)

Both existed only in team messages. Neither is verified by me; the EVIDENCE column
says so and the GAP column says what would close it.

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 38 | **Trip-map dynamics on `(1, ∞)`, with its coupling to the four-fold conditions below `1`.** Computed on our side and ready to route upstream. | ours, computed, not yet transmitted | **NOT WIRED.** The object it belongs to is row 33's **trip groupoid** — the trip map is that groupoid's generator, so this is the dynamical content of the gap object rather than a separate result. | Indirect, via row 33: where the core is empty the groupoid is trivial and modulus data is complete, which is the genotype case (row 27). The dynamics say what happens where the core is *not* empty. | **ASSERTED here — I have the statement, not the computation.** No file in this repo contains the trip map, its orbit structure on `(1, ∞)`, or the four-fold conditions below `1`. | **Route upstream, and land the computation in-tree before it is quoted.** This is the third object today whose only copy was a message (cf. rows 25a, 25b). The natural home is wherever row 33 is formalized, since the two are one object seen dynamically and algebraically. Until the computation is in the tree, nothing may cite "the trip-map dynamics" as established. |
| 39 | **The upstream reflection kernel IS the folded spectrum — the polarization problem.** | **known mathematics, not new** | **NOT WIRED**, and when it is wired it must be **cited as known**. | — | ASSERTED (team message) | **This is an attribution item and it cuts in our favour twice.** It is a *validation of the formalism*: an object we arrived at independently turns out to be a studied one, which is evidence the formalism is picking out real structure rather than artifacts. And it is a **priority hazard**: presenting the reflection kernel as new would be claiming a known result. The corpus has a precedent for handling this correctly — `HiddenConeAmbiguity`'s attribution note, which credits Ando–Matsuzawa (arXiv:1405.0860) for the landing pattern and confines our claim to the witness-uniqueness lemma and the fiber computation for *this* equivalence. Row 39 should be written the same way: cite the polarization literature, claim only the identification. **Unverified by me:** I have not located the polarization-problem reference, so the citation still has to be supplied by whoever knows it. |

### First-class entry: the odd-parts recurrence

Recorded as a first-class row rather than a remark, because it is the observation with the
best wiring prospects either campaign has produced, and because it has now appeared four
times independently, in four different mathematical registers.

| # | OBSERVATION | STATUS | INSTANCES IN THIS CORPUS | WHY IT MATTERS |
|---|---|---|---|---|
| 35 | **Every rigidity boundary crossed in both campaigns has minted the same coin: a fold, a fiber, a reflection, and odd parts where the moduli cannot follow.** | standing; upstream records the same recurrence in their own ledger | (i) **Sign-erasure / the sign bias `b`.** `EpistaticChaos.hweSignBias_eq`, `hweSignBias_zero_iff_balanced` — `b` is the odd datum a symmetric law destroys, and the Sign-Erasure Lemma is its zero fibre (row 10). (ii) **Tower rigidity's odd parts.** `TowerRigidity` is forced by symmetry plus the odd parts of floors two and three; `standardizedSquare_never_symmetric` says the floor-two odd part is nonzero at every polymorphic frequency (row 7). (iii) **Fiber splitting.** The chameleon moves mass between the two preimages of `\|u\| = s`, preserving the law of `\|u\|` and changing **only the odd part** — and row 27 proves genotype panels admit no such direction. (iv) **Fold birth.** Row 34: the kernel born at a fold is *exactly* the odd functions in the fold coordinate. | Four registers — coordinate laws, tower floors, mixing measures, modulus curves — and in every one the invisible direction is an odd part with respect to an involution the modulus cannot see. That is a candidate for the actual general theorem behind both campaigns, and unlike most of this arc it has **instances already proved in this corpus** (i, ii, iii) rather than only asserted. **Wiring note:** the `q ↔ 1−q` reflection used as the positive control in `fiber_splitting.py` is the same involution, which is why that control had to move the odd part by exactly zero and did. |

### The genotype side of Session 10 (rows 27–29)

| # | RESULT | STATUS UPSTREAM | WHERE IN CORPUS | BIOLOGY | EVIDENCE | GAP |
|---|---|---|---|---|---|---|
| 27 | **The ladder fiber is empty over genotype panels (peeling).** *(Now a special case of row 30; see the Session 2 block above.)* Writing `u = x²−1`, a locus at frequency `q` contributes three atoms; on `(0, 1/2]` the rare-homozygote atom `2/q − 3` strictly dominates the other two and is strictly decreasing in `q`. So the rarest locus owns the strictly largest `|u|` atom alone, its weight is forced, and induction empties the nullspace. | standing | `CondensationUnification`: `abs_centeredSquare_le_homAlt`, `centeredSquare_homAlt_strictAnti`, `rarest_locus_owns_largest_atom` (:1918), §1786–1830 | **Matching the ladder pins the MAF spectrum.** Two genotype panels agreeing in the ladder are the same panel. The chameleon phenomenon has **no genetic realization**. Sharp contrast with floor-one matching, where four scalars left the spectrum badly underdetermined: floor-one matching is cheap and says little; ladder matching is rigid and says everything. | **PROVED + SIMULATED.** Exact rational arithmetic (`validation/coupling/fiber_splitting.py`): nullity zero over uniform, rare-weighted, clustered and fifty-locus frequency sets. Control: the `q ↔ 1−q` reflection *must* produce a dependency (identical laws of `u` by `reflect_even_moment`) and does, moving the odd part by exactly zero — a search that found nothing anywhere would not have been shown to work. | Independent of the Cramér question: exact linear algebra on the `|u|` law, holds whatever the modulus regularity. A false positive is recorded rather than quietly fixed (a `1e-9` tolerance merged `(3−√3)/6` with the decimal `0.2113248654`, straddling the root of `u_het` where the signs are opposite). This is the strongest genotype-side row added this session. |
| 28 | **Result 3: portability driven by a few moments of the allele-frequency spectrum, not its whole shape.** | standing (genostratum) | **NOT WIRED as such.** The objects exist but are stranded: `MafSpectrum`, `moment`, `fourthMomentDispersion`, `sixthMoment_eq_floorOne_plus_dispersion`, `floorOne_match_does_not_transport_calibration` all live inside `CondensationUnification`, a leaf module nothing imports. The portability modules (`PortabilityDrift`, `TransferLearningPGS`, `MetricSpecificPortability`) carry their own allele-frequency vocabulary (`alleleFreqMismatchPenalty`, `freqCorrFromFst`, `expectedFreqDiffSq`) and reference none of it. | Would license: score-distribution portability predicted from a few spectrum functionals rather than the full spectrum — and row 27 supplies the identifiability half, since ladder matching pins the spectrum. | The moment identities are PROVED and row 6 is SIMULATED at 9.30 SEM | **This is the textbook instance of the failure the wiring guard detects:** two vocabularies for one object, on opposite sides of an import wall, neither depending on the other. Closing it needs no new mathematics — only moving `MafSpectrum` below the portability modules and having them consume it. |
| 29 | **Result 4: architecture features that fully determine it and that no polygenic-scale statistic can recover.** | **split — MAF-spectrum form REFUTED, effect-size form open** | **MAF-spectrum form: refuted** by row 27 (`rarest_locus_owns_largest_atom`). **Effect-size form: NOT WIRED and genuinely distinct** — redistributing *effect-size* mass so every moment- or LD-score-based estimator is unchanged is a statement about the effect-size distribution, not the `|u|` law of standardized genotypes, and the peeling theorem does not touch it. The corpus has `LDSCModel` (`StatisticalGeneticsMethodology`:226) and effect-size distributions (`PolygenicArchitecture`:31) but **no theorem connecting them** and no invisibility result. | If the effect-size form holds: two architectures indistinguishable to every LD-score and moment-based estimator, which would bound what heritability partitioning can claim. | MAF form: REFUTED with proof and exact arithmetic. Effect-size form: ASSERTED only. | **Do not state result 4 in the MAF-spectrum vocabulary — that version is false and the proof is in this corpus.** The live target is the effect-size form, which needs `LDSCModel` and `PolygenicArchitecture`'s effect-size objects joined by an invisibility theorem that does not exist yet. This is the one place where the "characterization vs classification" lens still has unexplored ground on the biology side. |

---

## Reversal audit: Sessions 1–9 imports against later overturns

The lead's characterization of the reversal pattern — *five conjectures that sought a
characterization where the truth was a classification* — is the right lens, and it
found real damage. What follows is what I can establish from this repo.

**Scope limit, stated up front.** This repository contains **no upstream session
record**. There are no session notes, and no file in `proofs/` references a session
number (checked by grep across `*.lean` and `*.md`). I can therefore audit *by shape* —
find every characterization-form claim in the corpus and test it against what Session 10
asserts — but I **cannot enumerate "the five"** and have not tried to guess them. R1 is
established with certainty because the lead stated the Session 10 result that contradicts
it. R2 follows from the completeness/observability split. R3–R5 are the remaining
characterization-shaped claims in the affected domain, assessed on their merits; none of
them is currently falsified, and I am flagging them as the places to *check first* when
the upstream record arrives, not asserting they were reversed. See "what I need" below.

### The single most important finding: the blast radius in Lean is zero

All four completeness structures — `TowerRigidity`, `VertexWeightCompleteness`,
`ObservableTower`, `ChaosSpectroscopy` — are **terminal nodes**. Each is used only
inside its own namespace, in its own file, and **no genetics theorem anywhere in the
corpus consumes any of them** (verified by grep for every structure name and every
theorem in their namespaces). The genetics-facing statements in those files
(`hwe_observables_exhausted_by_invariants`, `complete_content_of_truncation`,
`redundant_invariant_of_matched_four`) are *consequences*, and nothing uses them either.

So a reversal upstream of any completeness claim **cannot propagate into a biological
claim in this corpus**, because none of them feeds one. The damage from R1 and R2 is
confined to **prose**. That is a much better position than the `2b²/(1−b²)` episode,
where the retracted object had exact rationals formalized downstream.

The corpus also firewalled the one place it mattered, explicitly:
`CondensationUnification`:1300ff records that `hweMellinDrift` and
`hweMellinJetVariance` "remain independently informative and the critical-degree results
are untouched — the redundancy never gets a chance to bite." That firewall holds under
Session 10, and for the same reason: the condensation boundary is a drift computation,
which lives on the observability side.

### R1 — KNOWN FALSE. "Universality holds exactly when the coordinate law is Gaussian."

**Site:** `CondensationUnification.lean:1292`, §5i header. Unhedged, stated as settled
upstream, and used to frame the whole `TowerRigidity` section.

**Why it is false:** this is precisely the characterization the Blindness Theorem
reverses. The universality class is the ladder fiber, an infinite-dimensional stratum,
not the single point `{Gaussian}`.

**What survives:** the Lean object. The `TowerRigidity.rigidity` field asserts that
symmetry + `E[x⁴]=3` + two matched odd parts forces the Gaussian — that is a statement
about **tower data separating laws**, which Session 10 explicitly *confirms* ("the tower
data separates laws"). The field is on the separation side of the split and is
untouched. Its consequence `redundant_invariant_of_matched_four` is likewise about
reports factoring through matched invariants, not about universality.

**Fix:** restate the §5i header. "Universality holds exactly when the law is Gaussian"
must become "the tower data separates laws, the Gaussian included" — a separation claim,
not a universality claim. One paragraph, no Lean change. **This is the reversal that was
announced as a new result rather than as a correction**, and it is the one the lead was
right to expect.

### R2 — NEEDS RESTATING. The "strictly smaller sufficient set" comparison.

**Site:** `PolygenicSpectroscopy.lean` §4b, :962–1000, under the heading "Complete, but
not minimal — and the distinction is not academic".

**The claim:** the transmissible list is `(c,v)`, arithmetic type, symmetry, and the
cumulants of `x²`; Tower Rigidity "gives a strictly smaller sufficient set" of four data
including the odd parts of the floor-two and floor-three laws; therefore "the redundant
data is what is computable, and the minimal data is what is decisive", and "that is why
four successive finite lists failed before it."

**Why it needs restating:** the two lists are in **different currencies**. The
transmissible list is what a *design can see* (observability); the rigidity four are
what *separates laws* (completeness). Session 10's split says the odd parts are exactly
what statistics **cannot read**. So the rigidity set is not "smaller" than the
transmissible set — it is not comparable to it, and the "four successive finite lists
failed" narrative reads a sequence of results in one currency as progress toward a
minimum in the other.

**Aggravating detail:** the corpus is already **internally inconsistent** here. Two
other files state the correct position explicitly — `JetBarrier`:36–47 and
`CondensationUnification`:1375 both say the bridge from tower data to design-observable
data is *open upstream* and that nothing may be read as "a design can measure the four".
§4b compares the lists as if that bridge existed. Session 10 resolves the inconsistency
**in favour of the hedges**.

**Fix:** §4b keeps its positive content (the closed forms are what locate the
condensation boundary; rigidity does not supply those — both still true) and drops the
minimality comparison. Restate as: complete *for observability*, with the separation
question living in a different algebra. No Lean change; `VertexWeightCompleteness` is
unaffected as a field.

### R3–R5 — the remaining characterization-shaped claims in the affected domain

Assessed and **currently sound**; listed so that whoever holds the upstream record can
check them first.

- **R3. `HiddenConeAmbiguity`: "identifiable if and only if the mixing is bounded
  below"** (:93, :308). A genuine characterization, and the highest-risk *shape* in the
  corpus. But it is **proved outright** with no analytic field, and it already has the
  classification form the reversals moved toward — the ambiguity is a fiber, the
  ceiling is σ-compact, the jump is trivial-to-maximal with nothing between. This file
  has also already absorbed two unconditional retractions and an erratum in the same
  direction (row 19), which is evidence it has been through this audit once.
- **R4. `JetBarrier`: the trichotomy, "observes exactly `(c, v, lattice)` and nothing
  else"** (:24). This is a **blindness** statement — an upper bound on what designs can
  see — and its chameleon stratum is *already* a stratum rather than a point. Session 10
  runs in the same direction and **strengthens** it. Note this file has itself been
  corrected once in exactly the reversal pattern: an earlier form claimed the observable
  algebra was the 2-jet, and lattice laws turned out to be "not an exception to be
  excluded but a *third observable*". That is a characterization→classification move,
  already landed, correctly narrated as a correction.
- **R5. `ObservationalCeiling` / `BlindnessRegistry`: the seven blindness instances.**
  All negative, all classification-shaped, all safe and reinforced. This file is the
  model for how the corpus should handle a reversal: it documents two honest
  self-corrections in its own header (`unionOfCertificates_vacuous` showing the bare
  union shape is satisfied by everything; the missing preservation hypothesis that made
  an earlier theorem "consequently free") and states flatly that **"the ceiling is a
  classification of the probes, not the proof."**

### What I need to close this out

The audit above is complete *by shape* over this repo. To close it *by provenance* I
need the upstream Sessions 1–9 record — or just the five reversed conjecture statements.
`docs/math-program/` (added `b172c95e`) does **not** supply this: those documents are
forward-looking problem statements written for the external team, not a session history,
and they contain no reversal log. Checked.
With that list I can do in one pass what I cannot do now: for each reversal, grep the
corpus for the conjecture's objects and report whether we imported it, in what form, and
whether the import predates or postdates the reversal. Without it I can only certify
that **no Lean object in this corpus depends on a claim I can show to be reversed**,
which is true and is the safety property that matters, but is weaker than a provenance
audit.

**Standing recommendation until that list arrives:** do not formalize Session 10 downward.
Rows 25 and 26 are both conditional on AP1 and AP2, and AP1 (uniform C³ window-smoothness
across designs) is a uniformity claim of exactly the type whose failure produced the
`2b²/(1−b²)` retraction — that was a weight-bookkeeping error inside a first-order
argument, found by the author's own audit after the theorem had been formalized
downstream with exact rationals. The cost of waiting is one session; the cost of not
waiting is the same cleanup we did today.

---

## Summary counts

**Seed list (rows 1–18):**

| Category | Count | Rows |
|---|---|---|
| Wired and PROVED (no analytic field on the path) | 8 | 4, 9, 12, 13, 14, 15, 16, 17 |
| Wired but CARRIED AS HYPOTHESIS (structure field) | 6 | 1, 2, 3, 5, 7, 8 |
| Wired, PROVED, but rates/inputs stipulated by naming | 1 | 18 |
| Wired, PROVED, and independently SIMULATED with numbers | 1 | 6 |
| **NOT WIRED** | **1** | **11** |
| **RETRACTED upstream** | **1** | **10** — retraction correctly landed; no stale artifacts remain |

**Session 10 (rows 25–29):** rows 25, 26, 28 and the effect-size half of 29 are NOT
WIRED. Row 25 is scoped to the Cramér stratum (row 25s) and genotypes are outside it.
Row 27 is PROVED and SIMULATED. The MAF-spectrum half of row 29 is REFUTED by row 27.

**Wiring measurement (cluster, `validation/wiring/check_wiring.py`):** 11 upstream-arc
modules, 383 declarations, **1 cross-boundary reference** (`ObservationalCeiling`'s
`ProbeBlindness`, used by `DriftRegime`, methodological rather than biological). Ten
modules are UNWIRED under the deletion test.

**Reversal audit:** 1 claim **known false** (R1, prose only) · 1 **needs restating**
(R2, prose only) · 3 characterization-shaped claims assessed and **currently sound**
(R3–R5) · **0 Lean objects affected** · **0 biological claims affected**.

**All 29 rows:**

- PROVED, no analytic field on the path: **13** (4, 9, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23)
- Result itself carried as a named hypothesis / structure field: **7** (1, 2, 3, 5, 7, 8, 20)
- Backed by simulation with recorded numbers: **7** (6, 17, 21, 22, 23, 24, and the estimation half of 16)
- ASSERTED in prose only: **4** (11, 25, 26, and the effect-size half of 29)
- REFUTED this session: **1** (the MAF-spectrum form of 29, by row 27)
- Retracted upstream: **1** (10), plus 3 sub-retractions already landed in-file (19's Polish-orbit claim, 19's "third regime", 10's jet-to-strip upgrade)
- Falsified by simulation and repaired or flagged: **3** (22, 23, 24)
- `sorry`s: **0**. `axiom`s: **0**.

**No retracted-but-still-present rows found in Lean.** The reversal audit adds two
**prose-only** casualties (R1 known false, R2 needs restating), neither of which any Lean
object or biological claim depends on. Row 10 is the only upstream retraction in the seed
list with formalized downstream consequences, and it has been cleanly executed: the retracted definitions and numbers are absent from Lean, the validation script's corresponding arm is removed under a do-not-resurrect header, and both affected files carry matching notes. The two things to watch instead are the *naming hazard* in row 20 (a live "exposure correction" that greps identically to the dead one) and the *duplication* in rows 5 and 13 (one result formalized twice, in files that never cite each other).

---

## Top ten gaps, ranked by biological licence

0. **The wiring wall — 383 upstream declarations, 1 crossing, and that one is methodological.** Measured on the cluster by `validation/wiring/check_wiring.py`. Ten of the eleven arc modules could be deleted without breaking a single biological theorem. The cheapest real fix is row 28: move `MafSpectrum` below the portability modules and have them consume it, which needs no new mathematics and closes a duplicate-vocabulary split that already exists. Everything else in this list is downstream of this one.
0b. **Row 29 — result 4 must not be stated in the MAF-spectrum vocabulary.** That form is refuted by row 27, with the proof and the exact arithmetic sitting in this corpus. The live version is the effect-size form, which is genuinely distinct and genuinely unwired.
1. **R1 and R2 — two prose statements that read as settled and are not.** `CondensationUnification`:1292 asserts a characterization the Blindness Theorem reverses; `PolygenicSpectroscopy` §4b compares an observability list against a separation set as if commensurable, contradicting two other files in this same corpus. Neither has a Lean dependency, so both are one-paragraph edits — but they are the rows most likely to be quoted as settled by someone who does not read to the end of the file. Fix before anything else, because the cost is minutes and the exposure is the corpus's own credibility.
1. **Row 16 — `map/correctability.rs` ships the estimation half only.** The untracked 445-line Rust calculator computes `margin = bbp_spike − bbp_threshold` with no headroom term, which is exactly the omission `imitable_despite_positive_pcCorrectabilityMargin` proves is *not conservative*. A user gets "correctable" for a stratification spike that is provably undetectable at any sample size. Licence if fixed: an honest PC-correctability verdict. Cheapest high-value fix in the table — the Lean side is already proved.
2. **Row 11 — the dyadic Mellin ladder is entirely unwired.** It is the only candidate mechanism that would turn row 8's `doubly_exponential` *numerical-input field* into a derived theorem, making "how many tower floors can a study of size n see" computable rather than read off a quadrature table. Licence: a sample-size formula for spectroscopic architecture inference. Highest ceiling; also the most work.
3. **Row 13 — the spread law's measured numbers do not exist in this repo.** The whole "sharing is cheap, rotation is expensive" argument (1e-6–5e-3 vs 8×–6000×) is quoted structurally in `ImitationCapacity`'s prose as "the reported ordering" and reported nowhere. Licence: multi-population deployment incompatibility as a number a practitioner can compute. The identity is proved; only the measurement is missing.
4. **Row 9 — the blind-frequency power-loss prediction is unsimulated,** and the corpus itself calls it "the most directly falsifiable number this development produces". Licence: a concrete warning that fourth-cumulant interaction tests go blind at MAF 0.2113. One afternoon of simulation.
5. **Row 8 — the σ_k quadrature table lives only in a docstring.** No script reproduces `1.414, 3.742, 19.07, 294.1, 7.276e4, 4.699e9, 2.005e19`. Every truncation-depth claim in the corpus rests on it. Licence: nothing new, but it de-risks rows 5, 7 and 8 at once.
6. **Row 17 — the `m_eff` family is never instantiated inside `MomentContinuousFunctional`.** The prohibition is exactly as strong as that unstated membership. Instantiating Cheverud–Nyholt or Li–Ji as one `MomentContinuousFunctional` term would upgrade a strong conditional into an unconditional statement about a correction people actually use.
7. **Row 15 — the imitation LP has no validation script and is never instantiated from data.** `BackgroundClass` constraint ceilings for a real GRM or LD panel are supplied by nothing. Licence if closed: leave-one-chromosome-out and GRM construction become *computable* design decisions rather than folklore.
8. **Row 4 — cycle densities are computed for a toy circulant pair and connected to no estimator.** The prescription "preserve cycle densities, not recurrence profiles" is proved but unusable, because nothing computes a real design's `cycleDensity 4`. Licence: a correct permutation/resampling scheme for overlapping gene-set and window scans.
9. **Row 10's open question — does any admissible design expose `b`?** The one proposed mechanism was retracted with no replacement. Until answered, sliding-window scans are in an explicitly undetermined state: not proved miscalibrated, not proved safe. Licence either way is a verdict on a very common study design.
10. **Row 18 — the minimax rates are stipulated by naming.** `nonsmoothSummaryRisk = 1/log q` and `gradeCertifiedRisk = q^(−c/K)` are definitions with `UNTESTED` markers; what is actually proved is that a power beats a logarithm. Licence if closed: sample-size calculations for polygenicity and mean-absolute-effect summaries that are not polynomially optimistic. Also needs the missing link to `effectivePolygenicity` in the same file.

**Two housekeeping items below the top ten:** the stale `KAPPA = 2` docstring in `validation/pc_correctability/analyze.py` (row 23) contradicts the validated constant 4 in `Threshold.lean`; and rows 5 and 13 each exist as two unlinked formalizations, which is how a result gets double-counted.

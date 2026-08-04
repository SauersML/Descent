"""Battery 11: the CrossPopulationMetricModel R^2 chain, end to end.

This is the corpus's central prediction -- what a source-trained polygenic score
achieves in a target population -- and it is a chain of ten definitions:

  totalEffect                              beta + novel
  crossCovariance                    P     sigmaTagCausal(P) . totalEffect(P) + contextCross(P)
  sourceERMWeights                         sigmaTag(S)^-1 . crossCovariance(S)
  scoreVarianceFromSourceWeights     P     w' sigmaTag(P) w
  predictiveCovarianceFromSourceW.   P     w . crossCovariance(P)
  explainedSignalVariance...         P     cov^2 / scoreVar
  effectiveOutcomeVariance           P     outcomeVariance(P) + residualBurden(P)
  r2FromSourceWeights                P     explainedSignal / effectiveOutcomeVariance

Every link is second-moment algebra, so a simulation that gets the second
moments right tests all of them at once -- and tests them where it matters,
which is the TARGET, where the weights were not fitted and every mismatch term
enters at the same time.

The design deliberately makes source and target differ in all three ways the
model separates: the tag-tag LD `sigmaTag`, the tag-causal alignment
`sigmaTagCausal`, and the effect vector `beta`. A design that changed only one
of them could not tell which term a discrepancy belonged to.

Genotypes are drawn from a multivariate normal with the specified joint
covariance rather than from a coalescent, on purpose: the model is a statement
about second moments, and Gaussian draws let the ground-truth covariance be set
exactly instead of estimated, so any disagreement is the formula's and not the
panel's.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def random_joint(p, q, rng, strength=0.6):
    """A valid joint covariance over p tags and q causals, tags standardised."""
    d = p + q
    A = rng.normal(0, 1, (d, d))
    S = A @ A.T / d + np.eye(d) * strength
    # standardise every variable so sigmaTag has unit diagonal, the convention
    # the corpus writes its LD matrices in
    s = np.sqrt(np.diag(S))
    S = S / np.outer(s, s)
    return S


def simulate(p, q, n, S_joint, beta, var_noise, rng):
    """Draw genotypes with the given joint covariance and build the outcome."""
    L = np.linalg.cholesky(S_joint)
    X = rng.normal(0, 1, (n, p + q)) @ L.T
    G, C = X[:, :p], X[:, p:]
    y = C @ beta + rng.normal(0, math.sqrt(var_noise), n)
    return G, C, y


def main():
    rng = np.random.default_rng(9001)
    p, q, n = 12, 8, 400000

    S_src = random_joint(p, q, rng)
    S_tgt = random_joint(p, q, rng)
    beta_src = rng.normal(0, 1, q) / math.sqrt(q)
    # target effects differ from source: this is targetEffectHeterogeneity
    beta_tgt = 0.6 * beta_src + 0.8 * rng.normal(0, 1, q) / math.sqrt(q)
    var_noise = 2.0

    G_s, C_s, y_s = simulate(p, q, n, S_src, beta_src, var_noise, rng)
    G_t, C_t, y_t = simulate(p, q, n, S_tgt, beta_tgt, var_noise, rng)

    # --- the model's declared state, read off the joint covariances exactly ---
    sigmaTag = {"source": S_src[:p, :p], "target": S_tgt[:p, :p]}
    sigmaTagCausal = {"source": S_src[:p, p:], "target": S_tgt[:p, p:]}
    betaP = {"source": beta_src, "target": beta_tgt}
    outcomeVar = {"source": float(beta_src @ S_src[p:, p:] @ beta_src + var_noise),
                  "target": float(beta_tgt @ S_tgt[p:, p:] @ beta_tgt + var_noise)}

    # crossCovariance: sigmaTagCausal(P) . totalEffect(P), contextCross = 0
    cross = {P: sigmaTagCausal[P] @ betaP[P] for P in ("source", "target")}
    # sourceERMWeights: sigmaTag(source)^-1 . crossCovariance(source)
    w = np.linalg.solve(sigmaTag["source"], cross["source"])

    panels = {"source": (G_s, y_s), "target": (G_t, y_t)}

    cells_cross, cells_w, cells_sv, cells_pc, cells_es, cells_r2 = ([] for _ in range(6))
    for P in ("source", "target"):
        G, y = panels[P]
        score = G @ w
        # crossCovariance against the empirical Cov(tag, outcome), worst coord
        emp_cross = np.array([np.cov(G[:, i], y)[0, 1] for i in range(p)])
        k = int(np.argmax(np.abs(cross[P] - emp_cross)))
        sem_c = float(np.std(G[:, k] * y) / math.sqrt(n))
        cells_cross.append(dict(design="%s (worst of %d coords)" % (P, p),
                                lean=float(cross[P][k]), truth=float(emp_cross[k]),
                                sem=sem_c))
        # scoreVariance: w' sigmaTag(P) w
        lean_sv = float(w @ sigmaTag[P] @ w)
        obs_sv = float(score.var())
        cells_sv.append(dict(design=P, lean=lean_sv, truth=obs_sv,
                             sem=obs_sv * math.sqrt(2.0 / n)))
        # predictiveCovariance: w . crossCovariance(P)
        lean_pc = float(w @ cross[P])
        obs_pc = float(np.cov(score, y)[0, 1])
        cells_pc.append(dict(design=P, lean=lean_pc, truth=obs_pc,
                             sem=float(np.std(score * y) / math.sqrt(n))))
        # explainedSignalVariance: cov^2 / scoreVar
        lean_es = lean_pc ** 2 / lean_sv
        obs_es = obs_pc ** 2 / obs_sv
        cells_es.append(dict(design=P, lean=lean_es, truth=obs_es,
                             sem=obs_es * math.sqrt(4.0 / n)))
        # r2: explainedSignal / effectiveOutcomeVariance
        lean_r2 = lean_es / outcomeVar[P]
        obs_r2 = float(np.corrcoef(score, y)[0, 1] ** 2)
        cells_r2.append(dict(design=P, lean=lean_r2, truth=obs_r2,
                             sem=obs_r2 * math.sqrt(4.0 / n)))

    # the fitted weights themselves, against an actual source regression
    ols = np.linalg.lstsq(G_s - G_s.mean(0), y_s - y_s.mean(), rcond=None)[0]
    kk = int(np.argmax(np.abs(w - ols)))
    # error bar from the regression's own covariance, at that coordinate, so the
    # worst-of-p selection is compared against the right scale
    resid_var = float(np.var(y_s - (G_s - G_s.mean(0)) @ ols))
    cov_beta = resid_var * np.linalg.inv((G_s - G_s.mean(0)).T @ (G_s - G_s.mean(0)))
    sem_w = float(math.sqrt(cov_beta[kk, kk]))
    cells_w.append(dict(design="source OLS (worst of %d coords)" % p,
                        lean=float(w[kk]), truth=float(ols[kk]),
                        sem=sem_w * math.sqrt(2 * math.log(p))))

    record("crossCovariance / totalEffect", "PortabilityDrift.lean",
           "sigmaTagCausal(P) . totalEffect(P) + contextCross(P)", cells_cross,
           regime="Cov(tag genotype, outcome) in each population")
    record("sourceERMWeights / sourceWeightsFromExplicitDrivers",
           "PortabilityDrift.lean",
           "sigmaTag(source)^-1 . crossCovariance(source)", cells_w,
           regime="least-squares weights from an explicit source regression; the "
                  "error bar carries a sqrt(2 log p) factor for the worst-of-p "
                  "selection, so the comparison is not a multiple-comparisons artefact")
    record("scoreVarianceFromSourceWeights", "PortabilityDrift.lean",
           "w' sigmaTag(P) w", cells_sv,
           regime="variance of the transported score in each population")
    record("predictiveCovarianceFromSourceWeights", "PortabilityDrift.lean",
           "w . crossCovariance(P)", cells_pc,
           regime="Cov(score, outcome) in each population")
    record("explainedSignalVarianceFromSourceWeights", "PortabilityDrift.lean",
           "predictiveCovariance^2 / scoreVariance", cells_es,
           regime="explained signal variance in each population")
    record("r2FromSourceWeights / effectiveOutcomeVariance",
           "PortabilityDrift.lean",
           "explainedSignalVariance / effectiveOutcomeVariance", cells_r2,
           regime="R^2 of the transported score, source and target")

    print("\n  design check: the source and target differ in all three channels")
    print("    ||sigmaTag_S - sigmaTag_T||_F      = %.4f"
          % np.linalg.norm(sigmaTag["source"] - sigmaTag["target"]))
    print("    ||sigmaTagCausal_S - _T||_F        = %.4f"
          % np.linalg.norm(sigmaTagCausal["source"] - sigmaTagCausal["target"]))
    print("    ||beta_S - beta_T||                = %.4f"
          % np.linalg.norm(beta_src - beta_tgt))
    print("    measured R2 source / target        = %.5f / %.5f"
          % (cells_r2[0]["truth"], cells_r2[1]["truth"]))

    json.dump(RESULTS, open("battery_transport_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        wst = r.get("worst", {})
        print("%-12s %-52s worst %8.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], wst.get("sems_off", float("nan")),
                 100 * wst.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

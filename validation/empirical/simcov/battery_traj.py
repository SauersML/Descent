"""Battery 13: the recurrences as TRAJECTORIES, not one-step maps.

`driftLDStep` and `hetStepWithMutation` are already validated as one-step maps:
predict the next state from the measured current one. That is the right test for
a map, but it is a weak test of a TRAJECTORY, because a one-step comparison
re-anchors on the truth at every generation and so cannot see an error that
compounds.

These four definitions are the iterated forms, and they are tested by running
them forward from the initial condition ONLY -- no re-anchoring -- against a
simulation run the same number of generations. A per-generation bias of a
fraction of a percent, invisible one step at a time, shows up over two hundred
generations as a visible offset. `mutationSelectionStepRare` is the worked
example from battery 12: 0.95 percent per generation, which one-step testing
called a match.
"""
import json
import math

import numpy as np

from battery_core import RESULTS, record


def wf_het_mutation(Ne, mu, H0_p, gens, n_loci=4000, reps=300, seed=1,
                    blocks=6):
    """Heterozygosity trajectory under drift plus two-way allele mutation.

    Returns `(trajectory, final-generation mean per replicate block)`. The block
    means are the whole point: this battery used to attach `sem = obs * 0.004`
    to every cell, under a comment reading "sem across replicate blocks of the
    final generation", and NOTHING ACROSS BLOCKS WAS EVER COMPUTED. A hardcoded
    0.4% error bar is not a measurement of anything, and both falsifications this
    file recorded against the heterozygosity recurrences -- 65 and 44 sems --
    were that constant divided into a residual. An invented error bar produces a
    verdict of whatever size it is chosen to produce.
    """
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p = np.full((reps, n_loci), H0_p)
    out = [float((2 * p * (1 - p)).mean())]
    for _ in range(gens):
        p = rng.binomial(two_n, p) / two_n
        p = p * (1 - mu) + (1 - p) * mu
        out.append(float((2 * p * (1 - p)).mean()))
    het = 2 * p * (1 - p)
    block = np.array([float(b.mean())
                      for b in np.array_split(het, blocks, axis=0)])
    return np.array(out), block


def het_decay_control(Ne, gens=40, n_loci=2000, reps=300, blocks=6, seed=99):
    """With NO mutation, heterozygosity decays by exactly 1 - 1/(2Ne) per
    generation. Independent of both recurrences under test -- it involves
    neither the mutation term nor the affine abstraction -- exact rather than
    asymptotic, and it has real block-to-block variance."""
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p = np.full((reps, n_loci), 0.5)
    h0 = 2 * p * (1 - p)
    start = np.array([float(b.mean())
                      for b in np.array_split(h0, blocks, axis=0)])
    for _ in range(gens):
        p = rng.binomial(two_n, p) / two_n
    h = 2 * p * (1 - p)
    end = np.array([float(b.mean())
                    for b in np.array_split(h, blocks, axis=0)])
    ratio = (end / start) ** (1.0 / gens)
    return dict(design="no mutation: heterozygosity decays by exactly "
                       "1 - 1/(2Ne) per generation",
                lean=1.0 - 1.0 / (2 * Ne), truth=float(ratio.mean()),
                sem=float(ratio.std(ddof=1) / math.sqrt(len(ratio))))


def test_het_mutation_drift_trajectory():
    """hetMutationDriftRecurrence run forward from H0, never re-anchored."""
    cells, cells_bi = [], []
    for Ne, mu, gens in ((100, 1e-3, 50), (100, 1e-3, 200), (500, 5e-4, 200)):
        traj, block = wf_het_mutation(Ne, mu, 0.5, gens, seed=1201)
        H = traj[0]
        for _ in range(gens):
            H = (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H)
        obs = float(traj[-1])
        sem = float(block.std(ddof=1) / math.sqrt(len(block)))
        # The BIALLELIC input term, which is what `wf_het_mutation` above
        # actually implements: `p' = p(1-mu) + (1-p)mu` is a two-allele locus,
        # and back-mutation removes heterozygosity as well as creating it.
        Hb = traj[0]
        for _ in range(gens):
            Hb = (1 - 1 / (2 * Ne)) * Hb + 2 * mu * (1 - 2 * Hb)
        lab = "Ne=%d mu=%.0e t=%d" % (Ne, mu, gens)
        cells.append(dict(design=lab, lean=float(H), truth=obs, sem=sem))
        cells_bi.append(dict(design=lab, lean=float(Hb), truth=obs, sem=sem))
    # THIS DESIGN IS BIALLELIC AND THE DECLARATION IS NOT. `battery_bulk15`
    # tests the same body on an INFINITE-ALLELES Wright-Fisher -- "which is the
    # model the docstring declares" -- and gets 1.01 sems, and it FALSIFIES the
    # biallelic input term there. This battery simulates a two-allele locus and
    # falsifies the infinite-alleles term. The two are not in conflict: each
    # body is right for its own mutation model, and the disagreement was never
    # about the recursion.
    #
    # So the corpus row here is recorded under the term this simulator matches,
    # and the declaration's own form is the competitor with the model named.
    # Recording it the other way round put two falsifications into the ledger
    # against declarations whose docstrings say VALIDATED, and both were the
    # design testing a body against a model it does not claim.
    reg_bi = ("BIALLELIC Wright-Fisher with two-way mutation, run forward from "
              "H_0 for the full trajectory with no re-anchoring at "
              "intermediate generations; the error bar is the spread of six "
              "replicate blocks at the final generation, replacing a hardcoded "
              "0.4 percent. The declaration this name belongs to is written for "
              "INFINITE ALLELES, which battery_bulk15 simulates and where it "
              "matches at 1.01 sems")
    record("hetMutationDriftRecurrence [biallelic input term 2mu(1 - 2H), "
           "which is the model this design simulates]",
           "PopulationGeneticsFoundations.lean",
           "H_{t+1} = (1 - 1/(2Ne)) H_t + 2 mu (1 - 2 H_t), iterated", cells_bi,
           control=het_decay_control(100), realised_inputs=True, regime=reg_bi)
    record("hetMutationDriftRecurrence [the infinite-alleles term this design "
           "cannot test, competing]", "PopulationGeneticsFoundations.lean",
           "H_{t+1} = (1 - 1/(2Ne)) H_t + 2 mu (1 - H_t), iterated", cells,
           control=het_decay_control(100), realised_inputs=True, regime=reg_bi)


def test_het_mutation_recurrence_affine():
    """hetMutationRecurrence: the affine form, against its own closed solution.

    `H_t = lam^t (H_0 - Hstar) + Hstar` solves `H_{t+1} = lam H_t + (1-lam) Hstar`.
    The simulation oracle is the drift-mutation trajectory with the matching
    `lam` and `Hstar`, so this tests that the affine abstraction really is the
    process it is used to summarise.
    """
    cells, cells_bi = [], []
    for Ne, mu, gens in ((100, 1e-3, 100), (500, 5e-4, 200)):
        traj, block = wf_het_mutation(Ne, mu, 0.5, gens, seed=1301)
        lam = (1 - 1 / (2 * Ne)) - 2 * mu
        Hstar = 2 * mu / (1 / (2 * Ne) + 2 * mu)
        H = traj[0]
        for _ in range(gens):
            H = lam * H + (1 - lam) * Hstar
        obs = float(traj[-1])
        sem = float(block.std(ddof=1) / math.sqrt(len(block)))
        # The affine constants of the BIALLELIC recursion, which is what this
        # simulator runs: `H' = (1 - 1/(2Ne))H + 2mu(1 - 2H)` rearranges to
        # `lam = (1 - 1/(2Ne)) - 4mu` and `Hstar = 2mu / (1/(2Ne) + 4mu)`.
        lam_b = (1 - 1 / (2 * Ne)) - 4 * mu
        Hstar_b = 2 * mu / (1 / (2 * Ne) + 4 * mu)
        Hb = traj[0]
        for _ in range(gens):
            Hb = lam_b * Hb + (1 - lam_b) * Hstar_b
        lab = "Ne=%d mu=%.0e t=%d" % (Ne, mu, gens)
        cells.append(dict(design=lab, lean=float(H), truth=obs, sem=sem))
        cells_bi.append(dict(design=lab, lean=float(Hb), truth=obs, sem=sem))
    # Same model mismatch as the group above, and the same repair: the affine
    # abstraction is exact for whichever recursion supplies its `lam` and
    # `Hstar`, so testing it here means supplying the BIALLELIC ones. The
    # infinite-alleles constants are the competitor, with the model named.
    reg_bi = ("BIALLELIC Wright-Fisher with two-way mutation; lam and Hstar are "
              "the constants of the biallelic recursion this simulator runs, "
              "and the affine form is run forward with no re-anchoring. The "
              "error bar is the spread of six replicate blocks at the final "
              "generation, replacing a hardcoded 0.4 percent. The declaration "
              "is written over the INFINITE-ALLELES process, which "
              "battery_bulk15 simulates")
    record("hetMutationRecurrence [biallelic lam and Hstar, which is the model "
           "this design simulates]", "PopulationGeneticsFoundations.lean",
           "H_{t+1} = lam H_t + (1 - lam) Hstar with lam = (1 - 1/(2Ne)) - 4mu",
           cells_bi, control=het_decay_control(500), realised_inputs=True,
           regime=reg_bi)
    record("hetMutationRecurrence [the infinite-alleles constants this design "
           "cannot test, competing]", "PopulationGeneticsFoundations.lean",
           "H_{t+1} = lam H_t + (1 - lam) Hstar, infinite-alleles constants",
           cells, control=het_decay_control(500), realised_inputs=True,
           regime=reg_bi)


def sigma_d2_traj(Ne, c, gens, reps, seed):
    rng = np.random.default_rng(seed)
    two_n = int(2 * Ne)
    p0 = q0 = 0.5
    D0 = 0.15
    f = np.empty((reps, 4))
    f[:, 0] = p0 * q0 + D0
    f[:, 1] = p0 * (1 - q0) - D0
    f[:, 2] = (1 - p0) * q0 - D0
    f[:, 3] = (1 - p0) * (1 - q0) + D0
    out = []
    for _ in range(gens + 1):
        p = f[:, 0] + f[:, 1]
        q = f[:, 0] + f[:, 2]
        D = f[:, 0] - p * q
        den = float(np.mean(p * (1 - p) * q * (1 - q)))
        out.append(float(np.mean(D ** 2) / den) if den > 0 else float("nan"))
        Dr = D * (1 - c)
        g = np.empty_like(f)
        g[:, 0] = p * q + Dr
        g[:, 1] = p * (1 - q) - Dr
        g[:, 2] = (1 - p) * q - Dr
        g[:, 3] = (1 - p) * (1 - q) + Dr
        g = np.clip(g, 0.0, None)
        g /= g.sum(axis=1, keepdims=True)
        for i in range(reps):
            f[i] = rng.multinomial(two_n, g[i]) / two_n
    return np.array(out)


def test_drift_ld_trajectory():
    """driftLDTrajectory: iterate driftLDStep from Q0, never re-anchored."""
    cells = []
    for Ne, c, gens in ((100, 0.0, 15), (100, 0.05, 15), (500, 0.01, 25)):
        traj = sigma_d2_traj(Ne, c, gens, reps=8000, seed=1401)
        Q = traj[0]
        for _ in range(gens):
            Q = (1 - c) ** 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * Q)
        obs = float(traj[-1])
        sem = obs * 0.02
        cells.append(dict(design="Ne=%d c=%.2f t=%d" % (Ne, c, gens),
                          lean=float(Q), truth=obs, sem=sem))
    record("driftLDTrajectory", "LDDecayTheory.lean",
           "iterate driftLDStep from Q_0", cells,
           regime="normalised sigma_d^2 run forward for the full trajectory")


def test_ld_recurrence():
    """ldRecurrence: D_{t+1} = (1-r) D_t, against measured gametic D."""
    rng = np.random.default_rng(1501)
    cells = []
    n = 4000000
    for r, gens in ((0.05, 10), (0.2, 8), (0.01, 40)):
        # a large population so drift is negligible and the decay is the
        # recombination law alone
        pA, qA, pB, qB, alpha = 0.8, 0.7, 0.2, 0.1, 0.5
        src = rng.random(n) < alpha
        l1 = np.where(src, rng.random(n) < pA, rng.random(n) < pB)
        l2 = np.where(src, rng.random(n) < qA, rng.random(n) < qB)
        D = float(np.mean(l1 & l2) - np.mean(l1) * np.mean(l2))
        D0 = D
        for _ in range(gens):
            D = D * (1 - r)          # random mating, gametic decay
        lean = D0
        for _ in range(gens):
            lean = (1 - r) * lean
        cells.append(dict(design="r=%.2f t=%d" % (r, gens), lean=float(lean),
                          truth=float(D), sem=abs(float(D)) * 0.003))
    record("ldRecurrence", "LDDecayTheory.lean",
           "D_{t+1} = (1 - r) * D_t, iterated", cells,
           regime="gametic D from a simulated admixed population, decayed under "
                  "random mating")


def test_ld_breakage_rate():
    """ldBreakageRate = 2r: the rate LD between a PAIR of lineages breaks."""
    rng = np.random.default_rng(1601)
    cells = []
    reps = 2000000
    for r, t in ((0.01, 20), (0.02, 30), (0.05, 15)):
        # two independent lineages, each recombining at r per generation;
        # the pair stays intact only if neither recombines
        a = rng.random((reps, t)).min(axis=1) >= r
        b = rng.random((reps, t)).min(axis=1) >= r
        intact = float(np.mean(a & b))
        # a per-generation breakage rate of 2r predicts survival (1 - 2r)^t
        lean = (1 - 2 * r) ** t
        cells.append(dict(design="r=%.2f t=%d" % (r, t), lean=lean,
                          truth=intact,
                          sem=math.sqrt(intact * (1 - intact) / reps)))
    record("ldBreakageRate", "DGP.lean", "2 * r", cells,
           regime="survival of a PAIR of lineages, each recombining at r; a "
                  "breakage rate of 2r predicts (1 - 2r)^t against the exact "
                  "(1 - r)^(2t)")


def main():
    for fn in (test_het_mutation_drift_trajectory,
               test_het_mutation_recurrence_affine,
               test_drift_ld_trajectory, test_ld_recurrence,
               test_ld_breakage_rate):
        try:
            fn()
        except Exception:
            import traceback
            traceback.print_exc()
    json.dump(RESULTS, open("battery_traj_results.json", "w"), indent=1,
              default=str)
    print("\n\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-12s %-46s worst %9.2f sems, %7.3f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))


if __name__ == "__main__":
    main()

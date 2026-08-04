"""Battery 8: are pairwise statistics blind to the coalescent regime?

The claim under test is that after normalisation EVERY Lambda-coalescent has the
same pairwise coalescence time distribution, so heterozygosity, pi, pairwise
F_ST and everything built on them cannot see the reproductive regime -- while the
site-frequency spectrum at n >= 3 can, because it involves branch lengths
subtending three or more leaves.

This matters twice over.

First, if it holds it is a blindness instance of exactly the kind
`Calibrator.BlindnessRegistry` collects: a probe that returns the same number on
two objects certifies neither, and here the probe is the most-used summary
statistic in the field.

Second, and more immediately, it is a statement about THIS harness. Every F_ST
number produced in batteries 1-7 is built from pairwise coalescence times --
`1 - E[T_within]/E[T_between]` is a ratio of pairwise quantities. If the claim is
true then no amount of replication makes that oracle sensitive to the
reproductive regime, and every "VALIDATED" it issued is valid only within
Kingman. An instrument that cannot report its own blind spot will eventually
report someone else's answer as its own.

Design: the same normalisation applied to Kingman, to Beta(2-alpha, alpha) at
three alphas, and to a Dirac coalescent. Pairwise times are compared after
dividing by their own mean, which is the normalisation the claim is stated
under. The branch-mode SFS at n = 10 is the discriminating comparison.
"""
import json
import math

import numpy as np


def models():
    import msprime
    return [
        ("Kingman", msprime.StandardCoalescent()),
        ("Beta alpha=1.9", msprime.BetaCoalescent(alpha=1.9)),
        ("Beta alpha=1.5", msprime.BetaCoalescent(alpha=1.5)),
        ("Beta alpha=1.1", msprime.BetaCoalescent(alpha=1.1)),
        ("Dirac psi=0.3", msprime.DiracCoalescent(psi=0.3, c=1.0)),
    ]


def pairwise_times(model, reps=20000, Ne=1000, seed=1):
    """TMRCA of a single pair, one independent genealogy per replicate."""
    import msprime
    out = []
    for ts in msprime.sim_ancestry(
            samples=1, ploidy=2, population_size=Ne, model=model,
            num_replicates=reps, random_seed=seed):
        out.append(ts.first().time(ts.first().root))
    return np.array(out)


def branch_sfs(model, n_dip=5, reps=4000, Ne=1000, seed=1):
    """Expected SFS from branch lengths: no mutations, so no Poisson noise."""
    import msprime
    acc = None
    for ts in msprime.sim_ancestry(
            samples=n_dip, ploidy=2, population_size=Ne, model=model,
            num_replicates=reps, random_seed=seed):
        s = ts.allele_frequency_spectrum(mode="branch", polarised=True,
                                         span_normalise=False)
        acc = s if acc is None else acc + s
    sfs = acc[1:-1]
    return sfs / sfs.sum()


def main():
    out = {}
    print("=" * 74)
    print("PAIRWISE COALESCENCE TIMES, each normalised by its own mean")
    print("=" * 74)
    print("  %-18s %10s %10s %10s %10s"
          % ("model", "mean(raw)", "CV", "skew", "P(T>2mean)"))
    print("  (an exponential has CV 1.000, skew 2.000, P = 0.1353)")
    pair = {}
    for name, mdl in models():
        t = pairwise_times(mdl, seed=11)
        z = t / t.mean()
        cv = float(z.std())
        skew = float(((z - 1) ** 3).mean() / z.std() ** 3)
        tail = float((z > 2).mean())
        pair[name] = dict(mean=float(t.mean()), cv=cv, skew=skew, tail=tail,
                          sem_cv=cv / math.sqrt(2 * len(z)),
                          sem_tail=math.sqrt(tail * (1 - tail) / len(z)))
        print("  %-18s %10.1f %10.4f %10.4f %10.4f"
              % (name, t.mean(), cv, skew, tail))
    ref = pair["Kingman"]
    print("\n  deviation from Kingman, in sems of the two compared:")
    for name, d in pair.items():
        if name == "Kingman":
            continue
        z_cv = abs(d["cv"] - ref["cv"]) / math.sqrt(d["sem_cv"] ** 2 + ref["sem_cv"] ** 2)
        z_tl = abs(d["tail"] - ref["tail"]) / math.sqrt(
            d["sem_tail"] ** 2 + ref["sem_tail"] ** 2)
        print("    %-18s CV %6.2f sems    tail %6.2f sems" % (name, z_cv, z_tl))
    out["pairwise"] = pair

    print("\n" + "=" * 74)
    print("NORMALISED BRANCH-MODE SFS at n = 10, the same models")
    print("=" * 74)
    sfs = {}
    for name, mdl in models():
        s = branch_sfs(mdl, seed=21)
        sfs[name] = [float(x) for x in s]
        print("  %-18s %s" % (name, " ".join("%.4f" % x for x in s)))
    ref_s = np.array(sfs["Kingman"])
    print("\n  total variation distance from Kingman:")
    for name, s in sfs.items():
        if name == "Kingman":
            continue
        tv = 0.5 * float(np.abs(np.array(s) - ref_s).sum())
        print("    %-18s TV = %.4f" % (name, tv))
    out["sfs"] = sfs

    json.dump(out, open("battery_blind_results.json", "w"), indent=1)
    print("\nIf the pairwise rows agree and the SFS rows do not, the pairwise")
    print("probe is blind to a distinction the SFS resolves, and every F_ST in")
    print("this harness inherits that blindness.")


if __name__ == "__main__":
    main()

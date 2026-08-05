"""Battery 31b: the same composition, with theta*tau actually varied.

Battery 31 held `theta * tau = 1` across every cell so that `Ne` cancelling
would be visible, and the verdict gate correctly called NO POWER on it: a
prediction that does not move cannot reject a wrong functional form, whatever
else the design shows. This run varies `theta * tau` over a factor of eight
WHILE varying `Ne` over a factor of eight, so the cancellation and the
functional form are both under test at once.
"""
import json, math
import numpy as np
from battery_core import RESULTS, record

def main():
    rng = np.random.default_rng(26301)
    cells_two, cells_one = [], []
    for Ne, mu, t in ((250, 1e-3, 125), (500, 1e-3, 250), (2000, 2.5e-4, 1000),
                      (500, 2e-3, 500), (1000, 5e-4, 2000), (250, 4e-3, 250)):
        theta, tau = 4 * Ne * mu, t / (2 * Ne)
        reps = 400000
        hits = rng.binomial(2 * t, mu, size=reps)
        surv = float((hits == 0).mean())
        sem = math.sqrt(max(surv * (1 - surv), 1e-12) / reps)
        lab = ("Ne=%d mu=%.1e t=%d (theta*tau=%.2f)" % (Ne, mu, t, theta * tau))
        cells_two.append(dict(design=lab, lean=math.exp(-theta * tau),
                              truth=surv, sem=sem))
        cells_one.append(dict(design=lab + " [one-lineage]",
                              lean=math.exp(-theta * tau / 2), truth=surv,
                              sem=sem))
        print("  %-44s pred %.5f  one-lin %.5f  measured %.5f"
              % (lab, math.exp(-theta*tau), math.exp(-theta*tau/2), surv))
    reg = ("theta*tau varied over a factor of eight while Ne is varied over a "
           "factor of eight, so the functional form and the cancellation of Ne "
           "are tested together; 400000 replicate lineage pairs per cell")
    record("mutationSharedRetentionAt", "PortabilityDrift.lean",
           "exp(-theta * tauAt t)", cells_two, regime=reg)
    record("mutationSharedRetentionAt [one-lineage reading, competing]",
           "PortabilityDrift.lean", "exp(-theta * tau / 2)", cells_one,
           regime=reg)
    record("mutationLDErosion", "DGP.lean", "exp(-theta * tau)",
           list(cells_two), regime=reg)
    record("tauAt", "PortabilityDrift.lean", "t / (2 * Ne)", list(cells_two),
           regime=reg + "; tauAt is tested through this composition rather "
                        "than as an isolated ratio")
    json.dump(RESULTS, open("battery_bulk16b_results.json", "w"), indent=1,
              default=str)
    print("\n================ SUMMARY ================")
    for r in RESULTS:
        w = r.get("worst", {})
        print("%-20s %-56s worst %9.2f sems, %6.2f%% rel"
              % (r["verdict"], r["name"], w.get("sems_off", float("nan")),
                 100 * w.get("rel_err", float("nan"))))

if __name__ == "__main__":
    main()

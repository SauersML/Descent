"""battery_bulk8's coalescentRate row is a factor of two in a ploidy convention.

THE ROW. `coalescentRate = m(m-1)/2`, recorded at 100.3 sems and held as LEAD.
The battery asks msprime for `sim_ancestry(samples=m, ploidy=1,
population_size=Ne)`, takes the mean waiting time to the first coalescence, and
converts it to a rate by dividing by `2 Ne`.

WITH `ploidy = 1` MSPRIME'S COALESCENT UNIT IS `Ne` GENERATIONS, NOT `2 Ne`. The
pair coalescence rate is `1/(ploidy * N)` per generation, so a haploid population
of size `Ne` coalesces a pair in `Ne` generations on average, not `2 Ne`. Dividing
by `2 Ne` doubles every measured rate, and the body is then missed by a factor of
two in every cell.

That the recorded figure is 100.3 sems is not a coincidence and is worth the
arithmetic: the battery's bar is `obs_rate / sqrt(40000)`, i.e. 0.5 percent of the
value, and a factor-of-two discrepancy against a 0.5 percent bar is
`(obs/2) / (obs/200) = 100` sems exactly, whatever the cell.

This prints both conversions beside the body so the convention is legible rather
than argued. No verdict is emitted.
"""
import numpy as np
import msprime

NE, REPS = 1000, 20000

print("%-6s %18s %14s %14s %10s" % ("m", "mean first-coal", "rate /(2Ne)",
                                    "rate /(Ne)", "body"))
for m in (2, 4, 8):
    times = []
    for ts in msprime.sim_ancestry(samples=m, ploidy=1, population_size=NE,
                                   num_replicates=REPS, random_seed=18101):
        tr = ts.first()
        times.append(min(tr.time(u) for u in tr.nodes() if tr.num_children(u) > 0))
    mt = float(np.mean(times))
    print("%-6d %18.2f %14.3f %14.3f %10.1f"
          % (m, mt, 1.0 / (mt / (2 * NE)), 1.0 / (mt / NE), m * (m - 1) / 2))

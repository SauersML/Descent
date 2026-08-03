#!/usr/bin/env python3
"""Is the moment-body entropy lower bound limited by the BODY or by my
perturbation family?

Runs the validated zonotope/volumetric instrument at alpha = 1.5 with families
of increasing richness (more shells per scale, more scales).  If the fitted
lower-bound exponent keeps climbing with family size, the instrument has not
converged and the moment-body exponent is unresolved; if it plateaus, the
plateau is a genuine numerical lower bound on the exponent.
"""

import json
import math

import numpy as np
import mpmath as mp

import moment_body_entropy as M


def one(alpha, n_scales, per_scale, dps, epss):
    mp.mp.dps = dps
    scales = [0.4 * 0.5 ** i for i in range(n_scales)]
    atoms, masses, ratio = M.build_shell_family(1.0, alpha, scales, per_scale)
    G = M.exact_gram(atoms, masses)
    ld = M.pivoted_cholesky_logdets(G, rmax=len(atoms))
    rows = M.volumetric_bound(ld, epss)
    rows = [r for r in rows if r["logN_lower"] > 0]
    f = M.loglog_fit([1.0 / r["eps"] for r in rows], [r["logN_lower"] for r in rows])
    return dict(alpha=alpha, n_scales=n_scales, per_scale=per_scale,
                n_directions=len(atoms), dps=dps,
                max_r_certified=ld[-1][0] if ld else 0,
                r_selected=[r["r"] for r in rows],
                slope=f["slope"], stderr=f["stderr"],
                max_abs_log_resid=f["max_abs_resid"],
                rows=rows)


if __name__ == "__main__":
    epss = np.geomspace(1e-2, 1e-14, 14)
    out = []
    for (ns, ps) in ((25, 6), (25, 12), (25, 24), (40, 12), (15, 12), (40, 15)):
        out.append(one(1.5, ns, ps, 300, epss))
        print(json.dumps(out[-1], default=str), flush=True)
    print("SUMMARY", json.dumps(
        [(o["n_directions"], round(o["slope"], 4), round(o["stderr"], 4),
          max(o["r_selected"])) for o in out]))

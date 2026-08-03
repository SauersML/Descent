#!/usr/bin/env python3
"""Depth scan: does the certified moment-body bound improve as the shell family
reaches closer to the boundary (more geometric scales)?  Fixed shells per scale,
increasing scale depth.  Reports both a power-law fit and a quadratic-in-log fit,
since the whole question is which functional form the bound takes."""
import json
import math
import numpy as np
import mpmath as mp
import moment_body_entropy as M

epss = np.geomspace(1e-2, 1e-16, 16)
out = []
for ns in (15, 25, 40, 55):
    mp.mp.dps = 400
    scales = [0.4 * 0.5 ** i for i in range(ns)]
    atoms, masses, ratio = M.build_shell_family(1.0, 1.5, scales, 8)
    G = M.exact_gram(atoms, masses)
    ld = M.pivoted_cholesky_logdets(G, rmax=len(atoms))
    rows = [r for r in M.volumetric_bound(ld, epss) if r["logN_lower"] > 0]
    L = np.array([math.log(1.0 / r["eps"]) for r in rows])
    y = np.array([r["logN_lower"] for r in rows])
    f = M.loglog_fit(1.0 / np.array([r["eps"] for r in rows]), y)
    A = np.column_stack([np.ones(len(L)), L, L ** 2])
    b, *_ = np.linalg.lstsq(A, y, rcond=None)
    rec = dict(n_scales=ns, n_directions=len(atoms), finest_shell=scales[-1],
               max_r_certified=ld[-1][0], max_r_selected=max(r["r"] for r in rows),
               power_slope=f["slope"], power_stderr=f["stderr"],
               power_max_log_resid=f["max_abs_resid"],
               quad_in_log_coefs=[float(x) for x in b],
               quad_max_resid_over_max=float(np.max(np.abs(y - A @ b)) / np.max(y)),
               rows=rows)
    out.append(rec)
    print(json.dumps(rec, default=str), flush=True)
print("SUMMARY", json.dumps([(o["n_scales"], o["n_directions"],
                             round(o["power_slope"], 4), o["max_r_selected"],
                             round(o["quad_max_resid_over_max"], 5)) for o in out]))

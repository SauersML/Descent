#!/usr/bin/env python3.12
"""Batch 2: sharper sample-overlap arms and a realistic M/N ratio.

M is raised to 3000 so the LD-score regression has enough SNPs to be precise,
and rho_e is raised to 0.8 so the overlap bias the LDSC intercept exists to
absorb is large enough to read off cleanly.
"""
import json
import sys
from multiprocessing import Pool
from ldsc_sim import run_cfg

B2 = dict(M=3000, B=0, ld_r=0.7, N1=750, N2=750, Nover=0,
          h2_1=0.5, h2_2=0.5, rho_g=0.6, rho_e=0.0, reps=24, seed=1)


def cfgs():
    out = []
    s = 0

    def add(name, **kw):
        nonlocal s
        s += 1
        c = dict(B2); c.update(kw); c["name"] = name; c["seed"] = 500 + s
        out.append(c)

    # realistic GWAS proportion: M/N = 10
    add("B2_ATT_MoverN_10", N1=300, N2=300, reps=24)
    # overlap ladder at true rho_g = 0, strong environmental correlation
    add("B2_OVL_rg0_frac0", rho_g=0.0, rho_e=0.8, Nover=0)
    add("B2_OVL_rg0_frac0.5", rho_g=0.0, rho_e=0.8, Nover=375)
    add("B2_OVL_rg0_frac1", rho_g=0.0, rho_e=0.8, Nover=750)
    # NEGATIVE CONTROL for the overlap harness: full overlap but rho_e = 0, so
    # there is nothing for the intercept to absorb and no bias may appear.
    add("B2_OVL_rg0_frac1_re0_NEGCTRL", rho_g=0.0, rho_e=0.0, Nover=750)
    # overlap on top of a real signal
    add("B2_OVL_rg0.3_frac1_re0.8", rho_g=0.3, rho_e=0.8, Nover=750)
    return out


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    with Pool(n) as p:
        print(json.dumps(p.map(run_cfg, cfgs()), indent=1))

#!/usr/bin/env python3
"""Analyse the Whittle long-memory simulation against the LongMemoryGeometry claims."""

import json
import sys

import numpy as np

# Whittle information per observation, analytic.
#   AR(1) in (rho, s2):  I_rho = 1/(1-rho^2),  I_s2 = 1/(2 s2^2),  cross term 0.
#   mean of an AR(1):    I_mu  = (1-rho)^2 / s2      (from Var(xbar) = 2 pi f(0)/n)
#   ARFIMA(0,d,0):       I_d   = pi^2/6
I_ar1_rho = lambda rho: 1.0 / (1.0 - rho ** 2)
I_s2 = lambda s2: 1.0 / (2.0 * s2 ** 2)
I_mu = lambda rho, s2: (1.0 - rho) ** 2 / s2
I_arfima_d = np.pi ** 2 / 6.0


def main():
    d = json.load(open(sys.argv[1]))
    rows = d["rows"]
    nrep = d["nrep"]
    out = {"nrep": nrep}

    print(f"=== CONTROLS (nrep={nrep}) ===")
    ctrl = []
    for r in rows:
        if r["arm"] == "iid":
            s2 = r["params"]["s"] ** 2
            pred = 2 * s2 ** 2 / r["n"]
            obs = r["var"][0]
            ctrl.append(dict(arm="iid", n=r["n"], obs=obs, pred=pred, ratio=obs / pred,
                             se=r["var_se"][0]))
        if r["arm"] == "ar1_short":
            rho = r["params"]["rho"]
            pred = (1 - rho ** 2) / r["n"]
            obs = r["var"][0]
            ctrl.append(dict(arm="ar1_short(rho=0.5)", n=r["n"], obs=obs, pred=pred,
                             ratio=obs / pred, se=r["var_se"][0]))
        if r["arm"] == "arfima":
            pred = 1.0 / (I_arfima_d * r["n"])
            obs = r["var"][0]
            ctrl.append(dict(arm=f"arfima(d={r['params']['d']})", n=r["n"], obs=obs,
                             pred=pred, ratio=obs / pred, se=r["var_se"][0]))
    print(f"{'arm':<22}{'n':>7}{'Var_obs':>13}{'Var_theory':>13}{'ratio':>9}{'+-':>9}")
    for c in ctrl:
        print(f"{c['arm']:<22}{c['n']:>7}{c['obs']:>13.4e}{c['pred']:>13.4e}"
              f"{c['ratio']:>9.4f}{c['se']/c['pred']:>9.4f}")
    out["controls"] = ctrl

    print("\n=== MAIN ARM: near-unit-root AR(1), rho = 1 - delta ===")
    print(f"{'delta':>8}{'eps(s)':>8}{'n':>8}{'Var(delta_hat)':>16}{'+-rel':>8}"
          f"{'n*Var/delta':>13}{'claim 3d^3/eps^2':>18}{'obs/claim':>11}")
    main_rows = []
    for r in sorted([r for r in rows if r["arm"] == "ar1_near"],
                    key=lambda r: (-(1 - r["params"]["rho"]), r["n"], r["params"]["s"])):
        delta = 1.0 - r["params"]["rho"]
        eps = r["params"]["s"]
        n = r["n"]
        V = r["delta_hat_var"]
        claim = 3 * delta ** 3 / (n * eps ** 2)
        rec = dict(delta=delta, eps=eps, n=n, V=V, V_se=r["var_se"][0],
                   nV_over_delta=n * V / delta, claim=claim, obs_over_claim=V / claim,
                   theory=delta * (2 - delta) / n,
                   log_delta_var=r["log_delta_var"],
                   frac_nonpos=r["frac_nonpositive_delta"])
        main_rows.append(rec)
        print(f"{delta:>8.3f}{eps:>8.2f}{n:>8}{V:>16.4e}{r['var_se'][0]/V:>8.3f}"
              f"{n*V/delta:>13.4f}{claim:>18.4e}{V/claim:>11.4f}")
    out["ar1_near"] = main_rows

    # scaling exponents
    print("\n-- scaling of Var(delta_hat) --")
    for n in sorted({r["n"] for r in main_rows}):
        for eps in sorted({r["eps"] for r in main_rows}):
            sel = [r for r in main_rows if r["n"] == n and r["eps"] == eps]
            sel = [r for r in sel if r["frac_nonpos"] < 0.02]
            if len(sel) < 3:
                continue
            x = np.log([r["delta"] for r in sel])
            y = np.log([r["V"] for r in sel])
            p, _ = np.polyfit(x, y, 1)
            print(f"  n={n:<6} eps={eps:<5} Var ~ delta^{p:+.3f}   "
                  f"(theory +1, compendium claim +3)")
    # eps dependence at fixed delta, n
    print("\n-- dependence on the amplitude eps (claim: Var ~ 1/eps^2) --")
    for n in sorted({r["n"] for r in main_rows}):
        for delta in sorted({r["delta"] for r in main_rows}):
            a = [r for r in main_rows if r["n"] == n and r["delta"] == delta and r["eps"] == 1.0]
            b = [r for r in main_rows if r["n"] == n and r["delta"] == delta and r["eps"] == 2.5]
            if a and b:
                print(f"  n={n:<6} delta={delta:<6} Var(eps=2.5)/Var(eps=1.0) = "
                      f"{b[0]['V']/a[0]['V']:.4f}   (claim 1/6.25 = 0.16, "
                      f"parameter-invariance says 1.00)")

    print("\n=== TRANSPORTED FLOOR  (1/2) * metric * variance, times n ===")
    print("  claimed metric eps^2/delta^3;  true Whittle metric I_delta = 1/(delta(2-delta))")
    print(f"{'delta':>8}{'eps':>6}{'n':>8}{'n*(1/2)g_claim*V':>20}{'n*(1/2)I_true*V':>19}")
    for r in main_rows:
        g_claim = r["eps"] ** 2 / r["delta"] ** 3
        I_true = 1.0 / (r["delta"] * (2 - r["delta"]))
        print(f"{r['delta']:>8.3f}{r['eps']:>6.2f}{r['n']:>8}"
              f"{r['n']*0.5*g_claim*r['V']:>20.4f}{r['n']*0.5*I_true*r['V']:>19.4f}")
        r["floor_claimed_metric"] = r["n"] * 0.5 * g_claim * r["V"]
        r["floor_true_metric"] = r["n"] * 0.5 * I_true * r["V"]
    print("  (a flat column at 1.500 would confirm 3/(2n); a flat column at 0.500 says")
    print("   the floor is 1/(2n) for one parameter, i.e. the constant is the dimension)")

    print("\n=== DOES THE VARIANCE 'BLOW UP' AS MEMORY LENGTHENS? ===")
    print(f"{'delta':>8}{'n':>8}{'Var(delta_hat)':>16}{'Var(log delta_hat)':>20}"
          f"{'rel.sd':>10}")
    for r in main_rows:
        if r["eps"] == 1.0:
            print(f"{r['delta']:>8.3f}{r['n']:>8}{r['V']:>16.4e}"
                  f"{r['log_delta_var']:>20.4e}{np.sqrt(r['V'])/r['delta']:>10.3f}")

    print("\n=== 3-PARAMETER ARM: is the constant 3 the parameter count? ===")
    print("  transported loss n*(1/2)*tr(Cov * I_perobs); efficiency => p/2 = 1.500")
    tp = []
    for r in rows:
        if r["arm"] != "ar1_3par":
            continue
        rho, s, mu = r["params"]["rho"], r["params"]["s"], r["params"]["mu"]
        s2 = s ** 2
        C = np.array(r["cov"])
        I = np.diag([I_ar1_rho(rho), I_s2(s2), I_mu(rho, s2)])
        val = r["n"] * 0.5 * float(np.trace(C @ I))
        print(f"  delta={1-rho:<7.3f} n={r['n']:<7} n*(1/2)tr(Cov*I) = {val:.4f}")
        tp.append(dict(delta=1 - rho, n=r["n"], value=val))
    out["three_param"] = tp

    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()

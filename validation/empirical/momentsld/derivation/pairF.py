"""pairF.py -- EXACT pairwise coalescence times and Hudson F_ST for the two gnomon
demographies, straight from the generator's own demography constructors.

PREDICTION SIDE ONLY: this reads gen_real_pt.py's dem_serial1d / dem_grid2d (demography
CODE, permitted) and integrates the structured PAIR coalescent exactly through the real
event schedule with argcore's validated machinery. No simulation output is touched.

Reports T2(i,j) for every deme pair and the Hudson F_ST = 1 - T2_within_mean / T2(i,j),
plus, for the two-deme island reduction, the M that reproduces each F_ST
(F_ST = 1/(2M+1)  =>  M_eff = (1/F - 1)/2).
"""
import sys
import numpy as np

sys.path.insert(0, "/projects/standard/hsiehph/sauer354/theory-out")
sys.path.insert(0, "/projects/standard/hsiehph/sauer354/gnomon/sims/ancestry_calibration")
import argcore as ac
import msprime  # noqa: F401  (gen_real_pt needs it)


def dem_serial1d(D=10, N=3000, Nanc=10000, m=1e-3, split_step=400, T0=200):
    d = msprime.Demography()
    for k in range(D):
        d.add_population(name=f"d{k}", initial_size=N)
    d.add_population(name="ANC", initial_size=Nanc)
    for i in range(D - 1):
        d.set_migration_rate(f"d{i}", f"d{i+1}", m)
        d.set_migration_rate(f"d{i+1}", f"d{i}", m)
    for k in range(D - 1, 0, -1):
        t = T0 + (D - 1 - k) * split_step
        d.add_migration_rate_change(time=t, rate=0, source=f"d{k-1}", dest=f"d{k}")
        d.add_migration_rate_change(time=t, rate=0, source=f"d{k}", dest=f"d{k-1}")
        d.add_mass_migration(time=t + 1, source=f"d{k}", dest=f"d{k-1}", proportion=1.0)
    tanc = T0 + (D - 1) * split_step + 500
    d.add_population_split(time=tanc, derived=["d0"], ancestral="ANC")
    d.sort_events()
    return d, D


def dem_grid2d(side=6, N=3000, Nanc=10000, m=3e-4):
    d = msprime.Demography()
    nm = lambda r, c: f"d_{r}_{c}"
    for r in range(side):
        for c in range(side):
            d.add_population(name=nm(r, c), initial_size=N)
    d.add_population(name="ANC", initial_size=Nanc)
    for r in range(side):
        for c in range(side):
            for dr, dc in [(1, 0), (0, 1)]:
                r2, c2 = r + dr, c + dc
                if r2 < side and c2 < side:
                    d.set_migration_rate(nm(r, c), nm(r2, c2), m)
                    d.set_migration_rate(nm(r2, c2), nm(r, c), m)
    d.add_population_split(time=4 * N,
                           derived=[nm(r, c) for r in range(side) for c in range(side)],
                           ancestral="ANC")
    d.sort_events()
    return d, side * side


def t2_exact(demo, h=1.0):
    """Integrate the structured pair coalescent present-ward through the real schedule.
    Terminal condition at t_root: everything in ANC, T2 = 2*Nanc. Heun, 1-generation step."""
    pops, n, ix, Nsz, segments, relabels, t_root = ac.parse(demo)
    anc = ix["ANC"]
    T2 = np.full(n * n, 2.0 * Nsz[anc])
    times = sorted(relabels.keys(), reverse=True)
    for (t0, t1, Mseg) in reversed(segments):
        for tau in times:
            if t0 < tau <= t1:
                perm = np.arange(n)
                for s, dd in relabels[tau].items():
                    perm[s] = dd
                T2 = T2[(perm[:, None] * n + perm[None, :]).ravel()]
        Q2 = ac.pair_matrix(Mseg, Nsz, n)
        for _ in range(int(round((t1 - t0) / h))):
            k1 = 1.0 + Q2 @ T2
            k2 = 1.0 + Q2 @ (T2 + h * k1)
            T2 = T2 + 0.5 * h * (k1 + k2)
    for tau in times:
        if tau == 0:
            perm = np.arange(n)
            for s, dd in relabels[tau].items():
                perm[s] = dd
            T2 = T2[(perm[:, None] * n + perm[None, :]).ravel()]
    return T2.reshape(n, n)


def report(name, demo, nd, coords, distfn):
    T2 = t2_exact(demo)[:nd, :nd]
    print("\n" + "=" * 78)
    print("%s : %d demes, T2 in generations" % (name, nd))
    print("  T2(within) min/mean/max = %.1f / %.1f / %.1f"
          % (np.diag(T2).min(), np.diag(T2).mean(), np.diag(T2).max()))
    # Hudson F_ST for a pair (i,j): 1 - (T2_ii + T2_jj)/2 / T2_ij
    F = np.zeros((nd, nd))
    for i in range(nd):
        for j in range(nd):
            if i != j:
                F[i, j] = 1.0 - 0.5 * (T2[i, i] + T2[j, j]) / T2[i, j]
    return T2, F


print("EXACT PAIRWISE COALESCENT (prediction side; no simulation output touched)")

# ---------------------------------------------------------------- serial1d
demo, D = dem_serial1d()
T2s, Fs = report("serial1d", demo, D, None, None)
print("\n  serial1d F_ST(Hudson) BY PAIR (rows = train deme t, cols = other deme k):")
print("      " + "".join("%8d" % k for k in range(D)))
for t in range(D):
    print("  t=%d " % t + "".join("%8.4f" % Fs[t, k] for k in range(D)))
INHERITED = [0.0349, 0.0630, 0.0864, 0.1069, 0.1254, 0.1428, 0.1597, 0.1765, 0.1927]
print("\n  CHECK OF THE INHERITED PER-EDGE F LIST (metadata #43), which can only be a")
print("  function of d if the train deme is d0 -- comparing against row t=0:")
print("      d   inherited   F(0,d) here   ratio")
for d in range(1, D):
    print("      %d   %9.4f   %11.4f   %6.3f"
          % (d, INHERITED[d - 1], Fs[0, d], Fs[0, d] / INHERITED[d - 1]))
print("\n  AND THE SAME d FROM A MID-CHAIN TRAIN DEME (why d is not a sufficient label):")
print("      d      t=0      t=4 (k=t-d)   t=4 (k=t+d)   t=9")
for d in range(1, 6):
    lo = Fs[4, 4 - d] if 4 - d >= 0 else float("nan")
    hi = Fs[4, 4 + d] if 4 + d < D else float("nan")
    print("      %d   %7.4f   %11.4f   %11.4f   %7.4f"
          % (d, Fs[0, d], lo, hi, Fs[9, 9 - d]))

# ---------------------------------------------------------------- grid2d
demo, nd = dem_grid2d()
T2g, Fg = report("grid2d", demo, nd, None, None)
side = 6
rc = np.array([(r, c) for r in range(side) for c in range(side)])
print("\n  grid2d F_ST(Hudson) BY MANHATTAN DISTANCE, over ALL 36 possible train demes")
print("  (this is the exact spread the per-distance rows average over):")
print("      d     n_pairs    min F      mean F     max F   |  M_eff=(1/F-1)/2 at mean")
for d in range(1, 11):
    vals = []
    for i in range(nd):
        for j in range(nd):
            if i != j and abs(rc[i][0] - rc[j][0]) + abs(rc[i][1] - rc[j][1]) == d:
                vals.append(Fg[i, j])
    if not vals:
        continue
    v = np.array(vals)
    print("      %2d   %7d   %8.5f   %8.5f   %8.5f  |  %8.3f"
          % (d, len(v), v.min(), v.mean(), v.max(), (1.0 / v.mean() - 1.0) / 2.0))
print("\n  grid2d corner-to-corner F_ST = %.5f  (generator comment targets 0.20-0.25)"
      % Fg[0, nd - 1])
print("  grid2d nearest-neighbour F_ST = %.5f" % Fg[0, 1])
np.save("/projects/standard/hsiehph/sauer354/theory-out/pairF_serial1d.npy", Fs)
np.save("/projects/standard/hsiehph/sauer354/theory-out/pairF_grid2d.npy", Fg)
np.save("/projects/standard/hsiehph/sauer354/theory-out/pairT2_serial1d.npy", T2s)
np.save("/projects/standard/hsiehph/sauer354/theory-out/pairT2_grid2d.npy", T2g)
print("\nsaved pairF_*.npy / pairT2_*.npy to theory-out/")

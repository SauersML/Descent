"""Cell I: the exponential LD-decay chart, WITH the positive control the earlier
run lacked.

  OpenQuestions.ldTaggingDecay lam d = exp(-lam*d)

The corpus already records a LEAD against this shape, carried by the sibling
`PortabilityDrift.ldCorrelationDecay`: fitted against simulated r^2 the
exponential misses at both ends while the hyperbolic stays close.  That run
"carried no valid positive control, which is why it is a lead and not a
falsification".  This cell supplies exactly that control and nothing else new.

THE CONTROL.  A shape comparison that prefers hyperbolic on real data means
nothing unless the same fitter prefers EXPONENTIAL on data that is genuinely
exponential.  So every design is run twice: once on msprime r^2, and once on a
synthetic curve drawn from a true exponential with matched noise.  If the fitter
does not pick the exponential on the synthetic arm, the instrument is broken and
the real arm's verdict is void -- and this script exits nonzero.

Both shapes carry a free amplitude and a free rate, so neither is handicapped,
and the discrimination is the SHAPE, which no estimator convention moves: the
same binned r^2 values feed both fits, so any upward bias in r^2 is common.

Guard PGSEL_I1.
"""
import json, math, sys
import numpy as np
import msprime

GUARD = "PGSEL_I1"


def r2_curve(Ne, seqlen, rrate, mu, nhap, bins, seed, maf=0.05):
    ts = msprime.sim_ancestry(samples=nhap // 2, ploidy=2, population_size=Ne,
                              sequence_length=seqlen, recombination_rate=rrate,
                              random_seed=seed)
    ts = msprime.sim_mutations(ts, rate=mu, random_seed=seed + 1)
    G = ts.genotype_matrix()
    pos = ts.tables.sites.position
    p = G.mean(axis=1)
    keep = (p > maf) & (p < 1 - maf)
    G, pos = G[keep], pos[keep]
    if len(pos) > 900:                      # cap the pair count
        idx = np.linspace(0, len(pos) - 1, 900).astype(int)
        G, pos = G[idx], pos[idx]
    Gc = G - G.mean(axis=1, keepdims=True)
    sd = Gc.std(axis=1)
    ok = sd > 0
    Gc, pos, sd = Gc[ok], pos[ok], sd[ok]
    C = (Gc @ Gc.T) / Gc.shape[1]
    R2 = (C / np.outer(sd, sd)) ** 2
    d = np.abs(pos[:, None] - pos[None, :]) * rrate     # genetic distance
    iu = np.triu_indices(len(pos), 1)
    dv, rv = d[iu], R2[iu]
    out = []
    for lo, hi in zip(bins[:-1], bins[1:]):
        m = (dv >= lo) & (dv < hi)
        if m.sum() > 50:
            out.append((0.5 * (lo + hi), rv[m].mean(),
                        rv[m].std(ddof=1) / math.sqrt(m.sum())))
    return np.array(out)


def fit_shapes(x, y, w):
    """Least squares for A*exp(-lam*x) and A/(1+b*x), each with two free
    parameters.  Returns (sse_exp, sse_hyp, params)."""
    def sse(f, grid):
        best = (np.inf, None)
        for g in grid:
            base = f(x, g)
            A = (w * y * base).sum() / (w * base * base).sum()
            s = (w * (y - A * base) ** 2).sum()
            if s < best[0]:
                best = (s, (A, g))
        return best
    grid = np.exp(np.linspace(math.log(1e-1), math.log(1e5), 4000))
    se, pe = sse(lambda x, g: np.exp(-g * x), grid)
    sh, ph = sse(lambda x, g: 1.0 / (1.0 + g * x), grid)
    return se, sh, pe, ph


def one_design(Ne, seqlen, rrate, seed):
    bins = np.concatenate([[0], np.exp(np.linspace(math.log(2e-6),
                                                   math.log(2e-3), 14))])
    cur = r2_curve(Ne, seqlen, rrate, 1e-8, 300, bins, seed)
    x, y, s = cur[:, 0], cur[:, 1], cur[:, 2]
    w = 1.0 / s ** 2
    se, sh, pe, ph = fit_shapes(x, y, w)
    # --- POSITIVE CONTROL: the same fitter on a truly exponential curve, with
    # the same x grid and the same per-point noise scale.
    rng = np.random.default_rng(seed)
    lam_true = 1.0 / (x.mean())
    ytrue = y[0] * np.exp(-lam_true * x)
    yctl = ytrue + rng.normal(0, s)
    cse, csh, cpe, cph = fit_shapes(x, yctl, w)
    return dict(
        Ne=Ne, seqlen=seqlen, rrate=rrate, npoints=len(x),
        x=list(x), y=list(y), sem=list(s),
        sse_exponential=se, sse_hyperbolic=sh,
        exp_params=dict(A=pe[0], lam=pe[1]),
        hyp_params=dict(A=ph[0], b=ph[1]),
        chi2_per_point_exponential=se / len(x),
        chi2_per_point_hyperbolic=sh / len(x),
        worst_exponential_sems=float(np.max(np.abs(y - pe[0] * np.exp(-pe[1] * x)) / s)),
        worst_hyperbolic_sems=float(np.max(np.abs(y - ph[0] / (1 + ph[1] * x)) / s)),
        positive_control=dict(
            description="same fitter on a TRUE exponential with matched noise; "
                        "must prefer the exponential or the real arm is void",
            sse_exponential=cse, sse_hyperbolic=csh,
            prefers_exponential=bool(cse < csh)))


if __name__ == "__main__":
    rows = [one_design(2000, 4e6, 1e-8, 900),
            one_design(5000, 2e6, 1e-8, 1300)]
    print("FRESHNESS=OK", GUARD)
    print(json.dumps(dict(cell="I", target="ldTaggingDecay", guard=GUARD,
                          argument_source="msprime r^2 against genetic distance; both "
                                          "shapes fitted with free amplitude AND free rate "
                                          "on the SAME binned values, so the estimator's "
                                          "bias is common and the discrimination is shape",
                          detail=rows), indent=1, default=float))
    if not all(r["positive_control"]["prefers_exponential"] for r in rows):
        print("POSITIVE CONTROL FAILED -- instrument broken, real arm is void",
              file=sys.stderr)
        sys.exit(1)

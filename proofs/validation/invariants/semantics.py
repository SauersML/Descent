"""What a definition's NAME and DOCSTRING commit it to.

Two things are inferred here and nowhere else:

  `required_range(d)`  the interval the quantity is mathematically forced into
                       by what it is called.  A probability cannot exceed 1; a
                       correlation cannot exceed 1 in absolute value; a
                       variance cannot be negative.  Violating this is not a
                       modelling disagreement, it is an error.

  `admissible_box(d)`  the region of input space the definition is claimed
                       over.  Priority order, and the order matters:
                         1. hypotheses of the Lean theorems that mention it,
                         2. the meaning of the parameter names,
                         3. nothing -- in which case the definition is
                            UNGUARDED and that is the finding.

We never widen a range to make a definition pass, and we never invent a
hypothesis the author did not write.  If (1) is empty the definition carries no
stated domain restriction at all, and `box_source` records that.
"""
from __future__ import annotations

import math
import re

INF = math.inf

# --------------------------------------------------------------------------
# required ranges.  (lo, hi, why).  Matched against the definition name first,
# then the docstring.  Order matters: the first hit wins, so specific patterns
# precede general ones.

UNIT = (0.0, 1.0)
CORR = (-1.0, 1.0)
NONNEG = (0.0, INF)
POS = (1e-300, INF)

NAME_RANGES = [
    # -- correlations: [-1, 1] --------------------------------------------
    # a SQUARED correlation is a proportion; check it before the signed rule
    (r"(?i)correlationsq|corrsq|rsq|(?i)correlation.*squared", UNIT,
     "a squared correlation -- a proportion of variance"),
    (r"(?i)genetic[_]?correlation|^r[_]?g$|(?i)correlation", CORR,
     "a correlation coefficient"),
    (r"(?i)(^|[^a-z])rho($|[^a-z])", CORR, "rho denotes a correlation"),
    (r"(?i)cosine|cossim", CORR, "a cosine similarity"),
    # -- squared / variance-explained quantities: [0, 1] -------------------
    (r"(?i)r2|rsquared|varianceexplained|explainedvariance|pve",
     UNIT, "a proportion of variance explained"),
    (r"(?i)heritability|(^|[^a-z])h2($|[^a-z])", UNIT, "a heritability"),
    # -- F_ST and relatives: [0, 1] ---------------------------------------
    (r"(?i)fst|fixationindex|wrightf(is|it|st)", UNIT,
     "a fixation index / F-statistic"),
    (r"(?i)heterozygosity|(^|[^a-z])het($|[A-Z])", UNIT, "a heterozygosity"),
    # -- probabilities and frequencies: [0, 1] ----------------------------
    (r"(?i)probability|prevalence|^prob|(?i)allelefreq|allelefrequency|"
     r"(?i)frequency(?!.*spectrum)|(?i)^p[_]?[0-9]?$|(?i)maf",
     UNIT, "a probability or allele frequency"),
    (r"(?i)^power|(?i)power$|(?i)statisticalpower", UNIT, "a statistical power"),
    (r"(?i)auc|cstatistic|concordance", UNIT, "an AUC / c-statistic"),
    (r"(?i)proportion|fraction|share|percent|sharedfraction",
     UNIT, "a proportion"),
    (r"(?i)mutationrate|migrationrate|recombinationrate|errorrate|"
     r"falsepositiverate|discoveryrate", UNIT,
     "a per-generation / per-test probability"),
    (r"(?i)sensitivity|specificity|precision|recall|ppv|npv", UNIT,
     "a classification rate"),
    (r"(?i)portability|retention|attenuation|shrinkage|calibrationslope",
     UNIT, "a portability / retention factor -- a fraction of what transfers"),
    (r"(?i)coverage|typeierror|falsepositiverate|alpha$", UNIT, "an error rate"),
    (r"(?i)brier", (0.0, 1.0), "a Brier score for a binary outcome"),
    (r"(?i)admixtureproportion|ancestryproportion|ancestryfraction", UNIT,
     "an ancestry proportion"),
    # -- nonnegative -------------------------------------------------------
    (r"(?i)variance(?!explained)|^var[A-Z_]|(?i)sigmasq|sigma2|msе|mse$",
     NONNEG, "a variance"),
    (r"(?i)noncentrality|(^|[^a-z])ncp($|[^a-z])", NONNEG,
     "a noncentrality parameter"),
    (r"(?i)entropy|mutualinformation|divergence|kl$|kldiv|relativeentropy",
     NONNEG, "an information-theoretic divergence"),
    (r"(?i)standarderror|^se[A-Z_]|(?i)stddev|standarddeviation", NONNEG,
     "a standard deviation / standard error"),
    (r"(?i)distance|norm(?!al)", NONNEG, "a distance or norm"),
    (r"(?i)count|number[_]?of|^num[A-Z]", NONNEG, "a count"),
    # -- strictly positive -------------------------------------------------
    (r"(?i)effectivesamplesize|(^|[^a-z])ess($|[^a-z])", POS,
     "an effective sample size"),
    (r"(?i)effectivepopulationsize|effectivesize", POS,
     "an effective population size"),
]

DOC_RANGES = [
    (r"∈\s*\[\s*0\s*,\s*1\s*\]|in\s*\[0,\s*1\]|lies in \[0, ?1\]", UNIT,
     "the docstring states the range [0,1]"),
    (r"∈\s*\[\s*-\s*1\s*,\s*1\s*\]|in\s*\[-1,\s*1\]", CORR,
     "the docstring states the range [-1,1]"),
    (r"(?i)is a probability|is a proportion|is a fraction", UNIT,
     "the docstring calls it a probability/proportion"),
    (r"(?i)nonnegative|non-negative", NONNEG,
     "the docstring states nonnegativity"),
]


def _prep(table):
    """Compile the tables case-insensitively.

    The inline `(?i)` markers were written per-alternative; Python only allows
    them at position 0, so they are stripped and the whole pattern is compiled
    with IGNORECASE.
    """
    return [(re.compile(pat.replace("(?i)", ""), re.I), rng, why)
            for pat, rng, why in table]


_NAME_RANGES = _prep(NAME_RANGES)
_DOC_RANGES = _prep(DOC_RANGES)


# A name of the form `xFromY` returns an x, not a y.  Matching the whole name
# makes `tauFromObservedEffectCorrelation` look like a correlation when it
# returns an OU timescale, and `stabilizingNsFromObservedCorrelation` look like
# a correlation when it returns Ns.  Only the part before `From` names the
# result.
FROM_SPLIT = re.compile(r"From[A-Z]")

# Words that cancel a range rule: a SCALED rate (θ = 4Neμ, M = 4Nm) is a
# compound parameter, not a per-generation probability, and a RATIO of two
# such quantities is not confined to [0,1] by anything.
RANGE_VETO = re.compile(
    r"scaled|ratio$|odds|logit|log[A-Z]|perGeneration|^inv|Inverse|"
    # a matrix trace / eigenvalue / determinant is not a rate, and a
    # CALIBRATION SLOPE is not a proportion -- a slope above one is
    # under-dispersion, a real and expected state, not an error.
    r"trace|matrix|eigen|determinant|slope|enrichment|excess|surplus|"
    r"inflation|amplification|regret|numberNeeded|required[A-Z]|"
    # an MSE, a variance and a count are unbounded above whatever else the
    # name says; `sourceShrinkageMSE` is an MSE, not a shrinkage factor.
    r"mse$|rmse$|sse$|loss$|risk$|variance$|count$|size$", re.I)


def result_name(d):
    """The part of the name that names the RESULT."""
    name = d["name"]
    m = FROM_SPLIT.search(name)
    return name[: m.start()] if m and m.start() > 2 else name


def required_range(d):
    """Return (lo, hi, why) or None if the name commits to nothing."""
    name = result_name(d)
    if RANGE_VETO.search(name):
        return None
    for pat, rng, why in _NAME_RANGES:
        if pat.search(name):
            return (rng[0], rng[1], f"`{name}` names {why}")
    if name != d["name"]:
        return None
    doc = d.get("doc", "")
    for pat, rng, why in _DOC_RANGES:
        if pat.search(doc):
            return (rng[0], rng[1], why)
    return None


# --------------------------------------------------------------------------
# admissible boxes from parameter meaning

# name pattern -> (lo, hi, scale, why).  `scale` picks the sampling measure.
PARAM_BOXES = [
    (r"^(p|q|p_?bar|p[₀₁₂0-9]|q[₀₁₂0-9]|p_[a-z]|af|maf|freq)$",
     (1e-6, 1 - 1e-6, "lin", "an allele frequency lies in (0,1)")),
    (r"(?i)^(ne|n_e|nₑ|neSource|neTarget|ne_?[abt]\w*|effN|effectiveN)$",
     (1.0, 1e7, "log", "an effective population size is positive")),
    (r"(?i)^(n|nGwas|n_gwas|nCase\w*|nControl\w*|nTrain\w*|nTest\w*|nSnp\w*|"
     r"sampleSize|nTarget|nSource|m_?snps?)$",
     (1.0, 1e7, "log", "a sample or variant count is a positive integer")),
    (r"(?i)^(t|gen|generation\w*|t_b|t_r|tSplit|time)$",
     (0.0, 1e4, "log1p", "a time in generations is nonnegative")),
    (r"(?i)^(m|m₁₂|m₂₁|mig\w*|migrationRate)$",
     (1e-9, 0.5, "log", "a migration rate is a per-generation probability")),
    (r"(?i)^(mu|μ|mutationRate|u)$",
     (1e-10, 1e-2, "log", "a mutation rate per generation")),
    (r"(?i)^(s|sel\w*|selectionCoef\w*)$",
     (1e-6, 1.0, "log", "a selection coefficient in (0,1]")),
    (r"(?i)^(c|r|rec\w*|recombRate|recombinationRate|theta_?r)$",
     (1e-8, 0.5, "log", "a recombination fraction in (0,0.5]")),
    (r"(?i)^(θ|theta|scaledMutationRate)$",
     (1e-6, 1.0, "log", "θ = 4·Ne·μ, the scaled mutation rate")),
    (r"(?i)^(h2|h_?2|heritability|h2Obs|h2Liab)$",
     (1e-4, 1.0, "lin", "a heritability in (0,1]")),
    (r"(?i)^(r2|r_?2|r2Gwas|r2Source|r2Target|rSq)$",
     (1e-6, 1.0, "lin", "an R² in (0,1]")),
    (r"(?i)^(k|prevalence|prev)$",
     (1e-5, 0.5, "log", "a disease prevalence")),
    (r"(?i)^(rho|ρ|rg|r_?g|corr\w*|geneticCorrelation)$",
     (-1.0, 1.0, "lin", "a correlation in [-1,1]")),
    (r"(?i)^(fst|f_?st|fstSource|fstTarget|f_?st_?\w*)$",
     (0.0, 1.0, "lin", "an F_ST in [0,1]")),
    (r"(?i)^(alpha|α|admixture\w*|ancestryProp\w*)$",
     (0.0, 1.0, "lin", "an admixture / mixing proportion in [0,1]")),
    (r"(?i)^(h_?t|h_?s|h₀|h0|het\w*|heterozygosity\w*)$",
     (1e-9, 1.0, "lin", "a heterozygosity in (0,1]")),
    (r"(?i)^(v|v_\w+|v[A-Z]\w*|var\w*|sigma\w*|σ\w*|sd\w*|noiseVar|signalVar)$",
     (1e-6, 1e3, "log", "a variance / scale parameter is positive")),
    (r"(?i)^(beta|β|effect\w*|b)$",
     (-5.0, 5.0, "lin", "an effect size on a standardized scale")),
    (r"(?i)^(d|dist\w*|deme\w*|numDemes)$",
     (1.0, 1e3, "log", "a distance or deme count is positive")),
    (r"(?i)^(l|len\w*|length|window\w*)$",
     (1e-3, 1e6, "log", "a length scale is positive")),
    (r"(?i)^(lam|lambda|λ|decay|decayFactor)$",
     (0.0, 1.0, "lin", "a decay factor per step is in [0,1]")),
    (r"(?i)^(kappa|κ|scale|scaleFactor|c\w*Scale)$",
     (1e-3, 1e3, "log", "a positive scale factor")),
]


_PARAM_BOXES = [(re.compile(pat.replace("(?i)", ""), re.I), box)
                for pat, box in PARAM_BOXES]

# Second tier: SUBSTRING evidence.  Parameter names in this corpus are
# descriptive (`h2_true`, `avg_r2_tag`, `fstTarget`, `v_noise_s`), so an
# exact-match table misses most of them and the definition falls through to a
# junk default -- which manufactures escapes at physically meaningless points
# like an allele frequency of -1000.  These rules read the name for evidence.
#
# Only multi-character, unambiguous tokens appear here.  Single letters (`t`,
# `m`, `s`, `c`, `n`) are handled by the exact table above, because as
# substrings they fire inside unrelated words -- `total` is not a time and
# `v_sig_s` is not a selection coefficient.  Order is significance order: the
# first matching rule wins.
SUBSTRING_BOXES = [
    (("fixation", "f_st", "fst"),
     (0.0, 0.5, "lin", "an F_ST lies in [0,1]; human between-continent values "
      "reach ~0.15, so [0, 0.5] is already generous")),
    (("herit", "h2"), (1e-3, 1.0, "lin", "a heritability lies in (0,1]")),
    (("rsq", "r2", "varexp", "varianceexplained", "pve"),
     (1e-4, 1.0, "lin", "an R² / variance-explained lies in (0,1]")),
    (("prevalence", "baserate"), (1e-4, 0.5, "log", "a disease prevalence")),
    (("correlation", "corr", "rho", "cosine"),
     (-1.0, 1.0, "lin", "a correlation lies in [-1,1]")),
    (("allelefreq", "freq", "maf"),
     (1e-4, 1 - 1e-4, "lin", "an allele frequency lies in (0,1)")),
    (("heterozyg",), (1e-4, 1.0, "lin", "a heterozygosity lies in (0,1]")),
    (("sensitivity", "specificity", "ppv", "npv", "auc", "concordance",
      "accuracy", "coverage", "power", "proportion", "fraction", "share",
      "percent", "sparsity", "overlap", "admixture", "ancestry", "purity",
      "probability", "prob", "weight", "alpha", "sens", "spec", "prop", "frac",
      "tpr", "fpr", "tnr", "fnr", "recall", "precision"),
     (0.0, 1.0, "lin", "a proportion / probability lies in [0,1]")),
    (("popsize", "effectivesize", "effn", "neanc", "nesource", "netarget"),
     (1.0, 1e6, "log", "an effective population size is positive")),
    (("samplesize", "nsnp", "nvariant", "nmarker", "nloci", "nblock", "ncase",
      "ncontrol", "ntrain", "ntest", "ngwas", "nsample", "nparam", "size",
      "count", "num", "_n"),
     (1.0, 1e7, "log", "a sample / variant count is a positive integer")),
    (("mutationrate", "mutrate"),
     (1e-9, 1e-2, "log", "a mutation rate per generation")),
    (("migration",),
     (1e-8, 0.5, "log", "a migration rate is a per-generation probability")),
    (("recomb",), (1e-8, 0.5, "log", "a recombination fraction is in (0,0.5]")),
    (("selection", "selcoef"),
     (1e-6, 1.0, "log", "a selection coefficient lies in (0,1]")),
    (("theta",), (1e-5, 1.0, "log", "θ = 4·Ne·μ, a scaled mutation rate")),
    (("lambda", "decay", "hazard", "rate"),
     (1e-6, 1.0, "log", "a per-unit rate / decay factor lies in (0,1]")),
    (("length", "distance", "deme", "window", "span", "morgan"),
     (1e-3, 1e5, "log", "a length / distance is positive")),
    (("variance", "sigma", "noise", "signal", "stddev", "_sq", "sq_",
      "vsignal", "vresidual", "var", "tau", "sig"),
     (1e-4, 1e3, "log", "a variance / positive scale parameter")),
    (("effect", "slope", "intercept", "shift", "delta", "trend", "beta",
      "mean", "mu_", "_mu"),
     (-3.0, 3.0, "lin", "an effect / shift on a standardized scale")),
    (("threshold", "cutoff", "quantile", "zscore"),
     (-5.0, 5.0, "lin", "a threshold on a standardized scale")),
    (("time", "generation", "epoch"),
     (0.0, 1e3, "log1p", "a time in generations is nonnegative")),
    (("kappa", "gamma", "factor", "scale"),
     (1e-3, 1e2, "log", "a positive tuning factor")),
]

# Greek and subscripted single-symbol parameters, exact.
GREEK_BOXES = {
    "μ": (1e-9, 1e-2, "log", "μ is a mutation rate"),
    "θ": (1e-5, 1.0, "log", "θ = 4·Ne·μ"),
    "ρ": (-1.0, 1.0, "lin", "ρ is a correlation"),
    "σ": (1e-3, 1e2, "log", "σ is a standard deviation"),
    "τ": (1e-3, 1e2, "log", "τ is a scale parameter"),
    "λ": (1e-6, 1.0, "log", "λ is a rate"),
    "α": (0.0, 1.0, "lin", "α is a proportion or error rate"),
    "β": (-3.0, 3.0, "lin", "β is an effect size"),
    "δ": (-3.0, 3.0, "lin", "δ is a shift"),
    "κ": (1e-3, 1e2, "log", "κ is a positive tuning factor"),
    "η": (1e-3, 1e2, "log", "η is a positive tuning factor"),
    "π": (1e-4, 1 - 1e-4, "lin", "π is a probability or prevalence"),
    "γ": (1e-3, 1e2, "log", "γ is a positive tuning factor"),
}

# Suffixes that name WHICH population/arm a quantity belongs to, not what kind
# of quantity it is.  Stripping them lets `r2Target`, `fst_s`, `neB` match.
ROLE_SUFFIX = re.compile(
    r"(source|target|src|tgt|train|test|disc|repl|obs|true|est|hat|new|old|"
    r"anc|adm|pop|[abst12]|₁|₂|₀)$", re.I
)


# Single letters that mean a COUNT when the Lean type is ℕ, whatever they
# would mean at type ℝ (`k` is a prevalence at ℝ and a founder count at ℕ).
NAT_COUNTS = re.compile(r"^(k|n|m|j|i|d|l|r|t|s|c|q)$")


def param_box(pname, ptype):
    """(lo, hi, scale, why) for a parameter, or None if the name says nothing.

    Returning None matters: it is the signal that the definition is unguarded
    in that coordinate, and the caller reports that rather than inventing a
    box to make the definition pass.
    """
    if ptype == "ℕ" and NAT_COUNTS.match(pname):
        if pname == "t":
            return (0.0, 500.0, "nat", "a ℕ time in generations")
        return (1.0, 1e4, "nat", f"`{pname} : ℕ` is a count, so a positive integer")
    box = _param_box_real(pname)
    if ptype == "ℕ":
        if box:
            lo, hi, sc, why = box
            return (max(0.0, lo), min(hi, 1e5), "nat", why + " (a ℕ argument)")
        return (0.0, 1000.0, "nat", "a ℕ argument is a nonnegative integer")
    return box


def _lookup(name):
    for pat, box in _PARAM_BOXES:
        if pat.match(name):
            return box
    if name in GREEK_BOXES:
        return GREEK_BOXES[name]
    low = name.lower().replace("'", "")
    padded = "_" + low + "_"
    for toks, box in _SUB:
        for t in toks:
            hit = t in padded if (t.startswith("_") or t.endswith("_")) else t in low
            if hit:
                return box
    return None


# A name ending in `Sq` names a SQUARE, so it is nonnegative whatever the
# unsquared quantity's range is: `rhoSq` is not a correlation in [-1,1].
SQ_SUFFIX = re.compile(r"(sq|squared|_2|2)$", re.I)


def _param_box_real(pname):
    box = _lookup(pname)
    if box and SQ_SUFFIX.search(pname) and box[0] < 0:
        lo, hi, sc, why = box
        return (0.0, hi, sc, why + "; the `Sq` suffix makes it a square, so "
                                  "nonnegative")
    if box:
        return box
    # retry after stripping role suffixes and separators: `r2_target` -> `r2`
    stem = pname
    for _ in range(3):
        nxt = ROLE_SUFFIX.sub("", stem.rstrip("_")).rstrip("_")
        if nxt == stem or not nxt:
            break
        stem = nxt
        box = _lookup(stem)
        if box:
            return box
    return None


_SUB = [(toks, box) for toks, box in SUBSTRING_BOXES]


# --------------------------------------------------------------------------
# hypotheses harvested from theorems -> numeric constraints on a parameter

HYP_PATS = [
    (r"^0\s*<\s*(\w[\w'₀-₉]*)$", lambda m: (m.group(1), 0.0, INF, "strict")),
    (r"^0\s*≤\s*(\w[\w'₀-₉]*)$", lambda m: (m.group(1), 0.0, INF, "weak")),
    (r"^(\w[\w'₀-₉]*)\s*<\s*1$", lambda m: (m.group(1), -INF, 1.0, "strict")),
    (r"^(\w[\w'₀-₉]*)\s*≤\s*1$", lambda m: (m.group(1), -INF, 1.0, "weak")),
    (r"^([\d.]+)\s*<\s*(\w[\w'₀-₉]*)$",
     lambda m: (m.group(2), float(m.group(1)), INF, "strict")),
    (r"^([\d.]+)\s*≤\s*(\w[\w'₀-₉]*)$",
     lambda m: (m.group(2), float(m.group(1)), INF, "weak")),
    (r"^(\w[\w'₀-₉]*)\s*<\s*([\d.]+)$",
     lambda m: (m.group(1), -INF, float(m.group(2)), "strict")),
    (r"^(\w[\w'₀-₉]*)\s*≤\s*([\d.]+)$",
     lambda m: (m.group(1), -INF, float(m.group(2)), "weak")),
]


def parse_hyp(h):
    """Turn one hypothesis atom into (param, lo, hi, kind) or None."""
    h = h.strip().rstrip(",")
    for pat, fn in HYP_PATS:
        m = re.match(pat, h)
        if m:
            try:
                return fn(m)
            except ValueError:
                return None
    return None


def _rename(text, argmap):
    if not argmap:
        return text
    return re.sub(r"[A-Za-z_][\w'₀-₉]*", lambda m: argmap.get(m.group(), m.group()),
                  text)


def theorem_box(d):
    """Intersect the numeric hypotheses of the theorems that mention `d`.

    Returns (box, provenance).  A parameter constrained by NO theorem keeps
    (-inf, inf) here; the caller falls back to the meaning-derived box and
    records that the author stated nothing.
    """
    names = [p for p, _ in d["params"]]
    box = {p: [-INF, INF] for p in names}
    seen = {p: [] for p in names}
    for t in d.get("theorem_hyps", []):
        for h in t["hyps"]:
            r = parse_hyp(_rename(h, t.get("argmap") or {}))
            if not r:
                continue
            p, lo, hi, kind = r
            if p not in box:
                continue
            # UNION over theorems (each theorem is a separate claim), so we
            # widen; a claim proved on a wider box is the stronger claim.
            box[p][0] = min(box[p][0], lo) if seen[p] else lo
            box[p][1] = max(box[p][1], hi) if seen[p] else hi
            seen[p].append((t["thm"], h))
    return box, seen


def admissible_box(d):
    """Final box + a per-parameter provenance record.

    `source` is one of 'theorem', 'meaning', or 'none'.  'none' anywhere means
    the definition is UNGUARDED in that coordinate.
    """
    tbox, seen = theorem_box(d)
    out = {}
    unguarded = []
    for p, ty in d["params"]:
        lo, hi = tbox.get(p, [-INF, INF])
        has_thm = bool(seen.get(p))
        mb = param_box(p, ty)
        if has_thm and math.isfinite(lo) and math.isfinite(hi):
            out[p] = dict(lo=lo, hi=hi, scale="lin", source="theorem",
                          why=[f"{t}: {h}" for t, h in seen[p]])
            continue
        if mb:
            mlo, mhi, sc, why = mb
            if has_thm:
                lo2 = max(lo, mlo) if math.isfinite(lo) else mlo
                hi2 = min(hi, mhi) if math.isfinite(hi) else mhi
                if lo2 < hi2:
                    out[p] = dict(lo=lo2, hi=hi2, scale=sc, source="theorem+meaning",
                                  why=[why] + [f"{t}: {h}" for t, h in seen[p]])
                    continue
            out[p] = dict(lo=mlo, hi=mhi, scale=sc, source="meaning", why=[why])
            if not has_thm:
                unguarded.append(p)
            continue
        out[p] = dict(lo=-1e3, hi=1e3, scale="lin", source="none",
                      why=["no theorem hypothesis and no recognised meaning "
                           f"for parameter `{p}` : {ty}"])
        unguarded.append(p)
    return out, unguarded


# --------------------------------------------------------------------------
# relational side conditions
#
# Most of this corpus's range claims are guarded not by a box but by a
# RELATION between arguments: `H_S ≤ H_T` for Nei's F_ST, `D_sq ≤ var_tag *
# var_causal` for a tag r² (Cauchy-Schwarz), `total = between + within` for an
# explainable fraction.  A checker that ignores these reports every one of them
# as a defect, which is worse than reporting nothing.  We harvest them from the
# theorems and apply them as constraints on the search.
#
# The residual finding is then sharp and worth reporting: a range that holds
# ONLY under a side condition the definition itself does not state.

RANGE_THM = re.compile(
    r"nonneg|_pos\b|in_unit|le_one|_lt_one|_bound|bounded|_range|"
    r"between_zero|unit_interval", re.I
)


def side_constraints(d):
    """Relational hypotheses of the theorems that bound `d`.

    Returns a list of dicts {thm, hyp} holding Lean hypothesis text that
    relates two or more of the definition's own parameters.  Purely numeric
    one-sided bounds are excluded -- those already went into the box.
    """
    pnames = {p for p, _ in d["params"]}
    out, seen = [], set()
    for t in d.get("theorem_hyps", []):
        for h in t["hyps"]:
            h = _rename(h.strip().rstrip(","), t.get("argmap") or {})
            if parse_hyp(h) is not None:
                continue  # already a box constraint
            if not re.search(r"[<>≤≥=]", h):
                continue
            toks = set(re.findall(r"[A-Za-z_][\w'₀-₉]*", h))
            mentioned = toks & pnames
            if len(mentioned) < 1:
                continue
            # keep only hypotheses expressible in the arithmetic fragment
            if re.search(r"[∀∃∑∏∫λ]|fun |Finset|Measure|→", h):
                continue
            if h in seen:
                continue
            seen.add(h)
            out.append(dict(thm=t["thm"], hyp=h,
                            guards_range=bool(RANGE_THM.search(t["thm"]))))
    return out

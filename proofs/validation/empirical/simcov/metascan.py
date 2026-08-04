"""Repo-wide scan for the META-CATEGORIES behind each measured falsehood.

A falsified definition that gets a corrected body and a docstring is one bug
fixed.  The question this scanner asks is the one that matters: WHAT CLASS of
mistake was it, and where else in the corpus does that class live?

Lean cannot answer it.  A `def` is a stipulation, so there is nothing in
`def coalFst t Ne := t / (t + 2 * Ne)` for the kernel to disagree with, and every
theorem proved about it -- nonnegativity, monotonicity, the junk-value lemmas --
is true whatever the formula denotes.  A green build and a clean `#print axioms`
are therefore evidence about the ALGEBRA and no evidence at all about the
biology.  That gap is what the `Empirical status` markers exist to cover, and
what these three screens make enforceable.

  CATEGORY A -- UNRESOLVED FORK.  Two definitions of one observable, related to
    each other by an INEQUALITY or a difference but never by an equality, with
    neither carrying a measurement.  The corpus can then compute two different
    numbers for one quantity and prove theorems about both.  This is exactly
    `pairwiseFstFromBranchTaus` against `coalFst`: 0.50 versus 0.33 on the same
    simulated split, and a theorem stating only that one is BELOW the other.
    Guard 3c already screens for same-BODY duplicates; a fork has different
    bodies by construction, so it walks straight through.

  CATEGORY B -- UNDERSPECIFIED SIGNATURE.  The named quantity depends on
    something the argument list cannot express, so no value of the arguments
    makes it right.  `freqCorrFromFst (fst)` cannot see the ancestral spread;
    `fstMigrationMutationEquilibrium (Ne, m, mu)` cannot see the deme count.
    `check.py` already has the mechanism for this (`REQUIRED_ARGS`); it was
    simply missing the entries, which is why this scanner proposes them.

  CATEGORY C -- UNRESOLVED CANDIDATE.  A definition whose own docstring calls it
    a candidate, an alternative, or a form retained for comparison, that has
    never been discriminated from the sibling it is an alternative TO.  Retaining
    both is defensible only until a measurement can separate them;
    `steppingStoneFstQuadratic` sat here through a log-log slope of 0.959 against
    its predicted 2.
"""
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "proofs/Calibrator"


def lean_files(root):
    import glob
    fs = (glob.glob(os.path.join(root, "*.lean")) +
          glob.glob(os.path.join(root, "*", "*.lean")))
    extra = root.rstrip("/") + ".lean"
    if os.path.exists(extra):
        fs.append(extra)
    return sorted(fs)


def strip_comments(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def preceding_doc(lines, i):
    j = i - 1
    while j >= 0 and (not lines[j].strip() or lines[j].lstrip().startswith("@[")):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    while j >= 0 and "/--" not in lines[j]:
        if "/-!" in lines[j] or ("-/" in lines[j] and j != end):
            return ""
        j -= 1
    return "\n".join(lines[max(0, j):end + 1])


# --------------------------------------------------------------------------
# corpus model
# --------------------------------------------------------------------------
DEFS = {}          # short name -> dict(file, line, args, doc, status)
THEOREMS = []      # (file, name, statement)


def build():
    for f in lean_files(ROOT):
        raw = open(f, errors="ignore").read()
        raw_lines = raw.split("\n")
        src = strip_comments(raw)
        for i, line in enumerate(src.split("\n")):
            m = re.match(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)([^:]*):", line)
            if not m:
                continue
            short = m.group(1).split(".")[-1]
            doc = preceding_doc(raw_lines, i)
            st = re.search(r"Empirical status:\s*[*_ ]*([A-Za-z_]+)", doc)
            DEFS[short] = dict(file=os.path.basename(f), line=i + 1,
                               args=m.group(2), doc=doc,
                               status=(st.group(1).upper() if st else None))
        for m in re.finditer(r"^theorem\s+([A-Za-z_][\w.']*)(.*?):=", src,
                             re.S | re.M):
            THEOREMS.append((os.path.basename(f), m.group(1), m.group(2)))


# --------------------------------------------------------------------------
# CATEGORY A: unresolved forks
# --------------------------------------------------------------------------
# Observables whose name is unambiguous enough to group on.  Two definitions in
# one group compute the SAME number or one of them is misnamed.
OBSERVABLE = [
    ("F_ST", re.compile(r"fst|gst", re.I)),
    ("heterozygosity", re.compile(r"^het|heterozyg", re.I)),
    ("LD (D or r^2)", re.compile(r"^ld[A-Z_]|LD(?=[A-Z_]|$)|linkage", re.I)),
    ("AUC", re.compile(r"auc", re.I)),
    ("R^2", re.compile(r"r2(?![0-9])", re.I)),
    ("drift index", re.compile(r"drift", re.I)),
    ("portability", re.compile(r"portab", re.I)),
]
MEASURED = {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED"}


def category_a():
    print("=" * 78)
    print("CATEGORY A -- UNRESOLVED FORK")
    print("  two defs of one observable, related only by an inequality or a")
    print("  difference, neither carrying a measurement")
    print("=" * 78)
    hits = []
    for label, pat in OBSERVABLE:
        members = [n for n in DEFS if pat.search(n)]
        if len(members) < 2:
            continue
        for th_file, th_name, stmt in THEOREMS:
            present = [n for n in members
                       if re.search(r"\b" + re.escape(n) + r"\b", stmt)]
            if len(present) < 2:
                continue
            # does this theorem ASSERT AGREEMENT, or only order/difference?
            concl = stmt.split(":", 1)[-1]
            has_eq = re.search(r"(?<![<>≤≥≠!])=(?!=)", concl)
            has_ineq = re.search(r"[<>≤≥≠]|\-\s", concl)
            if has_eq:
                continue
            if not has_ineq:
                continue
            unmeasured = [n for n in present
                          if DEFS[n]["status"] not in MEASURED]
            if len(unmeasured) >= 2:
                hits.append((label, th_file, th_name, present))
    seen = set()
    for label, th_file, th_name, present in hits:
        key = tuple(sorted(present))
        if key in seen:
            continue
        seen.add(key)
        print("\n  [%s] %s" % (label, " vs ".join(sorted(present))))
        print("    forked by: %s (%s)" % (th_name, th_file))
        for n in sorted(present):
            print("      %-42s %-14s %s:%d"
                  % (n, DEFS[n]["status"] or "no marker",
                     DEFS[n]["file"], DEFS[n]["line"]))
    print("\n  CATEGORY A total: %d unresolved forks" % len(seen))
    return seen


# --------------------------------------------------------------------------
# CATEGORY B: underspecified signatures
# --------------------------------------------------------------------------
# Each entry is a dependency MEASURED in proofs/validation/empirical/simcov/.
PROPOSED_REQUIRED_ARGS = [
    (r"freqcorr|frequencycorrel|allelefreqcorr",
     [r"var", r"spread", r"ancestral", r"sd\b"],
     "the allele-frequency correlation is Var(p0)/(Var(p0)+F*E[p0(1-p0)]) and "
     "moves from 0.00 to 0.72 at FIXED F_ST as the ancestral spread changes"),
    (r"island|migrationmutationequil|migrationdriftequil",
     [r"nDeme", r"demes", r"\bn\b", r"islands"],
     "island-model F_ST depends on the deme count: at fixed 4*Ne*m the "
     "simulated F_ST moves from 0.093 at 2 demes to 0.165 at 4"),
    (r"steppingstone",
     [r"sigma", r"σ", r"disp"],
     "stepping-stone F_ST depends on the dispersal scale, and the fitted "
     "scale factor goes as m^0.959 not m^2"),
]


def category_b():
    print("\n" + "=" * 78)
    print("CATEGORY B -- UNDERSPECIFIED SIGNATURE")
    print("  the named quantity depends on something the arguments cannot express")
    print("=" * 78)
    hits = []
    for n, d in sorted(DEFS.items()):
        for pat, needed, why in PROPOSED_REQUIRED_ARGS:
            if not re.search(pat, n, re.I):
                continue
            if not any(re.search(a, d["args"], re.I) for a in needed):
                hits.append((n, d, needed[0], why))
    for n, d, need, why in hits:
        print("\n  %-44s %s:%d" % (n, d["file"], d["line"]))
        print("    args: %s" % " ".join(d["args"].split())[:70])
        print("    takes no %s-like argument; %s" % (need, why))
    print("\n  CATEGORY B total: %d underspecified signatures" % len(hits))
    return hits


# --------------------------------------------------------------------------
# CATEGORY C: unresolved candidates
# --------------------------------------------------------------------------
CANDIDATE = re.compile(
    r"offered as a candidate|is a candidate|as a candidate for|"
    r"retained so that|the alternative form|alternative to|"
    r"the form the previous|competing form|rival form|"
    r"not substituted for", re.I)


def category_c():
    print("\n" + "=" * 78)
    print("CATEGORY C -- UNRESOLVED CANDIDATE")
    print("  a self-declared alternative never discriminated from its sibling")
    print("=" * 78)
    hits = []
    for n, d in sorted(DEFS.items()):
        if not d["doc"] or not CANDIDATE.search(d["doc"]):
            continue
        if d["status"] in MEASURED:
            continue
        hits.append((n, d, CANDIDATE.search(d["doc"]).group(0)))
    for n, d, phrase in hits:
        print("\n  %-44s %s:%d  [%s]"
              % (n, d["file"], d["line"], d["status"] or "no marker"))
        print("    declares itself: \"%s\"" % phrase)
    print("\n  CATEGORY C total: %d unresolved candidates" % len(hits))
    return hits


if __name__ == "__main__":
    build()
    print("corpus: %d top-level defs, %d theorems\n" % (len(DEFS), len(THEOREMS)))
    a = category_a()
    b = category_b()
    c = category_c()
    print("\n" + "=" * 78)
    print("TOTAL META-CATEGORY HITS: A=%d  B=%d  C=%d" % (len(a), len(b), len(c)))

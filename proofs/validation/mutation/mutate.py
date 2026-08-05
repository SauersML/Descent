#!/usr/bin/env python3.12
"""Proof mutation: three modes over the Calibrator corpus.

    one       one mutant per Prop binder, that binder deleted   -> DROPPABLE
    all       one mutant per theorem, every Prop binder deleted -> UNCONDITIONAL
    vacuity   binders kept, conclusion replaced by `False`      -> VACUOUS

The first two close the tactic blind spot described below.  `vacuity` answers a
different question -- are the corpus's hypothesis sets satisfiable -- and also
covers conclusion-negation for this fragment, since a proof that survives a
negated conclusion yields both `C` and `¬C` and hence `False`.

Delete-and-rebuild for the tactic blind spot.

`omega`, `linarith`, `simp_all` and friends splice every hypothesis in scope
into the certificate they emit, so a hypothesis they did not need still occurs
in the kernel term and the occurrence-freedom scan in Check.lean cannot see it.
Closing that direction needs the statement actually rebuilt without the binder.

For each eligible theorem this emits one `example` per Prop binder, with that
binder removed and the ORIGINAL proof script unchanged, into a probe module
that imports the source module.  One build per source module rather than one
per mutant: 4065 mutants over ~112 builds.

A mutant that COMPILES proves the binder was not needed.  A mutant that fails
proves nothing -- the tactic may simply have found a different route with the
hypothesis present, or the example may fail to resolve a name.  So this is a
LOWER BOUND with no false-positive direction, the same shape as the scan it
supplements.

Calibration planted in every probe module:
  CALIB-DROPPABLE  a droppable binder; the mutant MUST compile.
  CALIB-NEEDED     a needed binder;    the mutant MUST NOT compile.
  CALIB-FRESH      an unconditional falsehood whose error MUST appear, or the
                   log is stale.
"""
import re
import sys
import pathlib

GUARD_ONE = "TACGUARD-C1"
GUARD_ALL = "TACGUARD-C2"
GUARD_VAC = "VACGUARD-C3"

SPLICERS = ["omega", "linarith", "nlinarith", "polyrith", "simp_all", "aesop",
            "decide", "positivity", "bound", "field_simp", "tauto", "grind"]
BINDER_OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
BINDER_CLOSE = {")", "}", "]", "⦄"}
PROPISH = re.compile(r"[<>≤≥≠∀∃∧∨¬→↔]|(?<![:=])=(?!=)")

CALIB = """
-- {g} CALIB-DROPPABLE
example (zzn : Nat) : 0 < zzn + 1 := by omega
-- {g} CALIB-NEEDED
example (zzm : Nat) : 1 < zzm := by omega
-- {g} CALIB-FRESH
example : (1:Nat) = 2 := by norm_num
"""


def decls(text):
    """(name, binder_text, conclusion_text, proof_text) per theorem/lemma."""
    starts = [m.start() for m in re.finditer(r"^(theorem|lemma) ", text, re.M)]
    for k, start in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else len(text)
        seg = text[start:stop]
        # trim a trailing `end ...` / `/-!` block belonging to the file, not the proof
        m = re.search(r"^(end |/-!|/--|@\[|namespace |section |variable |open )", seg[1:], re.M)
        if m:
            seg = seg[:m.start() + 1]
        i = seg.index(" ") + 1
        while i < len(seg) and seg[i] in " \n":
            i += 1
        j = i
        while j < len(seg) and (seg[j].isalnum() or seg[j] in "_.'₀₁₂₃₄₅₆₇₈₉"):
            j += 1
        name = seg[i:j]
        depth, p, binder_end = 0, j, None
        while p < len(seg):
            c = seg[p]
            if c in BINDER_OPEN:
                depth += 1
            elif c in BINDER_CLOSE:
                depth -= 1
                if depth < 0:
                    break
            elif depth == 0 and c == ":" and seg[p:p + 2] != ":=":
                binder_end = p
                break
            p += 1
        if binder_end is None:
            continue
        depth, q = 0, binder_end + 1
        while q < len(seg):
            c = seg[q]
            if c in BINDER_OPEN:
                depth += 1
            elif c in BINDER_CLOSE:
                depth -= 1
            elif depth == 0 and seg[q:q + 2] == ":=":
                break
            q += 1
        if q >= len(seg):
            continue
        yield (name, seg[j:binder_end], seg[binder_end + 1:q], seg[q:],
               text[:start].count("\n") + 1)


def binder_groups(binders):
    """[(text_with_delims, is_prop, single_name_or_None)] in source order."""
    out, depth, cur, opener = [], 0, "", ""
    for ch in binders:
        if ch in BINDER_OPEN:
            if depth == 0:
                opener, cur = ch, ""
                depth += 1
                continue
            depth += 1
        elif ch in BINDER_CLOSE:
            depth -= 1
            if depth == 0:
                inner = cur
                names = inner.split(":", 1)[0].split() if ":" in inner else []
                isp = ":" in inner and bool(PROPISH.search(inner.split(":", 1)[1]))
                out.append((opener + inner + BINDER_OPEN[opener], isp,
                            names[0] if len(names) == 1 else None))
                cur = ""
                continue
        if depth >= 1:
            cur += ch
    return out


def build(path, mode):
    guard = {"one": GUARD_ONE, "all": GUARD_ALL, "vacuity": GUARD_VAC}[mode]
    all_at_once = mode == "all"
    text = pathlib.Path(path).read_text(errors="replace")
    parts = list(pathlib.Path(path).with_suffix("").parts)
    mod = ".".join(parts[parts.index("Calibrator"):])
    opens = [o for o in re.findall(r"^open .*$", text, re.M) if "private" not in o]
    lines = [f"import {mod}", "", CALIB.format(g=guard), "",
             "namespace Calibrator", ""] + opens + [""]
    n = 0
    for name, binders, concl, proof, srcline in decls(text):
        if mode == "vacuity":
            # SATISFIABILITY, not deletability: keep the binders and replace the
            # conclusion by `False`.  A probe that COMPILES means `linarith`
            # derived a contradiction from the theorem's own hypotheses, so the
            # theorem is vacuous and proves nothing.  Also covers
            # conclusion-negation for this fragment: a proof surviving a negated
            # conclusion yields both `C` and `¬C`, hence `False`.
            groups = binder_groups(binders)
            if not any(isp for _, isp, _ in groups):
                continue
            lines.append(f"-- {guard} VACMUT {mod} {name} hypotheses {srcline}")
            lines.append(f"example{binders}: False := by linarith")
            n += 1
            continue
        if not any(re.search(r"\b" + re.escape(t) + r"\b", proof) for t in SPLICERS):
            continue
        groups = binder_groups(binders)
        idx = [k for k, (gt, isp, sg) in enumerate(groups)
               if isp and sg is not None and not sg.startswith("_")]
        if not idx:
            continue
        if all_at_once:
            # One mutant per theorem, with EVERY named Prop binder removed.
            # Compiling means the conclusion needs no hypothesis at all.
            kept = "".join(g[0] for k, g in enumerate(groups) if k not in idx)
            dropped = ",".join(groups[k][2] for k in idx)
            lines.append(f"-- {guard} ALLMUT {mod} {name} {dropped} {srcline}")
            lines.append(f"example {kept} :{concl}{proof}")
            n += 1
        else:
            for gi in idx:
                kept = "".join(g[0] for k, g in enumerate(groups) if k != gi)
                lines.append(f"-- {guard} MUT {mod} {name} {groups[gi][2]} {srcline}")
                lines.append(f"example {kept} :{concl}{proof}")
                n += 1
    return "\n".join(lines) + "\n", n


if __name__ == "__main__":
    args = sys.argv[1:]
    mode = "one"
    if args and args[0].startswith("--"):
        mode = {"--all-at-once": "all", "--vacuity": "vacuity"}[args[0]]
        args = args[1:]
    guards = {"one": GUARD_ONE, "all": GUARD_ALL, "vacuity": GUARD_VAC}
    print(f"FRESHNESS_GUARD={guards[mode]}")
    outdir = pathlib.Path(args[0])
    total = 0
    for i, p in enumerate(args[1:]):
        body, n = build(p, mode)
        if n == 0:
            continue
        (outdir / f"TProbe{i:03d}.lean").write_text(body)
        total += n
    print(f"PROBE_FILES\t{len(list(outdir.glob('TProbe*.lean')))}")
    print(f"TOTAL_MUTANTS\t{total}")

"""Triage criterion for the `rfl`-provable theorem audit, STATED BEFORE READING.

=== WHY THE CRITERION IS PUBLISHED FIRST ===

A mechanical extraction hands over N candidates and the reading supplies
whichever verdict the reader already expected. That is the same failure as a
witness placed outside the slice it certifies: the test cannot come out any way
but the expected one. So the rule is written, committed, and only then applied.

The list also OVERSTATES IN THE DIRECTION OF "INTERESTING" before any reading
happens: `equivalence.py`'s `agree_everywhere_different_bodies` suggested 19
genuine identities because it compares equivalence CLASSES, while a theorem
equates a specific PAIR; re-joining on the pair gives 7. Concretely:
`cluster_identities_hold_at_every_retention` lands in a class with
`fisherInformation` because everything in that class is shaped `a*b`, which
says nothing whatever about the pair the theorem actually equates. JOIN ON THE
EQUATED PAIR, normalise argument names, and compare the two bodies directly. A criterion applied
after seeing 19 is not the same criterion as one applied after seeing 7.

=== "PROVABLE BY rfl" IS NOT THE SAME PREDICATE AS "TAUTOLOGY" ===

Both directions fail, which is why the mechanical flag cannot be the verdict:

  * TRUE, CLOSABLE, AND STILL DEFECTIVE. `neiGstFromFrequencies_eq_hudsonFst`
    (as it then was) proved that two spellings agree. They did. The defect was
    the NAME: it asserted an estimator identity that does not hold, because
    `hudsonFst` computed Nei's G_ST. Nothing about the proof was wrong.
  * rfl-PROVABLE AND LOAD-BEARING. When two sides were defined INDEPENDENTLY,
    the equality IS the claim, and the theorem is an anti-drift guard: change
    either body and it stops compiling. `ldAfterGenerations_eq_retainedFraction`
    and `driftLDStep_eq_islandFstMultiplicativeStep` exist for exactly that.

=== THE THREE BUCKETS, AND THE MECHANICAL DISCRIMINATOR ===

  A. rfl-PROVABLE AND VACUOUS.
     One side is the other by construction -- a wrapper, an abbreviation, or a
     restatement whose body literally invokes the other. Nothing can drift,
     because there is only one definition. Deleting it loses nothing.

  B. rfl-PROVABLE AND LOAD-BEARING.
     Two bodies written independently, neither mentioning the other, that
     happen to agree. The theorem is the assertion that they agree, and it is
     the only thing preventing them from separating. Deleting it removes a
     guard while leaving the code compiling -- silent, and undetectable later.

     DISCRIMINATOR BETWEEN A AND B, and it is mechanical:
     DOES EITHER DEFINITION'S BODY REFERENCE THE OTHER?
     Yes -> A, the equality is structural.  No -> B, the equality is a claim.
     This is decidable from the bodies alone, without reading the docstring,
     which is what keeps the reader's expectation out of it.

  C. NOT ACTUALLY rfl, BUT EASY.
     Closes by `ring`/`simp`/`norm_num`, often with hypotheses. Trivial is not
     the same as vacuous: `ascertainment_artificial_loss` is easy, and dropping
     `h_array_worse` makes its second conjunct FALSE, so the hypothesis is
     load-bearing and the theorem has content.

     TEST FOR C: drop each hypothesis in turn and ask whether the statement
     survives. A hypothesis whose removal falsifies the conclusion is content.

  D. rfl-PROVABLE, TRUE, AND CERTIFYING THE WRONG PAIRING.
     The proof is correct, both bodies are independent, and the theorem is
     still a defect -- because the ARGUMENTS passed were the wrong ones.
     `olsEffectEstimationVariance_eq_haplotypeEffectEstimationVariance` was
     `sigma2/(n*varX) = sigma2/(n*f)`: true by `ring`, and reachable only by
     passing a haplotype FREQUENCY into a slot that wants a genotype VARIANCE.
     For a binary indicator the variance is `f*(1-f)`, and the missing `(1-f)`
     was measured at -50.4% at `f = 1/2`. The theorem was a cross-check that
     CERTIFIED the falsified identification.

     THE MECHANICAL ANSWER FOR D IS NOT MERELY ABSENT -- IT IS CONFIDENTLY
     AND SPECIFICALLY WRONG, IN THE SAFE-LOOKING DIRECTION. That is worse
     than a gap: a gap invites a reader to look, and a confident wrong
     answer does not. A `rfl` proof says the two sides reduce to the
     same term. IT SAYS NOTHING ABOUT WHETHER THE ARGUMENTS WERE THE RIGHT ONES
     TO PASS. The body-reference discriminator puts D in B -- independent
     bodies, equality is the claim -- and B is exactly the bucket labelled
     "do not delete". So D is the bucket where the mechanical answer is
     confidently wrong, and only checking each argument against the UNITS the
     slot expects will find it.

     `neiGstFromFrequencies_eq_hudsonFst` is the same disease at the level of
     NAMES; D is it at the level of ARGUMENT SLOTS.

  COLLAPSING B AND C INTO A IS HOW A GUARD GETS DELETED AS REDUNDANT, which is
  not hypothetical -- it is the failure this criterion was written to prevent.
  MISTAKING D FOR B IS THE OPPOSITE ERROR AND IS WORSE: it preserves, and
  thereby certifies, a wrong identification.

=== WORKED VERDICTS: THE POPGEN SLICE, 8 OF 8 ===

From the RFL scan in Check.lean at the elaborated environment, not from text.

  A (structural, nothing can drift) -- 2
    temporalMetricProfile_brier      the RHS, `temporalExactBrierRisk`, is
                                     DEFINED as the LHS. A name for a
                                     projection restated as a theorem.
    hetMutationRecurrence_zero       hand-written restatement of the base case
                                     Lean already generates as
                                     `hetMutationRecurrence.eq_1`, which the
                                     same scan found among the 11 generated.

  B (load-bearing, do not delete) -- 6
    neutralPortability_uses_ploidy      \
    temporalMetricProfile_r2         pins the profile's `r2` FIELD against the
                                     separately written `temporalR2`, argument
                                     order included; neither references the
                                     other, both wrap a common primitive
    ageDependentMetricProfile_r2     same shape
    temporalExactBrierRisk_eq_prevalence_scale
                                     asserts the profile's brier field IS the
                                     Bernoulli closed form pi(1-pi)(1-R2)

  C -- 0.   D -- 0.   E -- 0 in this slice.

  A PREDICTION ABOUT THIS LIST WAS MADE AND WAS WRONG, WHICH IS USEFUL: the
  other auditor expected two of the `_uses_ploidy` family to appear here,
  reasoning that the rest close by `unfold ...; ring`. The scan split the
  family correctly along that line without being told it existed.

=== THE BODY-REFERENCE TEST FAILS IN BOTH DIRECTIONS. IT HAS NO SAFE SIDE. ===

This is the most important caveat in the file and it was contributed by the
agent auditing the other half.

    D  is mechanically B, where the truth is "wrong pairing"  -> errs toward KEEP
    the ploidy family is mechanically A, where the truth is B -> errs toward DELETE

SO THE DISCRIMINATOR'S VERDICT CARRIES NO DIRECTIONAL SAFETY IN EITHER
DIRECTION. It cannot be used as "when in doubt it fails safe", because its two
known failure modes point opposite ways. It is a triage aid, never a decision.

REPLACEMENT TEST FOR CONVENTION-PINNING THEOREMS, which is cheaper and needs no
proof term at all:

    DOES THE DEFINITION INLINE THE CONSTANT, OR REFERENCE THE CONVENTION?

    inlines   -> the theorem is the LAST EDGE between the literal and the name,
                 and by the connectivity invariant a last edge is never
                 redundant however trivial its proof.  BUCKET B.
    references -> the theorem restates the definition.  BUCKET A.

Verified across the whole `_uses_ploidy` family: `neutralPortability` is
`r2_0 * max 0 (1 - 2 * fst)`, `pgsMean` sums `beta i * (2 * p i)`,
`fisherAverageEffect` is `a + d * (1 - 2 * p)`, `sharedLDRetention` is
`exp (-2 * recomb * t_div)`. NOT ONE OF THEM REFERENCES `ploidy`. Every one
inlines the literal, so every one of those theorems is a tripwire and none may
be collapsed.

=== A FIFTH FLAVOUR: ADVERTISING A HYPOTHESIS IT DOES NOT HAVE ===

  E. rfl-provable, TRUE, and CLAIMING A CONDITION THAT DOES NO WORK.
     `targetR2FromNeutralAFBenchmark_self` was documented as holding "at zero
     divergence". The equality holds at EVERY `fst`, because the definition IS
     `presentDayR2`. The docstring advertised a hypothesis the statement does
     not have, which is the same disease as a guard written `|se - se|`: a
     condition that appears to do work and does not.
     E is invisible to every test here because the defect is in the PROSE, not
     the term. Only reading the docstring against the statement finds it.

=== THE PLOIDY FAMILY REFINES THE DISCRIMINATOR, AGAINST MY OWN EXPECTATION ===

I expected the three `*_uses_ploidy` theorems to come out A -- "a definition
related to the convention it is built from" sounds structural. THEY ARE B, and
the reason is worth stating because it sharpens the test.

    neutralPortability r2_0 fst  =  r2_0 * max 0 (1 - 2 * fst)     -- LITERAL 2
    ploidy : R := 2
    neutralPortability_uses_ploidy : ... = r2_0 * max 0 (1 - ploidy * fst)

The definition does NOT reference `ploidy`. It hardcodes `2`. The theorem is
the ONLY thing tying that literal to the convention, so it is a tripwire: change
`ploidy` and it breaks, which is exactly the alarm wanted. Delete it and the
literal silently stops tracking the convention.

ITS TRIVIALITY IS WHAT MAKES IT WORK. `rfl` closes it because `ploidy` reduces
to `2` -- and that is the point, not a defect. A theorem can be trivial NOW and
be the only thing that would become FALSE later. "Provable by rfl" measures
today; "load-bearing" is a claim about what breaks tomorrow, and no proof-term
inspection can see that.

So the discriminator was right and my prior was wrong: it asks whether either
BODY references the other, and here neither does. The lesson is to run the test
rather than predict it -- I would have filed three guards under "safe to
collapse" on the strength of a plausible-sounding description.

=== ONE CASE THE BUCKETS DO NOT COVER, DECLARED RATHER THAN FORCED ===

  VACUOUS ON PURPOSE. `cluster_identities_hold_at_every_retention` is vacuous
  BY DESIGN: the property it flags is exactly the property being exhibited. It
  belongs in no bucket and must not be deleted for being in A. Where intent is
  the deciding fact and intent is not in the body, this refuses and says so.

=== ENUMERATION: USE the RFL scan in Check.lean, NOT THIS FILE'S TEXT SCAN ===

THE TEXT SCAN IN THIS FILE IS NOT TRUSTWORTHY AND ITS COUNTS MUST NOT BE USED.
Three text methods over the same nine modules returned 2, 16 and 3, with ZERO
overlap in theorem names between the last two. One classified `downstream` -- a
word occurring in prose -- as a theorem, and paired a theorem closed by
`apply mul_nonneg` with a conclusion belonging to a different declaration,
because a non-greedy regex spans declarations to reach the first `:= rfl` it
can find. Lean is whitespace-insensitive and its proofs are not a regular
language; no text scan recovers this reliably.

the RFL scan in Check.lean (this directory) asks the ELABORATED ENVIRONMENT instead, which
is the only authority: a theorem closes by `rfl` exactly when its proof term,
under its binders, is headed by `Eq.refl`. Run it with
`lake env lean validation/code/Check.lean`.

    hand-written rfl-closing theorems in the popgen slice:  8
    (19 raw, of which 11 are compiler-generated equation lemmas,
     sizeOf_spec and injEq, which are rfl by construction and written
     by nobody)

TWO CONTROLS EARNED THEIR KEEP WHILE BUILDING IT, and both produced a clean
null before firing:
  * The first version tested `ti.value.getAppFn` directly and returned 0 of 0.
    A theorem with binders stores its proof as `fun a b c => Eq.refl _`, so
    that asked whether a LAMBDA is `Eq.refl`, which is never true. A positive
    control on two theorems known to be written `:= rfl` refuted the zero
    immediately.
  * The unfiltered scan returned 19, which flattered the result until the
    generated names were separated out. Eleven of the nineteen are `f.eq_1`
    and friends.

AND THE SAME RE-DERIVATION IS OWED ON THE OTHER HALF. The candidate list this
criterion triages is built from numerically-sampled equivalence CLASSES plus a
`mentions` field parsed out of the sources by regex. The class side is
agreement at finitely many points, which is evidence toward "same function" and
NOT a proof -- only the converse is solid, that definitions in different classes
are definitely different, so NO DELETION MAY REST ON CLASS MEMBERSHIP ALONE.
The `mentions` side inherits the text parser's error rate, and the parser
reconciliation reports 101 disagreements including six dropped parameters in
multi-line signatures; a dropped parameter changes which definitions a
statement appears to mention. Lean knows definitional equality and it knows
what each statement mentions. Both halves should come from the environment.

=== A DEFERRED-WORK NOTE IS A CLAIM, NOT AN INSTRUCTION ===

It inherits the error rate of whatever produced it, and it is read by the next
sweep as a decision already taken. The specimen: a note in `Conventions.lean`
saying "the collapse to one name is the fix and has not been done" was written
from a name census before the bodies were read, survived three commits, and was
reversed by reading them -- `admixtureLDDecay` carries a VALIDATED regime and a
proved one-sided error bound that folding would detach from its name.

So a TODO in this corpus must carry its evidence and say what would overturn
it, like any other result. And when one is wrong, withdraw it IN PLACE quoting
what it said, rather than editing it away: the clean paragraph loses the fact
that a careful reader was misled there once.

=== AND A CONNECTIVITY RULE FOR ANY DELETION IN BUCKET A ===

A cluster of N spellings pinned pairwise can be collapsed to a hub with N-1
edges without losing the guard: a divergence between any two still fails some
proof. BUT THE INVARIANT IS CONNECTIVITY, NOT COUNT. Deleting the last edge to
a spelling disconnects it, and it can then drift freely with everything still
green. Before deleting a pairwise theorem, check that BOTH endpoints remain
reachable from the hub.

Verified on the live corpus: deleting `ldDecayPerGeneration_eq_
discreteRecombinationSurvival` and `..._eq_admixtureLDDecay` was SAFE, because
`geometricDecay` still carries three spokes in Conventions.lean and all four
spellings stay connected. That deletion was sound; the check is what shows it,
not the count.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
# parents[3] from the FILE, matching extract_defs.py/theorems.py/structures.py
# beside it. `HERE.parent.parent` is validation/, one level short of the corpus.
CALIB = pathlib.Path(__file__).resolve().parents[3] / "Descent"

# The population-genetics slice. Split by MODULE, not by list position: a
# tautology audit needs the surrounding file open, and two agents in one file
# is how the sweeps collided.
MINE = ["LDDecayTheory", "Conventions", "PopulationGeneticsFoundations",
        "DemographicHistory", "DriftRegime", "LongitudinalPortability",
        "HumanDemography", "AncestrySpecificArchitecture",
        "AncestrySpecificPower"]

# `theorem NAME (binders) : LHS = RHS := by rfl` / `:= rfl` / `:= by\n  rfl`.
#
# THE FIRST VERSION OF THIS ANCHORED `rfl` TO END-OF-LINE and found 2 theorems
# where a whitespace-flattened count finds 16 -- an eight-fold undercount that
# looked like a clean result. Caught by running the same question a second way
# and requiring the two to agree, which is the rule this file's own criterion
# states. Lean puts `rfl` on its own line as often as not, so the source is
# flattened before matching and line structure is never load-bearing here.
THM = re.compile(
    r"\btheorem\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(.*?):=\s*(?:by\s+)?rfl\b")

# A NON-GREEDY MATCH STILL SPANS DECLARATIONS. `(.*?)` will happily run from
# one theorem's name, past its own proof and several later declarations, to the
# first `:= rfl` it can find -- so a theorem closed by `apply mul_nonneg` gets
# paired with a conclusion belonging to something else entirely. That produced
# 16 matches of which every verdict was attached to the wrong theorem, and it
# included `downstream`, a word from prose that is not a declaration at all.
# Any candidate whose captured statement contains another declaration keyword
# is therefore discarded.
DECL_KEYWORD = re.compile(
    r"\b(theorem|lemma|def|abbrev|instance|structure|inductive|example)\b")


def flatten(text):
    """Collapse newline+indent to a single space; Lean wraps statements freely."""
    return re.sub(r"[ \t]*\n[ \t]*", " ", text)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
KEYWORDS = {"by", "rfl", "theorem", "fun", "let", "if", "then", "else",
            "forall", "exists", "Type", "Prop", "Real", "ℝ", "ℕ"}


def _depth_split(text, wanted):
    """Indices of `wanted` at bracket depth 0."""
    out, d = [], 0
    for i, ch in enumerate(text):
        if ch in "([{":
            d += 1
        elif ch in ")]}":
            d -= 1
        elif ch == wanted and d == 0:
            out.append(i)
    return out


def conclusion(stmt):
    """The part after the LAST top-level `:`.

    Splitting on the FIRST colon takes a binder ascription -- `(r : R)` -- and
    calls it the conclusion. That dropped 13 of 16 candidates here while
    looking like a clean result, which is the same undercount the flattening
    fix already caught once in this file.
    """
    cuts = _depth_split(stmt, ":")
    if not cuts:
        return None
    return stmt[cuts[-1] + 1:]


def top_level_eq(concl):
    """(lhs, rhs) if the conclusion is one equality at depth 0, else None.

    Hypotheses and nested equalities live inside brackets or behind arrows; a
    conclusion with an implication is not a bare identity and is refused rather
    than guessed at.
    """
    if "->" in concl or "\u2192" in concl:
        return None
    cuts = [i for i in _depth_split(concl, "=")
            if concl[i - 1] not in "<>!:" and concl[i + 1: i + 2] != "="]
    if len(cuts) != 1:
        return None
    return concl[:cuts[0]], concl[cuts[0] + 1:]


def bodies():
    """{short name: body} from the generated table, if it is present."""
    p = HERE.parent / "extract" / "defs.json"
    if not p.exists():
        return None
    blob = json.loads(p.read_text())
    return {d["short"]: (d.get("body") or "") for d in blob["definitions"]}


def heads(expr):
    """Identifiers appearing in one side of the equality."""
    return [t.split(".")[-1] for t in IDENT.findall(expr)
            if t.split(".")[-1] not in KEYWORDS]


def classify(lhs, rhs, defbodies):
    """A / B / REFUSE, from the bodies alone."""
    l, r = heads(lhs), heads(rhs)
    if not l or not r:
        return "REFUSE", "could not identify both sides"
    known = [n for n in set(l + r) if n in defbodies]
    if len(known) < 2:
        return "REFUSE", "fewer than two sides resolve to definitions"
    # Does either body reference the other definition?
    for a in known:
        for b in known:
            if a == b:
                continue
            if re.search(r"\b%s\b" % re.escape(b), defbodies[a]):
                return "A", f"{a}'s body references {b}: structural"
    return "B", f"{'/'.join(sorted(known)[:2])}: independent bodies, equality is the claim"


def main(argv):
    db = bodies()
    if db is None:
        raise SystemExit(
            "rfl_triage: extract/defs.json is missing. It is generated and\n"
            "  untracked -- regenerate:\n"
            "      python3 validation/empirical/extract/emit.py")
    tally, rows = {}, []
    for mod in MINE:
        f = CALIB / (mod + ".lean")
        if not f.exists():
            continue
        text = flatten(f.read_text())
        for m in THM.finditer(text):
            name, stmt = m.group(1), m.group(2)
            if DECL_KEYWORD.search(stmt):
                continue          # the match ran past its own declaration
            concl = conclusion(stmt)
            if concl is None:
                tally["REFUSE"] = tally.get("REFUSE", 0) + 1
                rows.append((mod, name, "REFUSE",
                             "could not isolate the conclusion"))
                continue
            eq = top_level_eq(concl)
            if eq is None:
                tally["REFUSE"] = tally.get("REFUSE", 0) + 1
                rows.append((mod, name, "REFUSE",
                             "conclusion is not a single top-level equality"))
                continue
            lhs, rhs = eq
            verdict, why = classify(lhs, rhs, db)
            tally[verdict] = tally.get(verdict, 0) + 1
            rows.append((mod, name, verdict, why))
    print(f"{'module':32s} {'theorem':46s} {'':1s} why")
    for mod, name, v, why in rows:
        print(f"{mod[:32]:32s} {name[:46]:46s} {v:1s} {why[:60]}")
    print()
    for k in ("A", "B", "REFUSE"):
        print(f"  {tally.get(k,0):4d}  {k}")
    print("\nA = structural (one body references the other), safe to collapse")
    print("B = independent bodies; the theorem IS the guard, do NOT delete")
    print("REFUSE = not decidable from bodies; needs reading, and is reported")
    print("         rather than assigned a bucket")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

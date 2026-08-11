# PRE-REGISTRATION: does the two-locus LD correlation inherit the one-locus
# isolation-by-distance operator in two dimensions?
#
# Filed by ld-deriver BEFORE reading any 4x4 or 5x5 output. At filing time the only
# lattice results in existence are the 3x3 ones (two distances, zero degrees of
# freedom against a two-parameter form, therefore uninformative by construction and
# already declared so). The command that writes this file also prints the current
# tail of ld2d.log so the record shows what had and had not been produced.

## THE HYPOTHESIS UNDER TEST

H1 (INHERITANCE). The equilibrium cross-deme LD correlation rD on a stepping-stone
lattice is governed by the Green's function of a screened random walk whose killing
rate is fixed by (rho, M) locally. The dimension enters ONLY through the Green's
function. Consequences: rD(d) proportional to lambda^d in 1-D (already confirmed to
6% by the exact chain solutions), and rD(r) proportional to K_0(r/L) in 2-D, with L
THE SAME in both geometries at the same (rho, M) -- legitimate because a block hops
at M/2 to each of two AXIAL neighbours in both, so the per-axis diffusion is equal.

H0 (NO INHERITANCE). The two-locus object is not governed by that operator; the 2-D
shape and/or its decay length are unrelated to the 1-D one.

## THE TWO CRITERIA, AND WHERE EACH TOLERANCE COMES FROM

(a) SHAPE. Fitting A*K_0(d/L), two free parameters, to the exact rD at all Manhattan
    distances available from the measurement deme, the maximum relative residual must
    be <= 6%.
    PROVENANCE OF 6%: it is the tolerance the 1-D geometric candidate was granted and
    reported at (max 6% over d=1..3, rho in [0.5,20], both M values). Holding the 2-D
    candidate to the standard already applied to its 1-D sibling is the only choice
    here that is not chosen after the fact. It is NOT derived from solve precision,
    which is irrelevant at this scale: spsolve on these systems is accurate to ~1e-10
    relative, so every residual above 1e-8 is model error, not numerical error.

(b) DECAY LENGTH, the parameter-free half. The L fitted in (a) must match the 1-D
    implied L = -1/ln(rD_01) at the SAME (rho, M) to within 15%.
    TARGETS, computed and recorded before this filing, from the exact chain solutions:
      M = 3.6  : L = 2.3292 (n=3) / 2.2779 (n=4) at rho=1 ; 1.0592 / 1.0528 at rho=5 ;
                 0.5571 / 0.5574 at rho=20
      M = 12   : L = 5.8018 / 5.3249 at rho=1 ; 2.1615 / 2.0501 at rho=5 ;
                 0.9406 / 0.9327 at rho=20
    PROVENANCE OF 15%: the 1-D target is itself only pinned to about 8% by finite
    chain length (worst case 5.8018 vs 5.3249, M=12 rho=1, an 8.2% spread between
    n=3 and n=4). A match tolerance cannot be tighter than the uncertainty in the
    thing being matched, so 15% is that 8% with room for the 2-D lattice's own
    finite-size error. It is far tighter than the scale on which the alternative
    already failed: the geometric law missed by 26-57% at d=2.
    Only the 2-D fits at M = 3.6 are in scope; the M = 12 targets are recorded for a
    later chain-geometry run and are not being tested now.

## THE THREE OUTCOMES, DECLARED IN ADVANCE

PASS      (a) and (b) both hold. The 2-D LD law has a parameter-free anchor: L comes
          from the 1-D solve and only the amplitude is free. Goes to custody scoring
          before any Lean body is written. Nothing is written on the strength of this
          file alone.
RULED OUT (a) holds, (b) fails. The K_0 SHAPE describes the data but with a decay
          length unrelated to the 1-D one, so the two-locus object does not inherit
          the one-locus operator. That is a mechanism ruled out, which is a result,
          and the slot stays named slack with H1 struck.
FAIL      (a) fails. K_0 does not describe the 2-D decay at all. Slot stays named
          slack; both candidate shapes (geometric and Bessel) are then dead.

## THE INCONCLUSIVE BRANCH, DECLARED NOW SO IT CANNOT BE INVENTED LATER

These lattices are small and have reflecting boundaries, which distorts a Green's
function near the edge; a 4x4 has no true centre, so the measurement deme sits
off-centre and the far distances are boundary-dominated. If the L fitted on 4x4 and
the L fitted on 5x5 differ from EACH OTHER by more than 15%, the lattices are too
small for the asymptotic form to be visible and the run is INCONCLUSIVE rather than
a FAIL -- a larger lattice is then required and no verdict is recorded. This branch
is available ONLY on that stated internal-consistency test. It is not available on
the basis of residuals looking large, and it does not apply to criterion (b): a
stable-but-mismatched L is a RULED OUT, not an inconclusive.

## WHAT WOULD MAKE THIS FILING WORTHLESS

Reading the 4x4 or 5x5 numbers before it is written. It is being written now, with
the solves still running and nothing past the 3x3 block in the log.

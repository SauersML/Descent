"""Simulation-engine adapters for the cross-engine differential harness.

Every empirical verdict in this corpus before this harness was produced by
msprime, a coalescent simulator.  That is a single point of failure twice over:
msprime's modelling assumptions (neutrality, the coalescent approximation) are
baked into every verdict, and most of the false verdicts this project has
caught came from misusing msprime's API, which a second engine with a different
API cannot reproduce in the same way.

An engine here is a small object that declares WHAT IT CAN SIMULATE.  A claim
about selection may not be answered by an engine whose `selection` capability
is False -- that is the whole point of the registry, and it is why adding a
third engine is a class, not a rewrite.

ENVIRONMENT: see README.md in this directory for how each engine was obtained,
with versions.  Nothing here runs on a laptop; all of it runs on the cluster.
"""

from __future__ import annotations

import math
import os
import subprocess
import tempfile

# Overridable so the harness is not pinned to one person's cluster paths.
SLIM_BIN = os.environ.get(
    "XSIM_SLIM", "/projects/standard/hsiehph/sauer354/xsim/build/slim")

GUARD = "XSIM_CE_V1"          # freshness token: present only in THIS source

# Total recombination map length, in Morgans, for the neutrality control.
# NOT free recombination: 0.5 per base over a 2 kb region is ~10^9 crossovers
# per run and every engine chokes on it.  Recombination changes the VARIANCE of
# per-site diversity, not its expectation, so a couple of Morgans is all the
# control needs -- and it keeps the three engines on identical genetics.
MAP_LENGTH = 2.0


class EngineUnavailable(RuntimeError):
    """The engine is not installed here.  Loud, never silently skipped."""


class Engine:
    """Base adapter.

    `kind` is the discriminating property, not the name: a claim validated only
    by engines of kind "coalescent" has never met a forward simulator, and
    `provenance.py` reads exactly that field.
    """

    name = "abstract"
    kind = "abstract"           # "coalescent" | "forward"
    selection = False           # can it simulate natural selection?
    finite_population = False   # does it realise drift in a finite N?
    biallelic_locus = False     # can it model ONE two-allele locus exactly,
                                # rather than emulating it with infinite sites?
    version = "unknown"

    def carrier_frequency(self, cell, seed):
        """Time-averaged frequency of a deleterious allele at one biallelic site.

        The observable is CARRIER frequency -- the fraction of gametes carrying
        at least one copy -- not the sum of infinite-sites mutation
        frequencies.  Under recurrent forward mutation the two differ: summed
        frequencies double-count a gamete that has been hit twice and can
        exceed 1 outright once the site fixes, which is precisely the regime
        this harness is aimed at.  Carrier frequency is also the observable the
        corpus recursion actually models, since its `mu * (1 - p)` term creates
        new carriers only out of non-carriers.
        """
        raise NotImplementedError

    def neutral_diversity(self, N, mu, L, seed):
        """Per-site nucleotide diversity at neutral freely-recombining sites.

        The neutrality control.  Every engine must return 4*N*mu here; a
        disagreement means the harness is broken, not the corpus.
        """
        raise NotImplementedError


# --------------------------------------------------------------------- SLiM
# A TRUE BIALLELIC LOCUS, not an infinite-sites emulation of one.
#
# Emulating a single two-allele locus by a one-base infinite-sites region is
# wrong wherever dominance is not additive, and the failure is silent.  Two
# gametes carrying DIFFERENT mutation objects at the same position make a
# compound heterozygote: in the biallelic model that individual is a mutant
# HOMOZYGOTE and takes the full 1 - s, but under per-mutation fitness it is
# heterozygous at two separate sites and takes (1 - h*s)^2.  At h = 0 those are
# 1 - s and 1 -- recessive homozygotes stop being selected at all, the measured
# frequency inflates, and the inflation GROWS with N because more distinct
# mutations segregate.  At h = 1/2 the two agree to O(s^2), which is why the
# additive cells are unaffected.
#
# So per-mutation fitness is switched off and the genotype's fitness is computed
# from the CARRIER COUNT across the individual's two genomes: 1, 1 - h*s, 1 - s.
_SLIM_MSB = """// {guard}
initialize() {{
	initializeMutationRate({mu!r});
	initializeMutationType("m2", {h!r}, "f", {negs!r});
	m2.convertToSubstitution = F;
	initializeGenomicElementType("g1", m2, 1.0);
	initializeGenomicElement(g1, 0, 0);
	initializeRecombinationRate(0);
}}
mutationEffect(m2) {{ return 1.0; }}
fitnessEffect() {{
	g = individual.genomes;
	k = sum(asInteger(g.countOfMutationsOfType(m2) > 0));
	if (k == 0) return 1.0;
	if (k == 1) return 1.0 - {h!r} * {s!r};
	return 1.0 - {s!r};
}}
1 early() {{ sim.addSubpop("p1", {N}); }}
{t0}:{t1} late() {{
	if (community.tick % {every} == 0) {{
		g = p1.genomes;
		catn("SAMPLE " + mean(asFloat(g.countOfMutationsOfType(m2) > 0)));
	}}
}}
{t1} late() {{ catn("{guard}"); }}
"""

_SLIM_NEUTRAL = """// {guard}
initialize() {{
	initializeMutationRate({mu!r});
	initializeMutationType("m1", 0.5, "f", 0.0);
	initializeGenomicElementType("g1", m1, 1.0);
	initializeGenomicElement(g1, 0, {Lm1});
	initializeRecombinationRate({rho!r});
}}
1 early() {{ sim.addSubpop("p1", {N}); }}
{gens} late() {{
	f = sim.mutationFrequencies(p1);
	catn("PI " + sum(2 * f * (1 - f)) / {L});
	catn("{guard}");
}}
"""


class SLiM(Engine):
    """SLiM 4.3, forward and individual-based, scripted in Eidos.

    A different language, a different process model and a different author from
    everything else in this repository's validation tree.
    """

    name = "slim"
    kind = "forward"
    selection = True
    finite_population = True
    biallelic_locus = True      # via the fitnessEffect() callback above

    def __init__(self, binary=None):
        self.binary = binary or SLIM_BIN
        if not os.path.exists(self.binary):
            raise EngineUnavailable(f"slim not found at {self.binary}")
        out = subprocess.run([self.binary, "-v"], capture_output=True, text=True)
        self.version = out.stdout.strip().split("\n")[0] or "slim"

    def _run(self, src, seed):
        with tempfile.NamedTemporaryFile("w", suffix=".slim", delete=False) as fh:
            fh.write(src)
            path = fh.name
        try:
            out = subprocess.run([self.binary, "-s", str(seed), path],
                                 capture_output=True, text=True, timeout=7200)
            # An instrument that cannot report its own absence will report
            # someone else's answer as its own.
            if GUARD not in out.stdout:
                raise RuntimeError(
                    "STALE/FAILED slim run: "
                    f"{out.stdout[-400:]} {out.stderr[-400:]}")
            return out.stdout
        finally:
            os.unlink(path)

    def carrier_frequency(self, cell, seed):
        src = _SLIM_MSB.format(guard=GUARD, mu=cell["MU"], h=cell["H"],
                               s=cell["S"], negs=-cell["S"], N=int(cell["N"]),
                               t0=int(cell["T0"]), t1=int(cell["T1"]),
                               every=int(cell.get("EVERY", 10)))
        vals = [float(l.split()[1]) for l in self._run(src, seed).splitlines()
                if l.startswith("SAMPLE")]
        if not vals:
            raise RuntimeError("slim: no samples")
        return sum(vals) / len(vals)

    def neutral_diversity(self, N, mu, L, seed):
        src = _SLIM_NEUTRAL.format(guard=GUARD, mu=mu, N=N, L=L, Lm1=L - 1,
                                   rho=MAP_LENGTH / L, gens=10 * N)
        line = [l for l in self._run(src, seed).splitlines()
                if l.startswith("PI ")]
        return float(line[0].split()[1])


# ------------------------------------------------------------------ fwdpy11
class Fwdpy11(Engine):
    """fwdpy11, forward and individual-based, C++ core driven from Python.

    Independent of SLiM: different code base, different random number library
    (GSL), different genetic-value machinery.
    """

    name = "fwdpy11"
    kind = "forward"
    selection = True
    finite_population = True

    def __init__(self):
        try:
            import fwdpy11
        except ImportError as e:
            raise EngineUnavailable(f"fwdpy11 not importable: {e}")
        self._f = fwdpy11
        self.version = fwdpy11.__version__

    def carrier_frequency(self, cell, seed):
        import numpy as np           # noqa: F401  (kept for parity/debugging)
        f = self._f
        N, mu, s, h = int(cell["N"]), cell["MU"], cell["S"], cell["H"]
        t0, t1 = int(cell["T0"]), int(cell["T1"])
        every = int(cell.get("EVERY", 10))
        # Continuous positions with NO recombination emulate one biallelic
        # site: every mutation in the region sits on the same non-recombining
        # unit, so a gamete carrying any of them is a carrier.
        pop = f.DiploidPopulation(N, 1.0)
        rng = f.GSLrng(seed)
        params = f.ModelParams(
            nregions=[], sregions=[f.ConstantS(0, 1.0, 1.0, -s, h, scaling=1.0)],
            recregions=[], rates=(0.0, mu, None),
            # SCALING MUST BE 1.0, NOT THE IDIOMATIC 2.0.  fwdpy11's
            # Multiplicative(scaling) gives genotype fitnesses 1, 1 + h*s,
            # 1 + scaling*s, while SLiM's mutation with selection coefficient s
            # and dominance h gives 1, 1 + h*s, 1 + s.  At scaling=2.0 the two
            # engines agree on heterozygotes and differ by a factor of two on
            # homozygotes.  That is invisible for a nearly-dominant allele at
            # low frequency -- homozygotes are ~p^2 -- and it is the ENTIRE
            # selective force on a recessive one, where it moved the answer by
            # a factor of 1.5 to 1.9 and made the two engines disagree at 9
            # sems.  Caught by the neutrality-control rule: two forward
            # simulators of the same model must agree, so a disagreement is the
            # harness, not the corpus.
            gvalue=f.Multiplicative(1.0),
            demography=f.ForwardDemesGraph.tubes([N], burnin=t1,
                                                 burnin_is_exact=True),
            simlen=t1, prune_selected=False)
        acc = []

        class Rec:
            def __call__(self, pop, sampler):
                if pop.generation >= t0 and pop.generation % every == 0:
                    carr = sum(g.n for g in pop.haploid_genomes
                               if g.n > 0 and len(g.smutations) > 0)
                    acc.append(carr / (2.0 * pop.N))

        f.evolvets(rng, pop, params, 100, recorder=Rec(),
                   suppress_table_indexing=True)
        if not acc:
            raise RuntimeError("fwdpy11: no samples")
        return sum(acc) / len(acc)

    def neutral_diversity(self, N, mu, L, seed):
        import msprime
        f = self._f
        pop = f.DiploidPopulation(N, float(L))
        rng = f.GSLrng(seed)
        params = f.ModelParams(
            nregions=[], sregions=[],
            recregions=[f.PoissonInterval(0, float(L), MAP_LENGTH)],
            rates=(0.0, 0.0, None), gvalue=f.Multiplicative(2.0),
            demography=f.ForwardDemesGraph.tubes([N], burnin=10 * N,
                                                 burnin_is_exact=True),
            simlen=10 * N)
        f.evolvets(rng, pop, params, 100, suppress_table_indexing=True)
        ts = msprime.sim_mutations(pop.dump_tables_to_tskit(), rate=mu,
                                   random_seed=seed + 1, discrete_genome=True)
        return ts.diversity(span_normalise=True)


# ------------------------------------------------------------------ msprime
class Msprime(Engine):
    """msprime, the coalescent engine every prior verdict in this corpus used.

    Carried here as the incumbent, and to anchor the neutrality control.  It
    cannot answer a question about selection, and `selection = False` is how
    the harness refuses to let it pretend otherwise.
    """

    name = "msprime"
    kind = "coalescent"
    selection = False
    finite_population = False

    def __init__(self):
        try:
            import msprime
        except ImportError as e:
            raise EngineUnavailable(f"msprime not importable: {e}")
        self._m = msprime
        self.version = msprime.__version__

    def neutral_diversity(self, N, mu, L, seed):
        m = self._m
        ts = m.sim_ancestry(samples=N, population_size=N, sequence_length=L,
                            recombination_rate=MAP_LENGTH / L, random_seed=seed,
                            discrete_genome=True)
        ts = m.sim_mutations(ts, rate=mu, random_seed=seed + 1,
                             discrete_genome=True)
        return ts.diversity(span_normalise=True)


REGISTRY = {"slim": SLiM, "fwdpy11": Fwdpy11, "msprime": Msprime}


def load(names):
    """Instantiate engines by name.  An unavailable engine raises; it is never
    quietly dropped, because a harness that skips an engine and still prints a
    verdict has just reported a single-engine result as a cross-engine one."""
    out = []
    for n in names:
        if n not in REGISTRY:
            raise KeyError(f"unknown engine {n!r}; have {sorted(REGISTRY)}")
        out.append(REGISTRY[n]())
    return out


def sem(xs):
    n = len(xs)
    if n < 2:
        return float("nan")
    m = sum(xs) / n
    v = sum((x - m) ** 2 for x in xs) / (n - 1)
    return math.sqrt(v / n)

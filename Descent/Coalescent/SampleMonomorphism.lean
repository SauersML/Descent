/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Duality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

namespace Coalescent

/-!
# When a sample loses its variation: block counting on the dual side

`Descent.Coalescent.Duality` proves the generator identity -- the Wright-Fisher diffusion
applied to `xᵐ` reproduces the coalescent's death rates -- and its own docstring already says
that the number of ancestral lineages is a pure death process with rates `d_k = k(k-1)/2`.
This file writes down the transition law of that process and the one observable it was
missing.

**The law.** For a neutral variant at frequency `p` when two branches part, the probability
that a sample of `n` haplotypes drawn from one branch is MONOMORPHIC after scaled time `τ`:

    P(mono | p, n, τ) = Σ_{k=1}^{n} P(N_τ = k | N_0 = n) · (pᵏ + (1-p)ᵏ)

`N_τ` is Kingman's block count. The step is moment duality, `E[X_τᵐ | X_0 = p] =
E[p^{N_τ} | N_0 = m]`, which is EXACT for the Wright-Fisher diffusion: no moment closure, no
distributional assumption, and no fitted quantity anywhere. The sample is monomorphic exactly
when all `N_τ` ancestral lineages carry the same allele, and conditionally on the ancestral
frequency the lineages are exchangeable draws, which is where `pᵏ + (1-p)ᵏ` comes from.

**The clock, named in the type.** `tau` is `t / (2 Nₑ)`, with `2 Nₑ` the number of GENE
COPIES. Tavaré's `N` is the copy count, so reading it as the diploid size halves `τ`, and
that is not a rounding error: it moves the block-count distribution by 0.30 to 0.45. The
argument is called `tau` rather than `t` so the wrong reading has no name to hide behind, and
the corpus has a MEASURED rejection of it rather than only this paragraph -- the halved-clock
form is a competing entry in both batteries below, falsified at 52.97 and 9.14 sems.

**Sources.** Tavaré (1984) for the duality and the transition law; Chen & Chen (2013),
PMC3697976, equation 15 for the closed form written in `blockCountLaw`.

**Stating is not computing, and this file states.** The closed form is an alternating sum
with factorial-scale terms. It is the right way to SAY what the law is and the wrong way to
EVALUATE it: at `n = 200` in double precision it loses its precision entirely to
cancellation, while a uniformization has no subtraction anywhere and stays a sub-probability
vector at every partial sum. The two agree to 1e-12 at the relevant times. Nobody should
"optimise" a numerical consumer onto this definition.

## What this law is licensed for

ONE population, and an initial condition carried FORWARD. It does NOT cover the structured or
migration case, whose block counting runs over deme configurations and is underived here. It
does NOT cover the downstream-observation object -- conditioning on the present, which is what
real data and a coalescent simulator both hand you. Those are separate derivations and
neither is started.

## The sibling it is not, and where the comparison has to live

`Portability.stillSegregatingProb` is a DIFFERENT OBJECT: the probability a variant is still
segregating IN THE POPULATION, Kimura's eigenfunction solution, whose signature carries no
sample size at all. A variant can be segregating in the population and absent from a sample.
The honest relation is a BOUND -- sample-segregating implies population-segregating -- and it
CANNOT BE STATED HERE: `stillSegregatingProb` lives above this layer, and the `assert_below`
lines at the top of this file are what stop the arrow being drawn the wrong way. The bound
belongs in the Portability layer beside its other operand, and it is owed. Two things it will
need: a clock conversion, since that body takes `t : ℕ` in generations while this one takes
real `τ`, and the range facts named as owed below.
-/

/-- **Kingman's block-counting transition law**: `P(N_τ = k | N_0 = n)`, in closed form.

Chen & Chen (2013) equation 15, equivalently Tavaré (1984): a sum over the number `j` of
lineages whose exponential term survives, with the death rate of `j` lineages supplied by
`deathRate` rather than restated, so the exponent here and the coalescent's rates elsewhere
in this group cannot drift apart.

The falling factorial `n.descFactorial j` is `n(n-1)···(n-j+1)` and the rising factorials
`k.ascFactorial (j-1)` and `n.ascFactorial j` are `k(k+1)···(k+j-2)` and `n(n+1)···(n+j-1)`;
those are Mathlib's conventions and they are the ones this formula wants.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a transition law derived from the death rates
    this group already carries, and a distribution rather than a statement about a
    population. What has observable content is the consumer below, which turns it into a
    prediction about a sample, and that is where the battery is.

Junk outside its domain, and stated rather than left to be discovered: for `k > n` the index
set is empty and the sum is `0`, which is the right value, since a sample of `n` cannot have
more than `n` ancestors. At `k = 0` the formula is evaluated outside the range the derivation
covers and no consumer here supplies it. -/
noncomputable def blockCountLaw (n k : ℕ) (tau : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k n,
    Real.exp (-(deathRate j * tau)) * (2 * (j : ℝ) - 1) * (-1 : ℝ) ^ (j - k) *
        ((k.ascFactorial (j - 1) : ℝ) * (n.descFactorial j : ℝ)) /
      ((k.factorial : ℝ) * ((j - k).factorial : ℝ) * (n.ascFactorial j : ℝ))

/-- **The probability that a sample of `n` haplotypes is monomorphic**, `τ` in units of
`2 Nₑ` generations after the branches parted at ancestral frequency `p`.

This is the quantity a scored tag actually loses when it stops varying in the target sample,
and it is what an analysis pricing tag loss off a population-level quantity is approximating.

    Empirical status: VALIDATED against simulated Wright-Fisher drift
    (`simcov/battery_fix36.py`, `simcov/battery_fix36b.py`), and read the next paragraph for
    what that does and does not cover.

    `battery_fix36`: MATCH at worst 2.19 sems and 1.48% relative over fourteen admitted
    cells, `competitors_rejected: 2`. One cell excluded by a readability rule fixed in
    advance (`p = 0.50`, `t = 250`, predicted 2.9e-6) and printed with its prediction rather
    than dropped. Two competing forms FALSIFIED on the same cells: the Balding-Nichols beta
    closure at 47.40 sems and the halved-clock reading at 52.97 sems. Positive control --
    pure sampling at `t = 0`, with no coalescent content in it -- at 0.67 sems. The beta
    closure's failure is worst at small `τ`, a diagnostic signature recorded BEFORE the data
    existed and reproduced by it.

    `battery_fix36b`, a sample-size sweep at `n` = 20, 50, 100 and 200: MATCH at worst 1.22
    sems, `competitors_rejected: 4`. It falsifies the population-fixation reading at 7.21
    sems, the beta closure at 8.33, the halved clock at 9.14, and the no-drift `τ = 0`
    reading at 29.67.

    Power: the prediction spans 0.00255 to 0.95123 across `battery_fix36`'s thirty-two
    cells and 0.04739 to 0.79181 across `battery_fix36b`'s twenty-four. A monomorphism
    probability has nowhere to hide in that range: a design confined to the tails would
    admit almost any curve through it, and this one crosses from a sample that has almost
    certainly kept its variation to one that has almost certainly lost it.

    WHAT THE MATCH COVERS. It validates this law AGAINST SIMULATED DRIFT. The two statements
    below are separate and both are true.

    The sample-versus-population distinction is MEASURED, not asserted -- and what is
    measured is a MAGNITUDE rather than a direction. The sign was never available as a
    finding: a fixed population makes every sample drawn from it monomorphic, so the
    sample-monomorphic event CONTAINS the population-fixed one site by site and the
    difference is non-negative in every realisation. What is under test is ADEQUACY AS AN
    APPROXIMATION, and that is `n`-dependent. Every cell where the two are separable at all
    sits at `n` = 20 or `n` = 50 -- 7.21 and 5.16 sems unascertained at `t` = 250, 6.00 and
    3.20 ascertained, 5.69 at `t` = 750 -- and the sweep places none at `n` = 100 or 200,
    because by there the gap has shrunk below what these site counts can read. So the
    substantive claim is unchanged and is now measured rather than argued: the sample
    quantity is the correct object, the population quantity is its `n → ∞` limit, and it
    remains an adequate approximation at the large samples this law is meant to serve.

    The validated REGIME is extended by that sweep: `n` = 20, 50 and 100 had no verdict
    before it and all pass. Only `n` = 200 had one previously.

    THE BETA CLOSURE'S REFUTATION IS `n`-DEPENDENT and must not be quoted flat. It misses by
    47 sems at `n` = 200 and by 7.82 sems at `t` = 2000 in the sweep, but at `n` = 20 it sits
    0.35 sems from the measurement and is indistinguishable from this law. The reason is
    structural -- the beta's defect is its missing atoms at 0 and 1, and at small `n` the
    sampling term dominates the atom term. The two rivals therefore fail at OPPOSITE ENDS of
    the sample-size axis: small `n` rejects the population reading and cannot reject the
    beta, large `n` rejects the beta and cannot reject the population reading. Neither sample
    size alone discriminates both, which is why the sweep spans the range, and that structure
    was filed before the counts existed.

    argument_source: derived. -/
noncomputable def tagSampleMonomorphicProb (p : ℝ) (n : ℕ) (tau : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, blockCountLaw n k tau * (p ^ k + (1 - p) ^ k)

/-- **A variant and its complement are the same variant.** Reading the sample from the other
allele exchanges `p` and `1 - p` and cannot change whether it is monomorphic. This mirrors
`Portability.stillSegregatingProb_symm`, which says the same thing about the population
quantity; that the two symmetries hold separately is one check that the objects are the pair
they are claimed to be. -/
theorem tagSampleMonomorphicProb_symm (p : ℝ) (n : ℕ) (tau : ℝ) :
    tagSampleMonomorphicProb (1 - p) n tau = tagSampleMonomorphicProb p n tau := by
  unfold tagSampleMonomorphicProb
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [show (1 : ℝ) - (1 - p) = p by ring]
  ring

/-- **One lineage, all the time.** A sample of one has a single ancestor at every time, so
the closed form must collapse to `1` -- and it does, through `deathRate_one`. -/
@[simp] theorem blockCountLaw_one_one (tau : ℝ) : blockCountLaw 1 1 tau = 1 := by
  rw [blockCountLaw, Finset.Icc_self, Finset.sum_singleton, deathRate_one]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.descFactorial_succ,
    Nat.descFactorial_zero, Nat.factorial]

/-- **A sample of one is always monomorphic**, which it is by the meaning of the word rather
than by any property of drift. The body returning anything else would be a defect in the
sum's index set, and this is the statement that would catch it. -/
theorem tagSampleMonomorphicProb_sample_one (p tau : ℝ) :
    tagSampleMonomorphicProb p 1 tau = 1 := by
  rw [tagSampleMonomorphicProb, Finset.Icc_self, Finset.sum_singleton, blockCountLaw_one_one]
  ring

/-- **Two lineages survive with probability `exp (-τ)`.** The pair coalesces at rate one --
`deathRate_two` -- so this is the exponential holding time and nothing else. -/
@[simp] theorem blockCountLaw_two_two (tau : ℝ) :
    blockCountLaw 2 2 tau = Real.exp (-tau) := by
  rw [blockCountLaw, Finset.Icc_self, Finset.sum_singleton, deathRate_two]
  -- `norm_num` evaluates the factorials and the index arithmetic but leaves
  -- `exp (-tau) * 3 * 4 / 12`: it does not cancel a numeral division against a
  -- transcendental factor, which is `ring`'s job rather than a normalisation's.
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.descFactorial_succ,
    Nat.descFactorial_zero, Nat.factorial]
  ring

/-- **Two lineages have coalesced with the complementary probability.** Stated separately
because it is where the closed form's alternating sum actually does something: the `j = 1`
and `j = 2` terms are `1` and `-exp (-τ)`, and the cancellation between them is the whole
mechanism the formula's factorial coefficients exist to arrange. -/
@[simp] theorem blockCountLaw_two_one (tau : ℝ) :
    blockCountLaw 2 1 tau = 1 - Real.exp (-tau) := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [blockCountLaw, hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), deathRate_one,
    deathRate_two]
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.descFactorial_succ,
    Nat.descFactorial_zero, Nat.factorial]
  ring

/-- **The pair case in closed form**: `P = 1 - 2p(1-p)exp(-τ)`.

This is a genuine consistency theorem rather than a restatement of the definition. The
right-hand side is derivable from the pair coalescence probability ALONE, without the
block-counting sum -- two lineages are still distinct with probability `exp (-τ)`, and two
distinct lineages disagree with probability `2p(1-p)` -- so the closed form's factorial
coefficients are being checked against a quantity that did not come from them. It is the
second control the battery runs. -/
theorem tagSampleMonomorphicProb_pair (p tau : ℝ) :
    tagSampleMonomorphicProb p 2 tau = 1 - 2 * p * (1 - p) * Real.exp (-tau) := by
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [tagSampleMonomorphicProb, hIcc, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2),
    blockCountLaw_two_one, blockCountLaw_two_two]
  ring

/-- **At the instant of the split there is no coalescent content left**, only sampling: the
pair probability is `p² + (1-p)²`, which is the chance two independent draws agree. This is
the battery's first control, at `n = 2`, and it is what a body that had accidentally kept a
drift term at zero time would fail. -/
theorem tagSampleMonomorphicProb_pair_at_zero (p : ℝ) :
    tagSampleMonomorphicProb p 2 0 = p ^ 2 + (1 - p) ^ 2 := by
  rw [tagSampleMonomorphicProb_pair]
  norm_num
  ring

end Coalescent

end Descent

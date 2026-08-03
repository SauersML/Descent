"""GENERATED FILE -- do not edit.  NOT AUTHORITATIVE IF COMMITTED.

    THE COPY OF THIS FILE IN GIT IS STALE BY CONSTRUCTION.

`proofs/Calibrator/` changes every few minutes.  A generated table committed
alongside it is a cache of a moving target, and committing it moves the
staleness from DETECTABLE to COMMITTED -- which is worse, because a file in the
repository reads as authoritative.

DO NOT CONSUME A COMMITTED COPY.  Run `python3 validation/extract/emit.py` in
your own worktree immediately before use.  It takes about a minute, writes only
inside that worktree, pins your numbers to the revision you are standing on, and
makes `api.require_fresh()` pass for a reason rather than by luck.  It also means
no two agents write to each other's artifacts.

`api.require_fresh()` will raise if you skip this.  That is the intended
behaviour, not an obstacle.


Produced by validation/extract/emit.py from the Lean sources under
proofs/Calibrator/.  Each function below was translated from the parsed body of
the corresponding Lean `def`; no formula in this file was typed by hand.

Regenerate with:  python3 validation/extract/emit.py
"""
# ruff: noqa
import lean_rt as _rt

def epistaticVariancePairwise(γ, p_1, p_2):
    return ((_rt.lpow(γ, 2.0) * (((2.0 * p_1) * ((1.0 - p_1))))) * (((2.0 * p_2) * ((1.0 - p_2)))))

def driftVariance(p0, fst):
    return ((p0 * ((1.0 - p0))) * fst)

def twoPopDriftVariance(p0, fst):
    return (2.0 * driftVariance(p0, fst))

def expectedFreqDiffSq(fst, p0):
    return (((2.0 * fst) * p0) * ((1.0 - p0)))

def gwasHeritability(h2_true, avg_r2_tag):
    return (h2_true * avg_r2_tag)

def geneFlowFstStep(m, Ne, F):
    return ibdFlowStep(Ne, m, F)

def portabilityFromArchitecture(rg, fst, tagging_ratio):
    return ((_rt.lpow(rg, 2.0) * ((1.0 - fst))) * tagging_ratio)

def fisherInformation(n, v):
    return (n * v)

def genotypeVarianceHWE(p):
    return ((2.0 * p) * ((1.0 - p)))

def effectiveFisherInformation(n, p, r2_ld):
    return (fisherInformation(n, (genotypeVarianceHWE(p))) * r2_ld)

def standardErrorSq(n, p, r2_ld):
    return _rt.rdiv(1.0, effectiveFisherInformation(n, p, r2_ld))

def effectiveSampleSize(n, p, r2_ld):
    return ((n * (((2.0 * p) * ((1.0 - p))))) * r2_ld)

def ncp(n_eff, β):
    return (n_eff * _rt.lpow(β, 2.0))

def hweHeterozygosity(p):
    return ((2.0 * p) * ((1.0 - p)))

def portableFraction(r2_causal, r2_total):
    return _rt.rdiv(r2_causal, r2_total)

def proportionalAllocation(pop_size, total_n, total_pop):
    return (total_n * (_rt.rdiv(pop_size, total_pop)))

def h2(m):
    return _rt.rdiv(_rt._proj(m, 'V_A'), _rt._proj(m, 'V_P'))

def amVarianceStep(V_0, r, h2, V):
    return _rt.rdiv((((V * ((1.0 + (r * h2)))) + V_0)), 2.0)

def equilibriumVariance(m):
    return _rt.rdiv(_rt._proj(m, 'V_A'), ((1.0 - (_rt._proj(m, 'r') * h2(m)))))

def amEquilibriumVariance(V_A, r, h2):
    return _rt.rdiv(V_A, ((1.0 - (r * h2))))

def amInducedLD(beta_i, beta_j, r, h2):
    return _rt.rdiv((((beta_i * beta_j) * r) * h2), ((1.0 - (r * h2))))

def observedH2(m):
    return _rt.rdiv(h2(m), ((1.0 - (_rt._proj(m, 'r') * h2(m)))))

def pgsR2AM(m, R2_rm):
    return _rt.rdiv(R2_rm, ((1.0 - (_rt._proj(m, 'r') * h2(m)))))

def amGap(m, R2_rm):
    return (pgsR2AM(m, R2_rm) - R2_rm)

def apparentPortability(d):
    return _rt.rdiv(((1.0 - (_rt._proj(d, 'r_s') * _rt._proj(d, 'h2')))), ((1.0 - (_rt._proj(d, 'r_t') * _rt._proj(d, 'h2')))))

def amCorrectedPortability(port_measured, r_source, r_target, h2):
    return _rt.rdiv((port_measured * ((1.0 - (r_source * h2)))), ((1.0 - (r_target * h2))))

def ibdFst(d, N, sigma_sq):
    return _rt.rdiv(d, ((((4.0 * N) * sigma_sq) + d)))

def posteriorPrecision(m):
    return (_rt.rdiv(1.0, _rt._proj(m, 'prior_var')) + _rt._proj(m, 'data_precision'))

def posteriorVariance(m):
    return _rt.rdiv(1.0, posteriorPrecision(m))

def posteriorMean(m, y):
    return ((posteriorVariance(m) * _rt._proj(m, 'data_precision')) * y)

def shrinkageFactor(m):
    return (posteriorVariance(m) * _rt._proj(m, 'data_precision'))

def gaussianPosteriorShrinkage(n, h):
    return _rt.rdiv((n * h), (((n * h) + 1.0)))

def jamesSteinMSE(lam, σ_sq, β_sq):
    return ((_rt.lpow(lam, 2.0) * σ_sq) + (_rt.lpow(((1.0 - lam)), 2.0) * β_sq))

def optimalShrinkage(σ_sq, β_sq):
    return _rt.rdiv(β_sq, ((σ_sq + β_sq)))

def snpShrinkage(σ, τ):
    return _rt.rdiv(σ, ((σ + τ)))

def spikeAndSlabPriorVariance(π, σ_slab):
    return (_rt.pi * _rt.lpow(σ_slab, 2.0))

def misspecExcessRisk(π, σ_β_sq):
    return ((_rt.pi * ((1.0 - _rt.pi))) * σ_β_sq)

def posteriorPredictiveVariance(residual_var, estimation_var):
    return (residual_var + estimation_var)

def multiAncestryEffectiveN(n_target, rg, n_other):
    return (n_target + (_rt.lpow(rg, 2.0) * n_other))

def averageEffect(m):
    return (_rt._proj(m, 'a') + (_rt._proj(m, 'd') * ((1.0 - (2.0 * _rt._proj(m, 'p'))))))

def genotypicValue(m, _e):
    _t = [(-_rt._proj(m, 'a')), _rt._proj(m, 'd'), _rt._proj(m, 'a')]
    return _t[_rt._ix(_e, 3, 'genotypicValue')]

def meanValue(m, h):
    return sum(((genotypeProb(h, g) * genotypicValue(m, g))) for g in range(int(3)))

def valueDosageCovariance(m, h):
    return sum((((genotypeProb(h, g) * ((genotypicValue(m, g) - meanValue(m, h)))) * centeredAltAlleleCount(h, g))) for g in range(int(3)))

def weightRatio(P, Q, w):
    return _rt.rdiv(wProd(Q, w), wProd(P, w))

def defect(P, Q, w, u):
    return _rt.rdiv(weightRatio(P, Q, w), weightRatio(P, Q, u))

def chi(P, Q, w):
    return _rt.rdiv(wProd(P, w), wProd(Q, w))

def outerAtom(w):
    return _rt.rsqrt(((1.0 + w)))

def innerAtom(w):
    return _rt.rsqrt(((1.0 - w)))

def mOne(p):
    return _rt.rdiv(_rt.rabs((1.0 - (2.0 * p))), p)

def mTwo(p):
    return _rt.rdiv(_rt.rabs((1.0 - (2.0 * p))), ((1.0 - p)))

def chain(k):
    return _rt.rdiv((k), (((2.0 * (k)) + 1.0)))

def modulus(family, j, t):
    return _rt.rabs((_rt.lpow(_rt._proj(family, 'atomValue')(j, t), 2.0) - 1.0))

def massAt(family, t, v):
    return sum(((_rt._proj(family, 'atomMass')(j, t) if (modulus(family, j, t) == v) else 0.0)) for j in range(int(_rt.sumdim('j', len(_rt._proj(family, 'atomMass'))))))

def spectrumModulusLaw(family, panel, v):
    return sum(((_rt._proj(panel, 'weight')(i) * massAt(family, (_rt._proj(panel, 'support')(i)), v))) for i in range(int(_rt.sumdim('i', len(_rt._proj(panel, 'weight')), len(_rt._proj(panel, 'support'))))))

def Covers(family, panel, i, v):
    return (massAt(family, (_rt._proj(panel, 'support')(i)), v) != 0.0)

def proportionMediated(indirect_effect, total_effect):
    return _rt.rdiv(indirect_effect, total_effect)

def costEffectiveness(improvement, cost):
    return _rt.rdiv(improvement, cost)

def eValue(rr):
    return (rr + _rt.rsqrt(((rr * ((rr - 1.0))))))

def liabilitySensitivity(Φ, m, R2, T_p):
    R = _rt.rsqrt(R2)
    h = _rt.rsqrt(_rt._proj(m, 'h_sq'))
    σ_resid = _rt.rsqrt((((_rt._proj(m, 'h_sq') * ((1.0 - R2))) + ((1.0 - _rt._proj(m, 'h_sq'))))))
    return Φ((_rt.rdiv(((((R * h) * _rt._proj(m, 'case_mean')) - T_p)), σ_resid)))

def liabilitySpecificity(Φ, m, R2, T_p, μ_control):
    R = _rt.rsqrt(R2)
    h = _rt.rsqrt(_rt._proj(m, 'h_sq'))
    σ_resid = _rt.rsqrt((((_rt._proj(m, 'h_sq') * ((1.0 - R2))) + ((1.0 - _rt._proj(m, 'h_sq'))))))
    return Φ((_rt.rdiv(((T_p - ((R * h) * μ_control))), σ_resid)))

def netReclassificationImprovement(event_nri, nonevent_nri):
    return (event_nri + nonevent_nri)

def sensFromR2(m, r2, T_p):
    return liabilitySensitivity(Phi, m, r2, T_p)

def specFromR2(m, r2, T_p, μ_control):
    return liabilitySpecificity(Phi, m, r2, T_p, μ_control)

def ppv(prev, tpr, fpr):
    return _rt.rdiv((prev * tpr), (((prev * tpr) + (((1.0 - prev)) * fpr))))

def proportionCorrectlyClassified(sensitivity, specificity, prevalence):
    return ((sensitivity * prevalence) + (specificity * ((1.0 - prevalence))))

def numberNeededToScreen(sens, π):
    return _rt.rdiv(1.0, ((sens * _rt.pi)))

def populationAttributableFraction(p_high, rr_reduction):
    return (p_high * ((1.0 - _rt.rdiv(1.0, rr_reduction))))

def brierScore(p, y):
    return _rt.lpow(((y - p)), 2.0)

def expectedBrierScore(p, π):
    return ((_rt.pi * _rt.lpow(((1.0 - p)), 2.0)) + (((1.0 - _rt.pi)) * _rt.lpow(p, 2.0)))

def sigmoid(x):
    return _rt.rdiv(1.0, ((1.0 + _rt.rexp(((-x))))))

def infRisk(μ, ℓ, p, F):
    return oracleRisk((populationRisk(μ, ℓ, p)), F)

def BayesRisk(R, F):
    return oracleRisk(R, F)

def bernoulliLogLoss(p, q):
    return (-(((p * _rt.rlog(q)) + (((1.0 - p)) * _rt.rlog(((1.0 - q)))))))

def bernoulliKLReal(p, q):
    return ((p * _rt.rlog((_rt.rdiv(p, q)))) + (((1.0 - p)) * _rt.rlog((_rt.rdiv(((1.0 - p)), ((1.0 - q)))))))

def klBernReal(p, q):
    return bernoulliKLReal(_rt._proj(p, '1'), _rt._proj(q, '1'))

def brierBernoulliRisk(η, q):
    return expectedBrierScore(q, η)

def logBernoulliRisk(η, q):
    return bernoulliLogLoss(η, q)

def logBayesRisk(μ, η, F):
    return BayesRisk((logRisk(μ, η)), F)

def brierBayesRisk(μ, η, F):
    return BayesRisk((brierRisk(μ, η)), F)

def gaussianJetVariance():
    return (_rt.rdiv(_rt.lpow(_rt.pi, 2.0), 2.0) - 4.0)

def criticalDegree(N, c):
    return _rt.rdiv(_rt.rlog(N), c)

def gaussianCriticalMultiplier():
    return _rt.rdiv(1.0, condensationConstant)

def windowVariance(w, v):
    return Phi((_rt.rdiv(w, _rt.rsqrt(v))))

def gaussianKurtosisMaf():
    return _rt.rdiv(((3.0 - _rt.rsqrt(3.0))), 6.0)

def moment(spectrum, k):
    return sum(((_rt._proj(spectrum, 'weight')(j) * sum(((_rt._proj((_rt._proj(spectrum, 'model')(j)), 'genotypeProb')(g) * _rt.lpow(_rt._proj((_rt._proj(spectrum, 'model')(j)), 'standardizedGenotype')(g), k))) for g in range(int(3))))) for j in range(int(_rt.sumdim('j', len(_rt._proj(spectrum, 'weight')), len(_rt._proj(spectrum, 'model'))))))

def centeredSquareThirdMoment(spectrum):
    return ((moment(spectrum, 6.0) - (3.0 * moment(spectrum, 4.0))) + 2.0)

def fourthMomentDispersion(spectrum):
    return ((sum(((_rt._proj(spectrum, 'weight')(j) * _rt.lpow((_rt.rdiv(1.0, _rt._proj((_rt._proj(spectrum, 'model')(j)), 'genotypeVariance'))), 2.0))) for j in range(int(_rt.sumdim('j', len(_rt._proj(spectrum, 'weight')), len(_rt._proj(spectrum, 'model'))))))) - _rt.lpow((moment(spectrum, 4.0)), 2.0))

def squaringScaleSq(fourthMoment):
    return (fourthMoment - 1.0)

def nextFloorFourthMoment(m2, m4, m6, m8):
    return _rt.rdiv((((((m8 - (4.0 * m6)) + (6.0 * m4)) - (4.0 * m2)) + 1.0)), _rt.lpow(((m4 - 1.0)), 2.0))

def squaringStep(scale, x):
    return _rt.rdiv(((_rt.lpow(x, 2.0) - 1.0)), scale)

def squaringFixedPoint(scale):
    return _rt.rdiv(((scale + _rt.rsqrt(((_rt.lpow(scale, 2.0) + 4.0))))), 2.0)

def ladderMomentOrder(rung):
    return _rt.lpow(2.0, rung)

def varianceProfile(s):
    return (((1.0 + s)) - ((1.0 - s)))

def fourthMomentProfile(s):
    return (_rt.lpow(((1.0 + s)), 2.0) - _rt.lpow(((1.0 - s)), 2.0))

def jProfile(tilt, order, s):
    return ((_rt.lpow(_rt.rlog(((1.0 + s))), order) * _rt.lpow(((1.0 + s)), tilt)) - (_rt.lpow(_rt.rlog(((1.0 - s))), order) * _rt.lpow(((1.0 - s)), tilt)))

def displacement(F, profile):
    return sum(((_rt._proj(F, 'mass')(j) * profile((_rt._proj(F, 'location')(j))))) for j in range(int(_rt.sumdim('j', len(_rt._proj(F, 'mass')), len(_rt._proj(F, 'location'))))))

def copiedBinaryJointExpectation():
    return _rt.rdiv(((((1.0) * 1.0) + (((-1.0)) * ((-1.0))))), 2.0)

def copiedBinaryConditionalProductExpectation():
    return _rt.rdiv(((((_rt.rdiv((((1.0) + ((-1.0)))), 2.0)) * 1.0) + ((_rt.rdiv((((1.0) + ((-1.0)))), 2.0)) * ((-1.0))))), 2.0)

def FullSupport(J):
    return all(((_rt._proj(J, 'mass')(x) != 0.0)) for x in range(int(_rt.sumdim('x', len(_rt._proj(J, 'mass'))))))

def ploidy():
    return 2.0

def hweGenotypeVariance(p):
    return ((ploidy * p) * ((1.0 - p)))

def coalescentTimeScale(Ne):
    return (ploidy * Ne)

def meanAlleleFreq(p_1, p_2):
    return _rt.rdiv(((p_1 + p_2)), 2.0)

def hudsonFst(p_1, p_2):
    return (1.0 - _rt.rdiv((((p_1 * ((1.0 - p_1))) + (p_2 * ((1.0 - p_2))))), (((ploidy * meanAlleleFreq(p_1, p_2)) * ((1.0 - meanAlleleFreq(p_1, p_2)))))))

def trueHudsonFst(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), (((p_1 * ((1.0 - p_2))) + (p_2 * ((1.0 - p_1))))))

def betweenSubgroupVariance(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), 4.0)

def convexMix(α, x, y):
    return ((α * x) + (((1.0 - α)) * y))

def geometricDecay(r, t):
    return _rt.lpow(((1.0 - r)), t)

def oneMinusRatio(a, b):
    return (1.0 - _rt.rdiv(a, b))

def retainedFraction(loss, total):
    return (((1.0 - loss)) * total)

def ldCorrelationSq(D, p_i, p_j):
    return _rt.rdiv(_rt.lpow(D, 2.0), ((genotypeVarianceHWE(p_i) * genotypeVarianceHWE(p_j))))

def ldCorrelationSqOfHaplotypeD(D, p_i, p_j):
    return ldCorrelationSq(((2.0 * D)), p_i, p_j)

def numBlocks(genome_length, mean_block_size):
    return _rt.rdiv(genome_length, mean_block_size)

def ldsrExpectedBetaSq(h2, M, ell_j, N):
    return ((_rt.rdiv(h2, M) * ell_j) + _rt.rdiv(1.0, N))

def ldsrExpectedChi2(N, h2, M, ell_j, a):
    return (((_rt.rdiv((N * h2), M) * ell_j) + (N * a)) + 1.0)

def haplotypeFreqAdmixed(alpha, p_A, q_A, p_B, q_B):
    return (((alpha * p_A) * q_A) + ((((1.0 - alpha)) * p_B) * q_B))

def admixtureLDTwoLocus(alpha, p_A, q_A, p_B, q_B):
    return (haplotypeFreqAdmixed(alpha, p_A, q_A, p_B, q_B) - (admixedAlleleFreq(alpha, p_A, p_B) * admixedAlleleFreq(alpha, q_A, q_B)))

def admixtureLDAtGen(alpha, p_A, q_A, p_B, q_B, r, g):
    return (_rt.lpow(((1.0 - r)), g) * admixtureLDTwoLocus(alpha, p_A, q_A, p_B, q_B))

def admixtureLDMagnitude(alpha, p_A, p_B, r, g):
    return (((alpha * ((1.0 - alpha))) * _rt.lpow(((p_A - p_B)), 2.0)) * _rt.lpow(((1.0 - r)), g))

def charFnSq(w, a, t):
    return sum((sum((_rt.mul(_rt.mul(w[int(u)], w[int(v)]), _rt.cos((_rt.mul(t, (_rt.sub(a[int(u)], a[int(v)]))))))) for v in range(int(len(w))))) for u in range(int(len(w))))

def scaledMutationRate(Ne, μ):
    return ((4.0 * Ne) * μ)

def scaledMigrationRate(Ne, m):
    return ((4.0 * Ne) * m)

def fstMutationDriftEquilibrium(θ):
    return _rt.rdiv(1.0, ((1.0 + θ)))

def hetDecayFromScaled(Ne, θ):
    return (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * ((1.0 - _rt.rdiv(θ, ((2.0 * Ne))))))

def Calibrator_HWEPolygenicScoreDGP_scoreMean(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'scoreMean')

def Calibrator_HWEPolygenicScoreDGP_scoreVariance(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'scoreVariance')

def scoreApproximationError(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'berryEsseenErrorBound')(_rt._proj(dgp, 'berryEsseenConstant'))

def Calibrator_SourceTaggedMoments_sigmaTagCausal(mom):
    return (_rt._proj(mom, 'directCausalSource') + _rt._proj(mom, 'proxyTaggingSource'))

def sourceBestLinearWeightsFromLD(mom, betaCausal):
    return _rt._proj(_rt.rinv(_rt._proj(mom, 'sigmaTagSource')), 'mulVec')((_rt._proj(_rt._proj(mom, 'sigmaTagCausal'), 'mulVec')(betaCausal)))

def frobeniusNormSq(A):
    t = float(len(A))
    return sum((sum((_rt.lpow((A[int(i)][int(j)]), 2.0)) for j in range(int(len(A))))) for i in range(int(len(A))))

def r2FromMSE(mse, varY):
    return (1.0 - _rt.rdiv(mse, varY))

def explainedR2FromTransportMoments(scoreOutcomeCov, scoreVariance, outcomeVariance):
    return _rt.rdiv(_rt.lpow(scoreOutcomeCov, 2.0), ((scoreVariance * outcomeVariance)))

def ldWitnessSourceWeights():
    return sourceBestLinearWeightsFromLD(ldWitnessSourceMoments, ldWitnessBeta)

def taggingMismatchScale(recombRate, arraySparsity):
    return (recombRate * arraySparsity)

def demographicCovarianceGapLowerBound(fstSource, fstTarget, recombRate, arraySparsity, kappa):
    return ((kappa * taggingMismatchScale(recombRate, arraySparsity)) * ((fstTarget - fstSource)))

def discreteRecombinationSurvival(recombRate, tmrca):
    return _rt.lpow(((1.0 - recombRate)), tmrca)

def twoLocusIBDCovariance(ibdWeight, recombRate, tmrca):
    return (ibdWeight * discreteRecombinationSurvival(recombRate, tmrca))

def twoLocusCoalescentCovarianceMatrix(ibdWeight, recombRate, tmrca):
    return (lambda i, j: (twoLocusIBDCovariance(ibdWeight, recombRate, tmrca) if ((i == twoLocusIdx0) and (j == twoLocusIdx1)) else (twoLocusIBDCovariance(ibdWeight, recombRate, tmrca) if ((i == twoLocusIdx1) and (j == twoLocusIdx0)) else (1.0 if (i == j) else 0.0))))

def optimalSlopeLinearNoise(sigma_g_sq, base_error, slope_error, c):
    return _rt.rdiv(sigma_g_sq, (((sigma_g_sq + base_error) + (slope_error * c))))

def totalVariance(arch, c):
    return _rt.add(_rt._proj(arch, 'V_genic')(c), _rt._proj(arch, 'V_cov')(c))

def optimalSlopeFromVariance(arch, c):
    return _rt.rdiv((totalVariance(arch, c)), (_rt._proj(arch, 'V_genic')(c)))

def prevalenceDGP_trueExpectation(pdgp, p, c):
    return _rt.add(_rt._proj(pdgp, 'prevalence')(c), _rt.mul(_rt._proj(pdgp, 'pgs_effect'), p))

def decaySlope(mech, c):
    return _rt._proj(mech, 'tagging_efficiency')((_rt._proj(mech, 'distance')(c)))

def measureBias(μ, Y, S):
    return _rt.sub(measureMean(μ, S), measureMean(μ, Y))

def trueExp(hdgp):
    return (lambda p, c: ((_rt._proj(hdgp, 'alpha')(c) * p) + _rt._proj(hdgp, 'baseline')(c)))

def tau(p):
    return _rt.rdiv(_rt._proj(p, 't_div'), ((2.0 * _rt._proj(p, 'Ne'))))

def Calibrator_EvolutionaryParameters_theta(p):
    return scaledMutationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mu'))

def Calibrator_EvolutionaryParameters_bigM(p):
    return scaledMigrationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mig'))

def fstDriftMigration(p):
    return _rt.rdiv(1.0, ((1.0 + Calibrator_EvolutionaryParameters_bigM(p))))

def fstDriftFlowStep(p, F):
    return ((F + _rt.rdiv(((1.0 - F)), ((2.0 * _rt._proj(p, 'Ne'))))) - ((2.0 * ((_rt._proj(p, 'mig') + _rt._proj(p, 'mu')))) * F))

def Calibrator_fstEquilibrium(p):
    return _rt.rdiv(1.0, (((1.0 + Calibrator_EvolutionaryParameters_theta(p)) + Calibrator_EvolutionaryParameters_bigM(p))))

def sharedLDRetention(p):
    return _rt.rexp(((((-2.0) * _rt._proj(p, 'recomb')) * _rt._proj(p, 't_div'))))

def mutationLDErosion(p):
    return _rt.rexp((((-Calibrator_EvolutionaryParameters_theta(p)) * tau(p))))

def migrationLDBoost(p):
    return (1.0 + _rt.rdiv((Calibrator_EvolutionaryParameters_bigM(p) * tau(p)), ((1.0 + Calibrator_EvolutionaryParameters_bigM(p)))))

def r2FromSignalVariance(vSignal, vNoise):
    return _rt.rdiv(vSignal, ((vSignal + vNoise)))

def gaussianAUCFromSignalVariance(vSignal, vNoise):
    return Phi((_rt.rsqrt((_rt.rdiv(vSignal, ((2.0 * vNoise)))))))

def calibratedBrier(π, r2):
    return ((_rt.pi * ((1.0 - _rt.pi))) * ((1.0 - r2)))

def calibratedBrierFromVariances(π, vSignal, vResidual):
    return ((_rt.pi * ((1.0 - _rt.pi))) * ((1.0 - _rt.rdiv(vSignal, ((vSignal + vResidual))))))

def Calibrator_TransportedMetrics_IrreducibleTargetPenalty_total(penalty):
    return (((_rt._proj(penalty, 'brokenTagging') + _rt._proj(penalty, 'ancestrySpecificLD')) + _rt._proj(penalty, 'sourceSpecificOverfit')) + _rt._proj(penalty, 'novelUntaggablePhenotype'))

def profileFromSignalVarianceWithPenalty(π, vNoise, vSignal, penalty):
    return profileFromSignalVariance(_rt.pi, ((vNoise + Calibrator_TransportedMetrics_IrreducibleTargetPenalty_total(penalty))), vSignal)

def metricProfileFromTargetSignalWithPenalty(m, vSignalTarget, penalty):
    return profileFromSignalVarianceWithPenalty(_rt._proj(m, 'prevalence'), _rt._proj(m, 'V_E'), vSignalTarget, penalty)

def alleleFreqDivergenceRate(Ne, mu, m_rate):
    theta = ((4.0 * Ne) * mu)
    bigM = ((4.0 * Ne) * m_rate)
    return _rt.rdiv(1.0, (((2.0 * Ne) * (((1.0 + theta) + bigM)))))

def ldBreakageRate(r):
    return (2.0 * r)

def contrastSpikeLevel(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), ((meanAlleleFreq(p_1, p_2) * ((1.0 - meanAlleleFreq(p_1, p_2))))))

def demoSteppingStoneFst(d, Ne, m, σ_sq):
    return _rt.rdiv(d, ((d + (((4.0 * Ne) * m) * σ_sq))))

def steppingStoneFstQuadratic(d, Ne, m, σ_sq):
    return _rt.rdiv(d, ((d + (((4.0 * Ne) * _rt.lpow(σ_sq, 2.0)) * _rt.lpow(m, 2.0)))))

def steppingStoneCoalescenceTime(d, σ_sq, m):
    return _rt.rdiv(d, (((2.0 * σ_sq) * m)))

def steppingStoneMeetingTimeOnLattice(d, D, σ_sq, m):
    return _rt.rdiv((d * ((D - d))), (((2.0 * σ_sq) * m)))

def admixedFst(α, fst_AB):
    return (_rt.lpow(((1.0 - α)), 2.0) * fst_AB)

def admixedFstExact(α, fst_AB, hetRatio):
    return _rt.rdiv((_rt.lpow(((1.0 - α)), 2.0) * fst_AB), hetRatio)

def admixedAlleleFreq(α, p_A, p_B):
    return ((α * p_A) + (((1.0 - α)) * p_B))

def introgressionVariants(N_0, introgressionRate, t):
    return (N_0 * ((1.0 - _rt.rexp((((-introgressionRate) * t))))))

def founderFst(k, t):
    return (1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * (k)))))), t))

def cumulativeDrift(Ne):
    return sum((_rt.rdiv(1.0, (_rt.mul(2.0, Ne[int(i)])))) for i in range(int(len(Ne))))

def fstVariableNe(Ne):
    return _rt.sub(1.0, _rt.rexp((_rt.neg((cumulativeDrift(Ne))))))

def driftLDCreationRate(Ne):
    return _rt.rdiv(1.0, ((2.0 * Ne)))

def bottleneckExcessLD(Ne_b, Ne_stable, c, t_b):
    return (driftLDTrajectory(Ne_b, c, (driftLDEquilibrium(Ne_stable, c)), t_b) - driftLDEquilibrium(Ne_stable, c))

def measuredLoss(M, t):
    return (1.0 - _rt.rdiv(_rt._proj(M, 'het')(t), _rt._proj(M, 'het')(0.0)))

def lossOfRetention(r):
    return (1.0 - r)

def targetHetOfRetention(H_0, r):
    return (H_0 * r)

def targetPgsVarOfRetention(V_A, r):
    return (V_A * r)

def clusterCrossCheck(r):
    return (targetHetOfRetention(1.0, r) == (1.0 * ((1.0 - lossOfRetention(r)))))

def benchmarkRatio(fstS, fstT):
    return _rt.rdiv(((1.0 - fstT)), ((1.0 - fstS)))

def benchmarkRatioSquared(fstS, fstT):
    return _rt.lpow((_rt.rdiv(((1.0 - fstT)), ((1.0 - fstS)))), 2.0)

def diagonalDesign(g):
    return (lambda x: g(x, x))

def fejerChannel3(γ_0, γ_1, γ_2):
    return ((γ_0 + ((_rt.rdiv(4.0, 3.0)) * γ_1)) + ((_rt.rdiv(2.0, 3.0)) * γ_2))

def gaussianPairSquareChannel3(γ_0, γ_1, γ_2):
    return (((3.0 * _rt.lpow(γ_0, 2.0)) + (4.0 * _rt.lpow(γ_1, 2.0))) + (2.0 * _rt.lpow(γ_2, 2.0)))

def ensembleSquaredLoss(target, deployment):
    return sum((_rt.lpow((_rt.sub(target[int(i)], deployment)), 2.0)) for i in range(int(len(target))))

def ensemblePredictorSquaredLoss(target, predictor):
    return sum((_rt.lpow((_rt.sub(target[int(i)], predictor[int(i)])), 2.0)) for i in range(int(len(target))))

def weightedBandEnsembleLoss(weight, target, deployment):
    return sum((sum((_rt.mul(weight[int(i)][int(b)], _rt.lpow((_rt.sub(target[int(i)][int(b)], deployment[int(b)])), 2.0))) for b in range(int(_rt.sumdim('b', len(weight[0]), len(target[0]), len(deployment)))))) for i in range(int(_rt.sumdim('i', len(weight), len(target)))))

def weightedBandPredictorLoss(weight, target, predictor):
    return sum((sum((_rt.mul(weight[int(i)][int(b)], _rt.lpow((_rt.sub(target[int(i)][int(b)], predictor[int(i)][int(b)])), 2.0))) for b in range(int(len(weight))))) for i in range(int(len(weight))))

def fisherAverageEffect(a, d, p):
    return (a + (d * ((1.0 - (2.0 * p)))))

def pairwiseModel(beta1, beta2, beta12, g1, g2):
    return (((beta1 * g1) + (beta2 * g2)) + ((beta12 * g1) * g2))

def epistaticVariance(beta12, p1, p2):
    return ((_rt.lpow(beta12, 2.0) * (((2.0 * p1) * ((1.0 - p1))))) * (((2.0 * p2) * ((1.0 - p2)))))

def dominanceVariance(p, d):
    return sum((_rt.lpow((_rt.mul(_rt.mul(_rt.mul(2.0, p[int(i)]), (_rt.sub(1.0, p[int(i)]))), d[int(i)])), 2.0)) for i in range(int(len(p))))

def hweThirdCentralMoment(h):
    return sum(((genotypeProb(h, g) * _rt.lpow(centeredAltAlleleCount(h, g), 3.0))) for g in range(int(3)))

def standardizedGenotype(h, g):
    return _rt.rdiv(centeredAltAlleleCount(h, g), _rt.rsqrt(genotypeVariance(h)))

def centeredSquare(h, g):
    return (_rt.lpow(standardizedGenotype(h, g), 2.0) - 1.0)

def signBias(h):
    return sum(((genotypeProb(h, g) * ((standardizedGenotype(h, g) * _rt.rabs(standardizedGenotype(h, g)))))) for g in range(int(3)))

def fourthCumulantFromMoments(secondMoment, fourthMoment):
    return (fourthMoment - (3.0 * _rt.lpow(secondMoment, 2.0)))

def circulantSpectrumA(c):
    return (((8.0 * _rt.lpow(c, 2.0)) + (2.0 * c)) - 4.0)

def circulantSpectrumB(c):
    return (((4.0 * _rt.lpow(c, 2.0)) + (4.0 * c)) - 2.0)

def cycleDensity(design, p):
    return _rt.trace((_rt.lpow(overlapMatrix(design), p)))

def palindromicCycleDensityA(s, p):
    return ((((_rt.lpow(circulantSpectrumA(1.0), p) + (2.0 * _rt.lpow(circulantSpectrumA((_rt.rdiv(s, 2.0))), p))) + (2.0 * _rt.lpow(circulantSpectrumA(0.0), p))) + (2.0 * _rt.lpow(circulantSpectrumA(((-(_rt.rdiv(s, 2.0))))), p))) + _rt.lpow(circulantSpectrumA(((-1.0))), p))

def palindromicCycleDensityB(s, p):
    return ((((_rt.lpow(circulantSpectrumB(1.0), p) + (2.0 * _rt.lpow(circulantSpectrumB((_rt.rdiv(s, 2.0))), p))) + (2.0 * _rt.lpow(circulantSpectrumB(0.0), p))) + (2.0 * _rt.lpow(circulantSpectrumB(((-(_rt.rdiv(s, 2.0))))), p))) + _rt.lpow(circulantSpectrumB(((-1.0))), p))

def expectedR2FromN(n, h2, M):
    return (h2 * (_rt.rdiv((n * h2), (((n * h2) + M)))))

def diploidStdev(q):
    return _rt.rsqrt((((2.0 * q) * ((1.0 - q)))))

def diploidAtomValue(j, q):
    return _rt.rdiv((((j) - (2.0 * q))), diploidStdev(q))

def diploidAtomMass(j, q):
    return (_rt.lpow(((1.0 - q)), 2.0) if (j == 0.0) else (((2.0 * q) * ((1.0 - q))) if (j == 1.0) else _rt.lpow(q, 2.0)))

def invHeterozygosity(q):
    return _rt.rdiv(1.0, (((2.0 * q) * ((1.0 - q)))))

def twoPointModulusLaw(family, site, pathWeight, v, w):
    m = float(len(pathWeight))
    return sum((_rt.mul(pathWeight[int(i)], (_rt.mul(_rt._proj(massAt(family), '1')((site(i)), v), _rt._proj(massAt(family), '2')((site(i)), w))))) for i in range(int(len(pathWeight))))

def positiveThreshold(x):
    return (1.0 if (0.0 < x) else 0.0)

def effectiveGeneticEffect(β_G, β_GxE, E_mean):
    return (β_G + (β_GxE * E_mean))

def linearNormOfReaction(a, b, E):
    return (a + (b * E))

def historyKernel(h, h_p):
    return markovPoissonKernel(((_rt._proj(h, 'memory') * _rt._proj(h_p, 'memory'))), (_rt.cos(((_rt._proj(h, 'phase') - _rt._proj(h_p, 'phase'))))))

def historySelfEnergy(h):
    return historyKernel(h, h)

def historySpectralDistanceSq(h, h_p):
    return ((historySelfEnergy(h) + historySelfEnergy(h_p)) - (2.0 * historyKernel(h, h_p)))

def historyDegradation(h, h_p):
    return (((_rt.lpow(_rt._proj(h, 'amplitude'), 2.0) * historySelfEnergy(h)) - (((2.0 * _rt._proj(h, 'amplitude')) * _rt._proj(h_p, 'amplitude')) * historyKernel(h, h_p))) + (_rt.lpow(_rt._proj(h_p, 'amplitude'), 2.0) * historySelfEnergy(h_p)))

def historyMarginalAmplitude(h):
    return _rt._proj(h, 'amplitude')

def discoveryNCP(n, β, maf_causal, ld):
    return (((n * _rt.lpow(β, 2.0)) * _rt.lpow(ld, 2.0)) * genotypeVarianceHWE(maf_causal))

def gwasDiscovered(n, β, maf_causal, ld, z):
    return (_rt.lpow(z, 2.0) <= discoveryNCP(n, β, maf_causal, ld))

def taggedScoreEstimationRisk(targetTagVariance, estimatorMSE):
    return sum((_rt.mul(targetTagVariance[int(i)], estimatorMSE[int(i)])) for i in range(int(len(targetTagVariance))))

def expectedLinearEffectEstimate(β_true, meanEstimationError):
    return (β_true + meanEstimationError)

def olsEffectEstimationVariance(σ2, varX, n):
    return _rt.rdiv(σ2, ((n * varX)))

def perCausalLocusSignal(h2, k):
    return _rt.rdiv(h2, k)

def geneticCorrelation(cov_g, vg_1, vg_2):
    return _rt.rdiv(cov_g, _rt.rsqrt(((vg_1 * vg_2))))

def multiTraitEffectiveSampleSize(n_1, n_2, rg):
    return (n_1 + (_rt.lpow(rg, 2.0) * n_2))

def multiTraitDiscoveryNCP(n_1, n_2, rg, β, maf, ld):
    return discoveryNCP((multiTraitEffectiveSampleSize(n_1, n_2, rg)), β, maf, ld)

def borrowedTraitBCrossCov(m):
    return _rt._proj(_rt._proj(m, 'sigmaTagCausal'), 'mulVec')(((lambda j: (_rt._proj(m, 'rg') * _rt._proj(m, 'sharedTraitEffect')(j)))))

def traitBSpecificCrossCov(m):
    return _rt._proj(_rt._proj(m, 'sigmaTagCausal'), 'mulVec')(_rt._proj(m, 'traitBSpecificEffect'))

def totalTraitBCrossCov(m):
    return (borrowedTraitBCrossCov(m) + traitBSpecificCrossCov(m))

def borrowedTraitBProjection(m):
    return _rt.dotProduct(_rt._proj(m, 'sourceWeights'), (borrowedTraitBCrossCov(m)))

def totalTraitBProjection(m):
    return _rt.dotProduct(_rt._proj(m, 'sourceWeights'), (totalTraitBCrossCov(m)))

def expectedDistinctHaplotypes(k, n):
    return (_rt.lpow((2.0), k) * ((1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, (_rt.lpow((2.0), k))))), n))))

def haplotypeHomozygosity(freq):
    return sum((_rt.lpow(freq[int(i)], 2.0)) for i in range(int(len(freq))))

def effectiveHaplotypeNumber(freq):
    return _rt.rdiv(1.0, haplotypeHomozygosity(freq))

def averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans):
    return ((freq_cis * interaction_cis) + (((1.0 - freq_cis)) * interaction_trans))

def dosagePhaseMisspecificationError(freq_cis, interaction_cis, interaction_trans):
    return ((freq_cis * _rt.lpow(((interaction_cis - averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans))), 2.0)) + (((1.0 - freq_cis)) * _rt.lpow(((interaction_trans - averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans))), 2.0)))

def haplotypePhasePredictionError(freq_cis, switch_err, pred_cis, pred_trans, interaction_cis, interaction_trans):
    return ((freq_cis * (((((1.0 - switch_err)) * _rt.lpow(((interaction_cis - pred_cis)), 2.0)) + (switch_err * _rt.lpow(((interaction_cis - pred_trans)), 2.0))))) + (((1.0 - freq_cis)) * (((((1.0 - switch_err)) * _rt.lpow(((interaction_trans - pred_trans)), 2.0)) + (switch_err * _rt.lpow(((interaction_trans - pred_cis)), 2.0))))))

def dosageTransportBias(freq_cis_source, freq_cis_target, interaction_cis, interaction_trans):
    return _rt.rabs((averagePhaseInteraction(freq_cis_target, interaction_cis, interaction_trans) - averagePhaseInteraction(freq_cis_source, interaction_cis, interaction_trans)))

def haplotypeTransportBias(freq_cis_target, pred_cis, pred_trans, interaction_cis, interaction_trans):
    return _rt.rabs((averagePhaseInteraction(freq_cis_target, pred_cis, pred_trans) - averagePhaseInteraction(freq_cis_target, interaction_cis, interaction_trans)))

def haplotypeEffectEstimationVariance(σ2, n, freq):
    return _rt.rdiv(σ2, ((n * freq)))

def phaseAttenuation(s):
    return _rt.lpow(((1.0 - (2.0 * s))), 2.0)

def ancestrySpecificEffect(beta_pop1, beta_pop2, alpha):
    return ((alpha * beta_pop1) + (((1.0 - alpha)) * beta_pop2))

def globalAncestryAveragedEffect(beta_1, beta_2, alpha):
    return ancestrySpecificEffect(beta_1, beta_2, alpha)

def localAncestryMisspecification(beta_1, beta_2, alpha):
    return ((alpha * _rt.lpow(((beta_1 - globalAncestryAveragedEffect(beta_1, beta_2, alpha))), 2.0)) + (((1.0 - alpha)) * _rt.lpow(((beta_2 - globalAncestryAveragedEffect(beta_1, beta_2, alpha))), 2.0)))

def expectedSegmentLength(g, r_total):
    return _rt.rdiv(1.0, ((g * r_total)))

def codedDecayProfile(B, x):
    return (lambda n: _rt.rexp((((-(B(n))) - x(n)))))

def neutralDriftR2Ratio(V_A, V_E, fst):
    return _rt.rdiv(presentDayR2(V_A, V_E, fst), presentDayR2(V_A, V_E, 0.0))

def taggedDriftR2Ratio(V_A, V_E, fst, shared_ld):
    return _rt.rdiv(presentDayR2MutationDrift(V_A, V_E, fst, shared_ld), presentDayR2(V_A, V_E, 0.0))

def addRankOneSignal(noise, factor, scale, loading):
    return (lambda ω, i: _rt.add(noise[int(ω)][int(i)], _rt.mul(_rt.mul(scale, factor[int(ω)]), loading[int(i)])))

def rankOneCovarianceBump(scale, loading):
    return (lambda i, j: _rt.mul(_rt.mul(_rt.lpow(scale, 2.0), loading[int(i)]), loading[int(j)]))

def ConstantDiagonal(A):
    return all(all(((A[int(i)][int(i)] == A[int(j)][int(j)])) for j in range(int(len(A)))) for i in range(int(len(A))))

def ShiftInvariant(shift, A):
    return all(all(((A[int((shift(i)))][int((shift(j)))] == A[int(i)][int(j)])) for j in range(int(len(A)))) for i in range(int(len(A))))

def scalarRowResolvent(latent, quadraticForm):
    return _rt.rdiv(1.0, ((1.0 + (_rt.lpow(latent, 2.0) * quadraticForm))))

def fairTwoPointVariance(a, b):
    return _rt.rdiv(_rt.lpow(((a - b)), 2.0), 4.0)

def gramForm(A, x, y):
    return sum((sum((_rt.mul(_rt.mul(x[int(i)], A[int(i)][int(j)]), y[int(j)])) for j in range(int(len(A))))) for i in range(int(len(A))))

def quadForm(A, x):
    return gramForm(A, x, x)

def stationaryLDEntry(decay, separation):
    return _rt.lpow(decay, separation)

def markovLDStep(decay, c, separation):
    return (1.0 if (separation == 0.0) else (decay * c(((separation - 1.0)))))

def ldKernelSymbol(decay, angle):
    return _rt.rdiv(((1.0 - _rt.lpow(decay, 2.0))), (((1.0 - ((2.0 * decay) * _rt.cos(angle))) + _rt.lpow(decay, 2.0))))

def ldHardEdge(decay):
    return _rt.rdiv(((1.0 - decay)), ((1.0 + decay)))

def ldWhiteningGain(decay):
    return _rt.rdiv(((1.0 + _rt.lpow(decay, 2.0))), ((1.0 - _rt.lpow(decay, 2.0))))

def ldPrecisionTrace(decay, nSites):
    return _rt.rdiv(((((nSites) * ((1.0 + _rt.lpow(decay, 2.0)))) - (2.0 * _rt.lpow(decay, 2.0)))), ((1.0 - _rt.lpow(decay, 2.0))))

def adjacentBoundarySeparation(d):
    if d == 0:
        return 1.0
    d = d - 1     # the `n + 1` pattern
    return d

def lossGeometryRisk(B, M):
    return _rt.trace((_rt.mul(B, M)))

def alleleLossProbability(initial, time):
    return _rt.rexp(((-(_rt.rdiv(initial, ((2.0 * time)))))))

def absorptionInformation(initial, time):
    return _rt.rdiv(alleleLossProbability(initial, time), ((4.0 * _rt.lpow(time, 2.0))))

def absorptionChannelWeight(initial, time):
    return _rt.rdiv((initial * alleleLossProbability(initial, time)), ((4.0 * time)))

def informationCrossoverTime(initial):
    return _rt.rdiv(initial, 2.0)

def attenuatedVariance(beta_sq, het, r2_imp):
    return ((beta_sq * het) * r2_imp)

def imputationErrorVariance(beta_sq, het, r2_imp):
    return ((beta_sq * het) * ((1.0 - r2_imp)))

def meanImputationR2(c, ld_extent):
    return _rt.rmax(0.0, ((1.0 - _rt.rdiv(c, ld_extent))))

def apparent_portability_loss(r2_source, r2_target_array):
    return (r2_source - r2_target_array)

def true_portability_loss(r2_source, r2_target_ideal):
    return (r2_source - r2_target_ideal)

def ascertainment_loss(coverage, v_causal):
    return (((1.0 - coverage)) * v_causal)

def total_portability_loss(loss_genetic, loss_technical):
    return (loss_genetic + loss_technical)

def latticeInflation(h):
    return _rt.rdiv(h, ((1.0 - _rt.rexp(((-h))))))

def latticeBracket(h, δ):
    return _rt.rdiv((h * _rt.rexp(((-δ)))), ((1.0 - _rt.rexp(((-h))))))

def ldRetentionPerGen(r, Ne):
    return (((1.0 - r)) * ((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))))

def ldAfterGenerations(D_0, r, Ne, t):
    return (D_0 * _rt.lpow((ldRetentionPerGen(r, Ne)), t))

def tagR2(D_sq, var_tag, var_causal):
    return _rt.rdiv(D_sq, ((var_tag * var_causal)))

def admixtureLD(α, Δp_1, Δp_2):
    return (((α * ((1.0 - α))) * Δp_1) * Δp_2)

def driftLDStep(Ne, c, Q):
    return (_rt.lpow(((1.0 - c)), 2.0) * ((_rt.rdiv(1.0, ((2.0 * Ne))) + (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * Q))))

def driftLDRetention(Ne, c):
    return (_rt.lpow(((1.0 - c)), 2.0) * ((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))))

def driftLDEquilibrium(Ne, c):
    return _rt.rdiv((_rt.lpow(((1.0 - c)), 2.0) * (_rt.rdiv(1.0, ((2.0 * Ne))))), ((1.0 - driftLDRetention(Ne, c))))

def ohtaKimuraSigmaDSq(Ne, c):
    ρ = ((4.0 * Ne) * c)
    return _rt.rdiv(((10.0 + ρ)), ((((2.0 + ρ)) * ((11.0 + ρ)))))

def driftLDTrajectory(Ne, c, Q_0, t):
    _prev = Q_0
    for _ in range(int(t)):
        _prev = driftLDStep(Ne, c, (_prev))
    return _prev

def ldMismatchFrobenius(Sig_S, Sig_T):
    return frobeniusNormSq((_rt.sub(Sig_S, Sig_T)))

def harmonicMeanNe(Ne):
    T = float(len(Ne))
    return _rt.rdiv((T), sum(((_rt.rdiv(1.0, Ne[int(i)]))) for i in range(int(len(Ne)))))

def excessLDAfterBottleneck(N_b, N_r, c, t_b, t_r):
    return (driftLDTrajectory(N_r, c, (driftLDTrajectory(N_b, c, (driftLDEquilibrium(N_r, c)), t_b)), t_r) - driftLDEquilibrium(N_r, c))

def ldDecayRatePerGen(Ne):
    return _rt.rdiv(1.0, ((2.0 * Ne)))

def ldHalfLife(r, Ne):
    return _rt.rdiv(_rt.rlog(2.0), ((-_rt.rlog((ldRetentionPerGen(r, Ne))))))

def ldRetainedFraction(r, Ne, t):
    return _rt.lpow((ldRetentionPerGen(r, Ne)), t)

def ldRecurrence(r, D_0, t):
    _prev = D_0
    for _ in range(int(t)):
        _prev = (((1.0 - r)) * _prev)
    return _prev

def expanderAgreementFloor():
    return (_rt.rdiv(1.0, 2.0) - _rt.rdiv(_rt.rsqrt(5.0), 6.0))

def portabilityAtTime(r2_initial, lambda_total, t):
    return (r2_initial * _rt.rexp((((-lambda_total) * t))))

def ldDecayPerGeneration(r, t):
    return _rt.lpow(((1.0 - r)), t)

def secularTrendBias(trend_rate, t):
    return (trend_rate * t)

def temporalMetricProfile(π, signalAtTime):
    return profileFromSignalVariance(_rt.pi, 1.0, signalAtTime)

def temporalR2(signalAtTime):
    return r2FromSignalVariance(signalAtTime, 1.0)

def ageDependentSignalShape(age, age_peak, width):
    return _rt.rexp((_rt.rdiv(_rt.lpow((-((age - age_peak))), 2.0), ((2.0 * _rt.lpow(width, 2.0))))))

def ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width):
    return (sourceSignalPeak * ageDependentSignalShape(age, age_peak, width))

def ageDependentMetricProfile(π, sourceSignalPeak, age, age_peak, width):
    return temporalMetricProfile(_rt.pi, (ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width)))

def ageDependentR2(sourceSignalPeak, age, age_peak, width):
    return temporalR2((ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width)))

def temporalCalibrationInTheLarge(π_obs, π_pred):
    return calibrationInTheLarge(π_obs, π_pred)

def temporalExactBrierRisk(π, signalAtTime):
    return _rt._proj((temporalMetricProfile(_rt.pi, signalAtTime)), 'brier')

def modelStaleness(lambda_, t):
    return (1.0 - _rt.rexp((((-lambda_) * t))))

def r2(d):
    return _rt.rdiv(_rt._proj(d, 'varCondE'), _rt._proj(d, 'varY'))

def discrimination(d):
    return _rt.rdiv(_rt._proj(d, 'varYhat'), _rt._proj(d, 'varY'))

def calibration(d):
    return _rt.rdiv(_rt._proj(d, 'varCondE'), _rt._proj(d, 'varYhat'))

def adaptationDifficultyIndex(nParams, infoPerSample):
    return _rt.rdiv(nParams, infoPerSample)

def fisherTraceMSELowerBound(nEff, nParams, infoPerSample):
    return _rt.rdiv(adaptationDifficultyIndex(nParams, infoPerSample), nEff)

def requiredEffectiveSampleSizeForTraceMSE(nParams, infoPerSample, targetTraceMSE):
    return _rt.rdiv(adaptationDifficultyIndex(nParams, infoPerSample), targetTraceMSE)

def brierDiscriminationLoss(m):
    return (targetCalibratedBrierFromSourceWeights(m) - sourceCalibratedBrierFromSourceWeightsAtPrevalence(m, _rt._proj(m, 'targetPrevalence')))

def brierCalibrationLoss(πSource, m):
    return (sourceCalibratedBrierFromSourceWeightsAtPrevalence(m, _rt._proj(m, 'targetPrevalence')) - sourceCalibratedBrierFromSourceWeightsAtPrevalence(m, πSource))

def metricPPV(sensitivity, specificity, prevalence):
    return _rt.rdiv((sensitivity * prevalence), (((sensitivity * prevalence) + (((1.0 - specificity)) * ((1.0 - prevalence))))))

def sensitivityPortabilityGap(sensSource, sensTarget):
    return _rt.rabs((sensTarget - sensSource))

def ppvPortabilityGap(sensitivity, specificity, prevalenceSource, prevalenceTarget):
    return _rt.rabs((metricPPV(sensitivity, specificity, prevalenceTarget) - metricPPV(sensitivity, specificity, prevalenceSource)))

def brierScoreMetric(p, y):
    return brierScore(p, y)

def ldBandReconstructionShare(decay, kappa):
    return _rt.rdiv((2.0 * _rt.arctan((((_rt.rdiv(((1.0 + decay)), ((1.0 - decay)))) * _rt.tan((_rt.rdiv((_rt.pi * kappa), 2.0))))))), _rt.pi)

def ldBandDetectionShare(decay, kappa):
    return (kappa - _rt.rdiv(((2.0 * decay) * _rt.sin(((_rt.pi * kappa)))), ((_rt.pi * ((1.0 + _rt.lpow(decay, 2.0)))))))

def ldPruningDetectionDeficit(decay, kappa):
    return _rt.rdiv(((2.0 * decay) * _rt.sin(((_rt.pi * kappa)))), ((_rt.pi * ((1.0 + _rt.lpow(decay, 2.0))))))

def ldPanelRetentionFraction(retainedMarkers, totalMarkers):
    return _rt.rdiv((retainedMarkers), (totalMarkers))

def ldBlockDetectionShare(recomb, Ne, retainedMarkers, totalMarkers):
    return ldBandDetectionShare((ldRetentionPerGen(recomb, Ne)), (ldPanelRetentionFraction(retainedMarkers, totalMarkers)))

def ldBlockPruningDeficit(recomb, Ne, retainedMarkers, totalMarkers):
    return ldPruningDetectionDeficit((ldRetentionPerGen(recomb, Ne)), (ldPanelRetentionFraction(retainedMarkers, totalMarkers)))

def ldTightLinkageDetectionShare(retainedMarkers, totalMarkers):
    return (ldPanelRetentionFraction(retainedMarkers, totalMarkers) - _rt.rdiv(_rt.sin(((_rt.pi * ldPanelRetentionFraction(retainedMarkers, totalMarkers)))), _rt.pi))

def targetCorrectionCurvature(weight, B, beta):
    return (lambda i: _rt.mul(weight[int(i)], coefficientEnergy((B(i)), beta)))

def targetCorrectionOptimum(B, beta, theta):
    return (lambda i: sharedCorrectionOptimum((B(i)), beta, theta))

def sharedCorrectionConsensus(curvature, optimum):
    return _rt.rdiv((sum((_rt.mul(curvature[int(i)], optimum[int(i)])) for i in range(int(len(curvature))))), sum((curvature[int(i)]) for i in range(int(len(curvature)))))

def sharedCorrectionSpread(curvature, optimum):
    return sum((_rt.mul(curvature[int(i)], _rt.lpow((_rt.sub(optimum[int(i)], sharedCorrectionConsensus(curvature, optimum))), 2.0))) for i in range(int(len(curvature))))

def sharedCorrectionCost(curvature, optimum, correction):
    return sum((_rt.mul(curvature[int(i)], _rt.lpow((_rt.sub(correction, optimum[int(i)])), 2.0))) for i in range(int(len(curvature))))

def effectMutualInformation(m, ρ):
    return (_rt.rdiv((-(m)), 2.0) * _rt.rlog(((1.0 - _rt.lpow(ρ, 2.0)))))

def portabilityGap(r2_source, r2_target):
    return (r2_source - r2_target)

def ldTaggingDecay(lam_LD, d):
    return _rt.rexp((((-lam_LD) * d)))

def combinedPortability(r2_src, lam_LD, lam_eff, d):
    return ((r2_src * ldTaggingDecay(lam_LD, d)) * _rt.lpow((_rt.rexp((((-lam_eff) * d)))), 2.0))

def snrPortabilityRatio(v_sig_s, v_noise_s, v_sig_t, v_noise_t):
    return _rt.rdiv((_rt.rdiv(v_sig_t, v_noise_t)), (_rt.rdiv(v_sig_s, v_noise_s)))

def f1Score(precision, sensitivity):
    return _rt.rdiv(((2.0 * precision) * sensitivity), ((precision + sensitivity)))

def uncorrectedBias(m):
    return (_rt._proj(m, 'c') * sum((_rt._proj(m, 'eigenvals')(i)) for i in range(int(_rt.sumdim('i', len(_rt._proj(m, 'eigenvals')))))))

def spectralResidualBiasEnergy(retention, bias):
    return sum((_rt.lpow((_rt.mul(retention[int(i)], bias[int(i)])), 2.0)) for i in range(int(len(retention))))

def pgsTestAxisBias(scale, expectedPhenotype, residualTargetAxis):
    return _rt.mul(scale, sum((_rt.mul(expectedPhenotype[int(i)], residualTargetAxis[int(i)])) for i in range(int(len(expectedPhenotype)))))

def ancestryGradientSusceptibility(markerAxisVariance, ancestryVariance):
    return (markerAxisVariance * ancestryVariance)

def pcTargetAxisEfficacy(uncorrectedSusceptibility, residualSusceptibility):
    return (1.0 - _rt.rdiv(residualSusceptibility, uncorrectedSusceptibility))

def ascertainmentAmplification(Φ, Λ):
    return _rt.rdiv((((1.0 + Φ) + Λ)), _rt.rsqrt(((1.0 + Λ))))

def pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ):
    return (_rt.rdiv((_rt.rsqrt(expectedSNPCount) * _rt.rsqrt(Hres)), effectSD) * ascertainmentAmplification(Φ, Λ))

def standardizedResidualPGSBias(expectedSNPCount, Hres, effectSD, Φ, Λ, confounding):
    return (pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ) * confounding)

def criticalConfoundingMagnitude(criticalSignal, expectedSNPCount, Hres, effectSD, Φ, Λ):
    return _rt.rdiv(criticalSignal, pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ))

def classMargin(cohort, i):
    return pcCorrectabilityMargin(_rt._proj(cohort, 'sampleSize'), (_rt._proj(cohort, 'effectiveMarkers')(i)), (_rt._proj(cohort, 'differentiation')(i)), _rt._proj(cohort, 'subgroupSize'))

def classInformation(cohort, i):
    return (_rt._proj(cohort, 'effectiveMarkers')(i) * _rt.lpow(_rt._proj(cohort, 'differentiation')(i), 2.0))

def informationMatchedWeight(cohort, i):
    return (_rt._proj(cohort, 'effectiveMarkers')(i) * _rt._proj(cohort, 'differentiation')(i))

def weightedSignal(cohort, weight):
    return sum((_rt.mul(weight[int(i)], _rt._proj(cohort, 'differentiation')(i))) for i in range(int(len(weight))))

def weightedNoise(cohort, weight):
    return sum((_rt.rdiv(_rt.lpow(weight[int(i)], 2.0), _rt._proj(cohort, 'effectiveMarkers')(i))) for i in range(int(len(weight))))

def weightedInformation(cohort, weight):
    return _rt.rdiv(_rt.lpow(weightedSignal(cohort, weight), 2.0), weightedNoise(cohort, weight))

def spikeOuter(v):
    return (lambda i, j: _rt.mul(v[int(i)], v[int(j)]))

def twoBlock(k, a, b):
    return (lambda i: (a if (i < k) else b))

def frobeniusForm(A, M):
    return sum((sum((_rt.mul(A[int(i)][int(j)], M[int(i)][int(j)])) for j in range(int(len(A))))) for i in range(int(len(A))))

def traceForm(M):
    return sum((M[int(i)][int(i)]) for i in range(int(len(M))))

def diagonalGapForm(i, j, M):
    return _rt.sub(M[int(i)][int(i)], M[int(j)][int(j)])

def traceWindowSpikeLoad(decay, nSites):
    return _rt.rdiv(ldPrecisionTrace(decay, nSites), (nSites))

def whitenedCapacity(headroom, decay):
    return _rt.rdiv(headroom, ldWhiteningGain(decay))

def subgroupContrast(n, m):
    return twoBlock(m, (_rt.rdiv((((n) - (m))), (n))), ((-(_rt.rdiv((m), (n))))))

def stratificationCertificateMargin(headroom, n, M, F, m):
    return (demographicSpike(n, F, m) - ((headroom + bbpProxyThreshold(n, M))))

def blockSpectrum(k, ε):
    return twoBlock(k, ε, 1.0)

def meffPerturbed(n):
    return blockSpectrum(n, (_rt.rinv((((n) + 1.0)))))

def meffFlat(n):
    return blockSpectrum(n, 1.0)

def meffSize(n):
    return (n + (n * n))

def weightedMean(w, c):
    return sum((_rt.mul(w[int(t)], c[int(t)])) for t in range(int(len(w))))

def energyWeightedVariance(w, c):
    return sum((_rt.mul(w[int(t)], _rt.lpow((_rt.sub(c[int(t)], weightedMean(w, c))), 2.0))) for t in range(int(len(w))))

def samplePCOverlapSq(n, M, spike):
    return (_rt.rdiv(((1.0 - _rt.rdiv((_rt.rdiv(n, M)), _rt.lpow(spike, 2.0)))), ((1.0 + _rt.rdiv((_rt.rdiv(n, M)), spike)))) if (bbpProxyThreshold(n, M) < spike) else 0.0)

def samplePCResidualAxisFraction(n, M, spike):
    return (1.0 - samplePCOverlapSq(n, M, spike))

def Calibrator_EmpiricalPCOverlapModel_residualBiasEnergy(m):
    return (_rt._proj(m, 'confoundingEnergy') - sum((_rt._proj(m, 'overlapSq')(i)) for i in range(int(_rt.sumdim('i', len(_rt._proj(m, 'overlapSq')))))))

def markerDangerIndex(confounding, n, markers):
    return (confounding * _rt.rsqrt((_rt.rdiv(markers, n))))

def effectiveSubgroupSize(n, m):
    return _rt.rdiv((m * ((n - m))), n)

def demographicSpike(n, F, m):
    return ((4.0 * F) * effectiveSubgroupSize(n, m))

def bbpProxyThreshold(n, M):
    return _rt.rsqrt((_rt.rdiv(n, M)))

def pcCorrectabilityMargin(n, M, F, m):
    return (demographicSpike(n, F, m) - bbpProxyThreshold(n, M))

def modeledPCResidualSusceptibility(markerAxisVariance, ancestryVariance, n, markers, spike):
    return ancestryGradientSusceptibility(markerAxisVariance, ((ancestryVariance * samplePCResidualAxisFraction(n, markers, spike))))

def calibrationInTheLarge(mean_observed, mean_predicted):
    return (mean_observed - mean_predicted)

def calibrationSlopeDeviation(slope):
    return _rt.rabs((slope - 1.0))

def toProfile(mom, link):
    return Calibrator_calibrationProfile(link, _rt._proj(mom, 'meanObserved'), _rt._proj(mom, 'meanPredicted'), _rt._proj(mom, 'slope'))

def Calibrator_identityCalibrationProfile(mean_observed, mean_predicted, slope):
    return Calibrator_calibrationProfile(0, mean_observed, mean_predicted, slope)

def logisticCalibrationProfile(mean_observed, mean_predicted, slope):
    return Calibrator_calibrationProfile(1, mean_observed, mean_predicted, slope)

def hosmerLemeshowContrib(observed, expected, n_group):
    return _rt.rdiv((n_group * _rt.lpow(((observed - expected)), 2.0)), ((expected * ((1.0 - expected)))))

def prevalenceLogit(pi):
    return _rt.rlog((_rt.rdiv(pi, ((1.0 - pi)))))

def prevalenceCITLShift(pi_source, pi_target):
    return (prevalenceLogit(pi_target) - prevalenceLogit(pi_source))

def Calibrator_CrossPopulationCalibrationShiftModel_observedMeanShift(m):
    return ((_rt._proj(m, 'prevalenceShift') + _rt._proj(m, 'environmentalObservedShift')) + _rt._proj(m, 'geneticObservedShift'))

def predictedMeanShift(m):
    return (_rt._proj(m, 'scoreMeanShift') + _rt._proj(m, 'deploymentInterceptShift'))

def Calibrator_CrossPopulationCalibrationShiftModel_observedMean(m, P):
    return (_rt._proj(m, 'baseObservedMean') + pair(0.0, Calibrator_CrossPopulationCalibrationShiftModel_observedMeanShift(m), P))

def Calibrator_CrossPopulationCalibrationShiftModel_predictedMean(m, P):
    return (_rt._proj(m, 'basePredictedMean') + pair(0.0, predictedMeanShift(m), P))

def Calibrator_CrossPopulationCalibrationShiftModel_calibrationProfile(m, P, link):
    return _rt._proj((calibrationMoments(m, P)), 'toProfile')(link)

def Calibrator_CrossPopulationCalibrationShiftModel_identityCalibrationProfile(m, P):
    return Calibrator_CrossPopulationCalibrationShiftModel_calibrationProfile(m, P, 0)

def deploymentIntercept(m, P):
    return (_rt._proj(m, 'baseDeploymentIntercept') + pair(0.0, _rt._proj(m, 'deploymentInterceptShift'), P))

def Calibrator_CrossPopulationMechanisticCalibrationModel_observedMeanShift(m):
    return ((_rt._proj(m, 'prevalenceShift') + _rt._proj(m, 'environmentalObservedShift')) + _rt._proj(m, 'geneticObservedShift'))

def Calibrator_CrossPopulationMechanisticCalibrationModel_scoreMean(m, P):
    return sourceWeightedTagScore(_rt._proj(m, 'metric'), (_rt._proj(m, 'tagMean')(P)))

def scoreMeanShift(m):
    return (Calibrator_CrossPopulationMechanisticCalibrationModel_scoreMean(m, 1) - Calibrator_CrossPopulationMechanisticCalibrationModel_scoreMean(m, 0))

def Calibrator_CrossPopulationMechanisticCalibrationModel_predictedMean(m, P):
    return (deploymentIntercept(m, P) + Calibrator_CrossPopulationMechanisticCalibrationModel_scoreMean(m, P))

def Calibrator_CrossPopulationMechanisticCalibrationModel_observedMean(m, P):
    return (_rt._proj(m, 'baseObservedMean') + pair(0.0, Calibrator_CrossPopulationMechanisticCalibrationModel_observedMeanShift(m), P))

def calibrationSlope(m, P):
    return calibrationSlopeFromSourceWeights(_rt._proj(m, 'metric'), P)

def Calibrator_CrossPopulationMechanisticCalibrationModel_calibrationProfile(m, P, link):
    return _rt._proj(_rt._proj(m, 'toShiftModel'), 'calibrationProfile')(P, link)

def Calibrator_CrossPopulationMechanisticCalibrationModel_identityCalibrationProfile(m, P):
    return Calibrator_CrossPopulationMechanisticCalibrationModel_calibrationProfile(m, P, 0)

def tagMeanAt(m, P, t):
    return pair(_rt._proj(m, 'baseTagMean'), (_rt._proj(m, 'targetTagMeanAt')(t)), P)

def deploymentInterceptAt(m, P, t):
    return (_rt._proj(m, 'baseDeploymentIntercept') + pair(0.0, (_rt._proj(m, 'deploymentInterceptShiftAt')(t)), P))

def observedMeanShiftAt(m, t):
    return ((_rt._proj(m, 'prevalenceShiftAt')(t) + _rt._proj(m, 'environmentalObservedShiftAt')(t)) + _rt._proj(m, 'geneticObservedShiftAt')(t))

def scoreMeanAt(m, P, t):
    return sourceWeightedTagScore((_rt._proj(_rt._proj(m, 'metric'), 'toMetricModelAt')(t)), (tagMeanAt(m, P, t)))

def scoreMeanShiftAt(m, t):
    return (scoreMeanAt(m, 1, t) - scoreMeanAt(m, 0, t))

def predictedMeanAt(m, P, t):
    return (deploymentInterceptAt(m, P, t) + scoreMeanAt(m, P, t))

def observedMeanAt(m, P, t):
    return (_rt._proj(m, 'baseObservedMean') + pair(0.0, (observedMeanShiftAt(m, t)), P))

def targetCalibrationProfileAtGeneration(m, t, link):
    return _rt._proj((toMechanisticCalibrationModelAt(m, t)), 'calibrationProfile')(1, link)

def targetIdentityCalibrationProfileAtGeneration(m, t):
    return targetCalibrationProfileAtGeneration(m, t, 0)

def prevalenceLogisticCalibrationProfile(pi_source, pi_target, slope):
    return logisticCalibrationProfile((prevalenceLogit(pi_target)), (prevalenceLogit(pi_source)), slope)

def interceptRecalibrated(pgs, new_intercept):
    return (new_intercept + pgs)

def logisticRecalibrated(pgs, a, b):
    return (a + (b * pgs))

def recalibratedCalibrationSlope(slope, fittedSlope):
    return _rt.rdiv(slope, fittedSlope)

def recalibrationTraceMSELowerBound(nEvents, nParams, infoPerEvent):
    return _rt.rdiv(nParams, ((nEvents * infoPerEvent)))

def requiredEventsForRecalibration(nParams, infoPerEvent, targetTraceMSE):
    return _rt.rdiv(nParams, ((infoPerEvent * targetTraceMSE)))

def requiredTargetCohortSizeForRecalibration(nParams, prevalence, infoPerEvent, targetTraceMSE):
    return _rt.rdiv(requiredEventsForRecalibration(nParams, infoPerEvent, targetTraceMSE), prevalence)

def classifiedHighRisk(threshold, predictedRisk):
    return (threshold < predictedRisk)

def nri(up_events, down_events, up_nonevents, down_nonevents, n_events, n_nonevents):
    return (_rt.rdiv(((up_events - down_events)), n_events) + _rt.rdiv(((down_nonevents - up_nonevents)), n_nonevents))

def nriFromDownwardInterceptRecalibration(μevent, μnonevent, threshold, δ):
    return nri(0.0, (downReclassificationRate(μevent, threshold, δ)), 0.0, (downReclassificationRate(μnonevent, threshold, δ)), 1.0, 1.0)

def reclassifiedBandEventPrevalence(π, μevent, μnonevent, threshold, δ):
    return _rt.rdiv(((_rt.pi * thresholdBandRate(μevent, threshold, δ))), (((_rt.pi * thresholdBandRate(μevent, threshold, δ)) + (((1.0 - _rt.pi)) * thresholdBandRate(μnonevent, threshold, δ)))))

def qalyContributionAtTime(model, path, t):
    return ((_rt._proj(model, 'discount')(t) * _rt._proj(path, 'followupWeight')(t)) * (((_rt._proj(path, 'eventProb')(t) * _rt._proj(path, 'treatmentBenefit')(t)) - _rt._proj(path, 'treatmentHarm')(t))))

def receivesTreatment(model, path):
    return (0.0 < treatmentMargin(model, path))

def qalyGainUnderDecision(model, truePath, predictedPath):
    return by(classical, exact, (treatmentMargin(model, truePath) if receivesTreatment(model, predictedPath) else 0.0))

def qalyLoss(model, truePath, predictedPath):
    return (qalyGainUnderDecision(model, truePath, truePath) - qalyGainUnderDecision(model, truePath, predictedPath))

def qalyDecisionRegretMargin(model, truePath, predictedPath):
    return by(classical, exact, (_rt.rmax(((-treatmentMargin(model, truePath))), 0.0) if receivesTreatment(model, predictedPath) else _rt.rmax((treatmentMargin(model, truePath)), 0.0)))

def screeningUtilityFromCounts(model, tp, fp, n):
    return ((_rt._proj(model, 'benefit') * (_rt.rdiv(tp, n))) - (_rt._proj(model, 'harm') * (_rt.rdiv(fp, n))))

def screeningUtilityFromRates(model, sens, spec, prevalence):
    return (((sens * prevalence) * _rt._proj(model, 'benefit')) - ((((1.0 - spec)) * ((1.0 - prevalence))) * _rt._proj(model, 'harm')))

def screeningQalyGain(sens, spec, prevalence, benefit, harm):
    return screeningUtilityFromRates((qalyScreeningDecisionModel(benefit, harm)), sens, spec, prevalence)

def decisionCurveNetBenefit(tp, fp, n, t):
    return screeningUtilityFromCounts((decisionCurveScreeningModel(t)), tp, fp, n)

def thresholdQalyLoss(model, trueRisk, predictedRisk):
    return (thresholdQalyGainUnderDecision(model, trueRisk, trueRisk) - thresholdQalyGainUnderDecision(model, trueRisk, predictedRisk))

def thresholdDecisionRegretMargin(model, trueRisk, predictedRisk):
    return by(classical, exact, (_rt.rmax(((_rt._proj(model, 'threshold') - trueRisk)), 0.0) if classifiedHighRisk(_rt._proj(model, 'threshold'), predictedRisk) else _rt.rmax(((trueRisk - _rt._proj(model, 'threshold'))), 0.0)))

def scalarPermeability(covariance, covarianceDerivative):
    return ((_rt.rdiv(1.0, 2.0)) * _rt.lpow((_rt.rdiv(covarianceDerivative, covariance)), 2.0))

def centeredSquareVarianceFromMoments(secondMoment, fourthMoment):
    return (fourthMoment - _rt.lpow(secondMoment, 2.0))

def covarianceScoreInformationFromMoments(covariance, covarianceDerivative, secondMoment, fourthMoment):
    return (_rt.lpow((_rt.rdiv(covarianceDerivative, ((2.0 * _rt.lpow(covariance, 2.0))))), 2.0) * centeredSquareVarianceFromMoments(secondMoment, fourthMoment))

def diagonalPermeability(covariance, covarianceDerivative):
    return sum((scalarPermeability((covariance[int(i)]), (covarianceDerivative[int(i)]))) for i in range(int(len(covariance))))

def totalGaussianInformation(m, covariance, covarianceDerivative):
    return (m * scalarPermeability(covariance, covarianceDerivative))

def gaussianCovarianceTangentEstimatorVariance(m, covariance, covarianceDerivative):
    return _rt.rdiv((2.0 * _rt.lpow(covariance, 2.0)), ((m * _rt.lpow(covarianceDerivative, 2.0))))

def lagSensitivityMatrix(lag, covarianceDerivative):
    return (lambda i, j: covarianceDerivative((lag(i)), j))

def lagObservationDerivative(lag, covarianceDerivative, tangent):
    return _rt._proj((lagSensitivityMatrix(lag, covarianceDerivative)), 'mulVec')(tangent)

def lagCompletionPermeability(covariance, lag, covarianceDerivative, tangent):
    return diagonalPermeability(covariance, (lagObservationDerivative(lag, covarianceDerivative, tangent)))

def quadraticChannel(θ):
    return _rt.lpow(θ, 2.0)

def neutralPortabilityRatioLD(fst_additional, ld_factor):
    return (((1.0 - fst_additional)) * ld_factor)

def neutralDriftFactor(Ne, t):
    return _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))), t)

def selectedDriftFactor(Ne, t, s_correction):
    return _rt.lpow((((1.0 - _rt.rdiv(1.0, ((2.0 * Ne)))) + s_correction)), t)

def fstFromDriftFactor(driftFactor):
    return (1.0 - driftFactor)

def causalPortabilityFromLocalFst(sourceSquaredEffect, fstCausal):
    return _rt.rdiv((sum((_rt.mul(sourceSquaredEffect[int(i)], (_rt.sub(1.0, fstCausal[int(i)])))) for i in range(int(len(sourceSquaredEffect))))), (sum((sourceSquaredEffect[int(i)]) for i in range(int(len(sourceSquaredEffect))))))

def qst(V_between, V_within):
    return _rt.rdiv(V_between, ((V_between + (2.0 * V_within))))

def pgsDriftVariance_one_pop(V_A, fst):
    return (fst * V_A)

def pgsDriftVarianceFromLoci(fst, β):
    n = float(len(β))
    return sum((_rt.mul(fst, _rt.lpow(β[int(i)], 2.0))) for i in range(int(len(β))))

def pgsDiffVariance_two_pop(V_A, fst):
    return (2.0 * pgsDriftVariance_one_pop(V_A, fst))

def expectedPGSDiffVariance(V_A, fst):
    return ((V_A * 2.0) * fst)

def effectCorrelationStabilizingDriftSelection(d, s, N):
    return (1.0 - _rt.rdiv(d, ((1.0 + (s * N)))))

def effectCorrelationFluctuating(d, f, N):
    return _rt.rmax(((-1.0)), ((1.0 - (d * ((1.0 + (f * N)))))))

def expectedSquaredEffect(h2, M):
    return _rt.rdiv(h2, M)

def spikeAndSlabVariance(pi, sigma_sq_large, sigma_sq_small):
    return ((pi * sigma_sq_large) + (((1.0 - pi)) * sigma_sq_small))

def effectivePolygenicity(sum_beta_sq, sum_beta_fourth):
    return _rt.rdiv(_rt.lpow(sum_beta_sq, 2.0), sum_beta_fourth)

def effectivePolygenicityOfEffects(beta):
    return effectivePolygenicity((sum((_rt.lpow(beta[int(j)], 2.0)) for j in range(int(len(beta))))), (sum((_rt.lpow(beta[int(j)], 4.0)) for j in range(int(len(beta))))))

def sourceEffectMass(model):
    return sum((_rt._proj(model, 'sourceSquaredEffect')(j)) for j in range(int(_rt.sumdim('j', len(_rt._proj(model, 'sourceSquaredEffect'))))))

def targetRetainedEffectMass(model):
    return sum((_rt._proj(model, 'targetRetainedSquaredEffect')(j)) for j in range(int(_rt.sumdim('j', len(_rt._proj(model, 'targetRetainedSquaredEffect'))))))

def lostEffectMass(model):
    return (sourceEffectMass(model) - targetRetainedEffectMass(model))

def relativePortabilityLoss(model):
    return _rt.rdiv(lostEffectMass(model), sourceEffectMass(model))

def portabilityScore(model):
    return _rt.rdiv(targetRetainedEffectMass(model), sourceEffectMass(model))

def meanAbsoluteEffect(beta):
    q = float(len(beta))
    return _rt.rdiv((sum((_rt.rabs(beta[int(j)])) for j in range(int(len(beta))))), q)

def nonsmoothSummaryRisk(q):
    return _rt.rdiv(1.0, _rt.rlog(q))

def gradeCertifiedRisk(q, K, c):
    return _rt.lpow(q, ((-(_rt.rdiv(c, K)))))

def certificateDeficit(q, K, c):
    return _rt.rdiv(nonsmoothSummaryRisk(q), gradeCertifiedRisk(q, K, c))

def heritabilityEnrichment(h2_cat, M_cat, h2_total, M_total):
    return _rt.rdiv((_rt.rdiv(h2_cat, M_cat)), (_rt.rdiv(h2_total, M_total)))

def predictedPortability(model):
    return portabilityScore(model)

def weightedRetentionUpperBound(model, retentionUpper):
    return _rt.rdiv((sum((_rt.mul(retentionUpper[int(j)], _rt._proj(model, 'sourceSquaredEffect')(j))) for j in range(int(len(retentionUpper))))), sourceEffectMass(model))

def rgFstWeightedUpperBound(model, rgUpper, fstLower):
    return weightedRetentionUpperBound(model, ((lambda j: _rt.mul(_rt.lpow((rgUpper[int(j)]), 2.0), (_rt.sub(1.0, fstLower[int(j)]))))))

def standardizedSquare(h, g):
    return _rt.rdiv(_rt.lpow((centeredAltAlleleCount(h, g)), 2.0), genotypeVariance(h))

def mellinDrift(h):
    return sum((((genotypeProb(h, g) * standardizedSquare(h, g)) * _rt.rlog((standardizedSquare(h, g))))) for g in range(int(3)))

def hweMellinDrift(q):
    return ((_rt.lpow(((1.0 - (2.0 * q))), 2.0) * _rt.rlog((_rt.rdiv(_rt.lpow(((1.0 - (2.0 * q))), 2.0), (((2.0 * q) * ((1.0 - q)))))))) + (((4.0 * q) * ((1.0 - q))) * _rt.rlog(2.0)))

def maxSafeEpistaticOrder(N, q):
    return _rt.rdiv(_rt.rlog(N), hweMellinDrift(q))

def hweLatticeCondition(q):
    return (_rt.lpow(((1.0 - (2.0 * q))), 2.0) == ((4.0 * q) * ((1.0 - q))))

def latticeCriticalMaf():
    return _rt.rdiv(((2.0 - _rt.rsqrt(2.0))), 4.0)

def mellinJetVariance(h):
    return ((sum((((genotypeProb(h, g) * standardizedSquare(h, g)) * _rt.lpow((_rt.rlog((standardizedSquare(h, g)))), 2.0))) for g in range(int(3)))) - _rt.lpow(mellinDrift(h), 2.0))

def hweMellinJetVariance(q):
    return ((((((2.0 * q) * ((1.0 - q))) * _rt.lpow((_rt.rlog((_rt.rdiv((2.0 * q), ((1.0 - q)))))), 2.0)) + (_rt.lpow(((1.0 - (2.0 * q))), 2.0) * _rt.lpow((_rt.rlog((_rt.rdiv(_rt.lpow(((1.0 - (2.0 * q))), 2.0), (((2.0 * q) * ((1.0 - q)))))))), 2.0))) + (((2.0 * q) * ((1.0 - q))) * _rt.lpow((_rt.rlog((_rt.rdiv((2.0 * ((1.0 - q))), q)))), 2.0))) - _rt.lpow(hweMellinDrift(q), 2.0))

def hardCallLatticeSpan():
    return _rt.rlog((_rt.rdiv(((1.0 - latticeCriticalMaf)), latticeCriticalMaf)))

def hardCallLatticeIndex(_e):
    _t = [(-1.0), 0.0, 1.0]
    return _t[_rt._ix(_e, 3, 'hardCallLatticeIndex')]

def standardizedFourthMoment(h):
    return sum(((genotypeProb(h, g) * _rt.lpow(standardizedSquare(h, g), 2.0))) for g in range(int(3)))

def neiFst(H_T, H_S):
    return _rt.rdiv(((H_T - H_S)), H_T)

def neiGstFromFrequencies(p_1, p_2):
    p_bar = _rt.rdiv(((p_1 + p_2)), 2.0)
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), (((4.0 * p_bar) * ((1.0 - p_bar)))))

def expectedHeterozygosity(θ):
    return _rt.rdiv(θ, ((1.0 + θ)))

def coalFst(t, Ne):
    return _rt.rdiv(t, ((t + (2.0 * Ne))))

def continentIslandStepSelectionFirst(s, m, p):
    return (((1.0 - m)) * (_rt.rdiv((p * ((1.0 + s))), ((1.0 + (s * p))))))

def continentIslandStepMigrationFirst(s, m, p):
    return _rt.rdiv((((((1.0 - m)) * p)) * ((1.0 + s))), ((1.0 + (s * ((((1.0 - m)) * p))))))

def selectionMigrationEquilibrium(s, m):
    return _rt.rmax(0.0, (_rt.rdiv((((s - m) - (m * s))), s)))

def selectionMigrationEquilibriumMigrationFirst(s, m):
    return _rt.rmax(0.0, (_rt.rdiv((((s - m) - (m * s))), ((s * ((1.0 - m)))))))

def wrightFIT(f_IS, f_ST):
    return (1.0 - (((1.0 - f_IS)) * ((1.0 - f_ST))))

def heterozygosityLossFromDrift(t, Ne):
    return (1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))), t))

def scaledIdentityStep(scaledRate, F):
    return (1.0 - (scaledRate * F))

def fstMutationDriftTransient(θ, t, Ne):
    return (fstMutationDriftEquilibrium(θ) * ((1.0 - _rt.rexp((_rt.rdiv(((-((1.0 + θ))) * t), ((2.0 * Ne))))))))

def expectedNewMutations(θ, t):
    return (_rt.rdiv(θ, 2.0) * t)

def sharedLDFractionFromMutation(θ, t):
    return _rt.rexp(((-(expectedNewMutations(θ, t)))))

def islandDemeCorrection(d):
    return _rt.lpow((_rt.rdiv(d, ((d - 1.0)))), 2.0)

def islandFstFiniteDemes(Ne, m, d):
    return _rt.rdiv(1.0, ((1.0 + (((4.0 * Ne) * m) * islandDemeCorrection(d)))))

def fstMigrationMutationEquilibrium(Ne, m, μ):
    return _rt.rdiv(1.0, (((1.0 + ((4.0 * Ne) * m)) + ((4.0 * Ne) * μ))))

def steppingStoneCharacteristicLength(m, σ_sq, μ):
    return _rt.rsqrt((_rt.rdiv((m * σ_sq), ((2.0 * μ)))))

def alleleFreqAfterMigration(p_0, p_c, m, t):
    return (p_c + (((p_0 - p_c)) * _rt.lpow(((1.0 - m)), t)))

def ldCorrelationFromMigration(M):
    return _rt.rdiv(_rt.lpow(M, 2.0), _rt.lpow(((1.0 + M)), 2.0))

def hetRecurrence(Ne, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * _prev)
    return _prev

def fstDerived(Ne, t):
    return (1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))), t))

def hetMutationDriftRecurrence(Ne, mu, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = ((((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * _prev) + ((2.0 * mu) * ((1.0 - _prev))))
    return _prev

def Calibrator_hetDecayFactor(Ne, θ):
    return hetDecayFromScaled(Ne, θ)

def hetMutationRecurrence(lam, Hstar, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = ((lam * _prev) + (((1.0 - lam)) * Hstar))
    return _prev

def fstFromHetRatio(H, H_0):
    return (1.0 - _rt.rdiv(H, H_0))

def fstMutationDriftTransientDiscrete(θ, Ne, t):
    return (fstMutationDriftEquilibrium(θ) * ((1.0 - _rt.lpow(Calibrator_hetDecayFactor(Ne, θ), t))))

def neutralPortability(r2_0, fst):
    return (r2_0 * _rt.rmax(0.0, ((1.0 - (2.0 * fst)))))

def stabilizingPortability(r2_0, fst, strength):
    return (neutralPortability(r2_0, fst) * _rt.rexp((((-strength) * fst))))

def diversifyingPortability(r2_0, fst, lam_turn):
    return (neutralPortability(r2_0, fst) * _rt.lpow((_rt.rexp((((-lam_turn) * fst)))), 2.0))

def coalescenceSurvivalFromHazard(hazard, t):
    return _rt.rexp(((-(integratedCoalescentHazard(hazard, t)))))

def coalescenceCdfFromHazard(hazard, t):
    return (1.0 - coalescenceSurvivalFromHazard(hazard, t))

def coalescentTau(t, Ne):
    return _rt.rdiv(t, ((2.0 * Ne)))

def fstFromTau(tau):
    return _rt.rdiv(tau, ((1.0 + tau)))

def fstFromGenerations(t, Ne):
    return fstFromTau((coalescentTau(t, Ne)))

def pairwiseFstFromBranches(fstS, fstT):
    return (1.0 - (((1.0 - fstS)) * ((1.0 - fstT))))

def pairwiseFstFromBranchTaus(tauS, tauT):
    return fstFromTau(((tauS + tauT)))

def fstEqLimitLowMutationManyDemes(m):
    return _rt.rdiv(1.0, ((1.0 + scaledMigrationRate(_rt._proj(m, 'Ne'), _rt._proj(m, 'mig')))))

def hudsonFstFromCoalescenceTimes(ETss, ETst):
    return (1.0 - _rt.rdiv(ETss, ETst))

def delta(d):
    return hudsonFstFromCoalescenceTimes(_rt._proj(d, 'ETss'), _rt._proj(d, 'ETst'))

def twoDemeIMFirstStepSame(M, _ETss, ETst):
    return (_rt.rdiv(1.0, ((1.0 + M))) + ((_rt.rdiv(M, ((1.0 + M)))) * ETst))

def twoDemeIMFirstStepDiff(M, ETss, _ETst):
    return (_rt.rdiv(1.0, M) + ETss)

def twoDemeIMEquilibriumETss(_M):
    return 2.0

def twoDemeIMEquilibriumETst(M):
    return _rt.rdiv((((2.0 * M) + 1.0)), M)

def twoDemeIMEquilibriumDelta(M):
    return _rt.rdiv(1.0, (((2.0 * M) + 1.0)))

def hetStepWithMutation(Ne, mu, H):
    return ((((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * H) + ((2.0 * mu) * ((1.0 - H))))

def hetTrajectory(Ne, mu, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = hetStepWithMutation(Ne, mu, (_prev))
    return _prev

def hetMutationFloor(Ne, mu):
    return _rt.rdiv(((4.0 * Ne) * mu), ((1.0 + ((4.0 * Ne) * mu))))

def retention(r):
    return _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * _rt._proj(r, 'Ne')))))), _rt._proj(r, 'horizon'))

def targetHet(r):
    return (_rt._proj(r, 'H₀') * retention(r))

def pgsVarianceFromHet(β_sq_sum, het):
    return (β_sq_sum * het)

def targetHetFromFst(het_source, fst):
    return (het_source * ((1.0 - fst)))

def presentDayPGSVariance(V_A, fst):
    return pgsVarianceFromHet(V_A, ((1.0 - fst)))

def wrightFisherDriftRetention(N, t):
    return _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * (N)))))), t)

def wrightFisherHeterozygosityLoss(N, t):
    return (1.0 - wrightFisherDriftRetention(N, t))

def Var_Delta_Mu(V_A, fst):
    return ((2.0 * fst) * V_A)

def Expected_Abs_Shift(V_A, fstS, fstT):
    return (_rt.rsqrt((Var_Delta_Mu(V_A, ((fstS + fstT))))) * _rt.rsqrt((_rt.rdiv(2.0, _rt.pi))))

def presentDaySignalToNoise(V_A, V_E, fst):
    return _rt.rdiv(presentDayPGSVariance(V_A, fst), V_E)

def presentDayR2(V_A, V_E, fst):
    return r2FromSignalVariance((presentDayPGSVariance(V_A, fst)), V_E)

def presentDayGaussianAUC(V_A, V_E, fst):
    return Phi((_rt.rsqrt((_rt.rdiv(presentDaySignalToNoise(V_A, V_E, fst), 2.0)))))

def presentDayEqualVarianceGaussianAUC(V_A, V_E, fst):
    return presentDayGaussianAUC(V_A, V_E, fst)

def realWorldPGSVariance(V_A, fst, rhoSq):
    return ((rhoSq * ((1.0 - fst))) * V_A)

def sourceERMWeights(sigmaObsSource, crossSource):
    return _rt._proj(_rt.rinv(sigmaObsSource), 'mulVec')(crossSource)

def sigmaTagCausalSourceAt(m, P):
    return (((_rt._proj(m, 'directCausal')(P) + _rt._proj(m, 'novelDirectCausal')(P))) + ((_rt._proj(m, 'proxyTagging')(P) + _rt._proj(m, 'novelProxyTagging')(P))))

def totalEffect(m, P):
    return (_rt._proj(m, 'beta')(P) + _rt._proj(m, 'novelCausalEffect')(P))

def targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, w):
    return _rt.sub(_rt.add(noiseVar, _rt.dotProduct(w, (_rt.mulVec(sigmaObsTarget, w)))), _rt.mul(2.0, _rt.dotProduct(w, crossTarget)))

def crossCovariance(m, P):
    return (_rt._proj((sigmaTagCausalSourceAt(m, P)), 'mulVec')((totalEffect(m, P))) + _rt._proj(m, 'contextCross')(P))

def sourceWeightsFromExplicitDrivers(m):
    return sourceERMWeights((_rt._proj(m, 'sigmaTag')(0)), (crossCovariance(m, 0)))

def sourceWeightedTagScore(m, tagState):
    return _rt.dotProduct((sourceWeightsFromExplicitDrivers(m)), tagState)

def taggingProjection(m, P):
    return _rt._proj((sigmaTagCausalSourceAt(m, P)), 'mulVec')((totalEffect(m, P)))

def targetEffectHeterogeneity(m):
    return (totalEffect(m, 1) - (_rt._proj(m, 'beta')(0)))

def targetSourceEffectProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((_rt._proj(m, 'beta')(0)))

def targetEffectHeterogeneityProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((targetEffectHeterogeneity(m)))

def targetNovelMutationEffectProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((_rt._proj(m, 'novelCausalEffect')(1)))

def directCausalProjection(m, P):
    return _rt._proj(((_rt._proj(m, 'directCausal')(P) + _rt._proj(m, 'novelDirectCausal')(P))), 'mulVec')((totalEffect(m, P)))

def proxyTaggingProjection(m, P):
    return _rt._proj(((_rt._proj(m, 'proxyTagging')(P) + _rt._proj(m, 'novelProxyTagging')(P))), 'mulVec')((totalEffect(m, P)))

def scoreVarianceFromSourceWeights(m, P):
    wS = sourceWeightsFromExplicitDrivers(m)
    return _rt.dotProduct(wS, (_rt._proj((_rt._proj(m, 'sigmaTag')(P)), 'mulVec')(wS)))

def predictiveCovarianceFromSourceWeights(m, P):
    return _rt.dotProduct((sourceWeightsFromExplicitDrivers(m)), (crossCovariance(m, P)))

def calibrationSlopeFromSourceWeights(m, P):
    return _rt.rdiv(predictiveCovarianceFromSourceWeights(m, P), scoreVarianceFromSourceWeights(m, P))

def brokenTaggingResidual(m):
    delta = _rt._proj((((sigmaTagCausalSourceAt(m, 0)) - (sigmaTagCausalSourceAt(m, 1)))), 'mulVec')((totalEffect(m, 1)))
    return _rt.dotProduct(delta, delta)

def ancestrySpecificLDResidual(m):
    wS = sourceWeightsFromExplicitDrivers(m)
    delta = _rt._proj((((_rt._proj(m, 'sigmaTag')(0)) - (_rt._proj(m, 'sigmaTag')(1)))), 'mulVec')(wS)
    return _rt.dotProduct(delta, delta)

def sourceSpecificOverfitResidual(m):
    delta = ((_rt._proj(m, 'contextCross')(0)) - (_rt._proj(m, 'contextCross')(1)))
    return _rt.dotProduct(delta, delta)

def novelUntaggablePhenotypeResidual(m):
    return _rt._proj(m, 'novelUntaggablePhenotypeVarianceTarget')

def irreducibleTargetResidualBurden(m):
    return (((brokenTaggingResidual(m) + ancestrySpecificLDResidual(m)) + sourceSpecificOverfitResidual(m)) + novelUntaggablePhenotypeResidual(m))

def residualBurden(m, P):
    return pair(0.0, (irreducibleTargetResidualBurden(m)), P)

def effectiveOutcomeVariance(m, P):
    return ((_rt._proj(m, 'outcomeVariance')(P)) + residualBurden(m, P))

def explainedSignalVarianceFromSourceWeights(m, P):
    return _rt.rdiv(_rt.lpow((predictiveCovarianceFromSourceWeights(m, P)), 2.0), scoreVarianceFromSourceWeights(m, P))

def r2FromSourceWeights(m, P):
    return _rt.rdiv(explainedSignalVarianceFromSourceWeights(m, P), effectiveOutcomeVariance(m, P))

def residualVarianceFromSourceWeights(m, P):
    return (effectiveOutcomeVariance(m, P) - explainedSignalVarianceFromSourceWeights(m, P))

def sourceCalibratedBrierFromSourceWeightsAtPrevalence(m, π):
    return calibratedBrierFromVariances(_rt.pi, (explainedSignalVarianceFromSourceWeights(m, 0)), (residualVarianceFromSourceWeights(m, 0)))

def targetCalibratedBrierFromSourceWeights(m):
    return calibratedBrierFromVariances(_rt._proj(m, 'targetPrevalence'), (explainedSignalVarianceFromSourceWeights(m, 1)), (residualVarianceFromSourceWeights(m, 1)))

def ldCorrelationDecay(distance, fstGap, lambda_):
    return _rt.rexp(((-(((lambda_ * fstGap) * distance)))))

def Calibrator_GenerationalPopGenParameters_bigM(g):
    return scaledMigrationRate(_rt._proj(g, 'Ne'), _rt._proj(g, 'mig'))

def tauAt(g, t):
    return _rt.rdiv((t), ((2.0 * _rt._proj(g, 'Ne'))))

def Calibrator_GenerationalPopGenParameters_hetDecayFactor(g):
    return hetDecayFromScaled(_rt._proj(g, 'Ne'), Calibrator_GenerationalPopGenParameters_theta(g))

def fstTransientAt(g, t):
    return ((_rt.rdiv(1.0, (((1.0 + Calibrator_GenerationalPopGenParameters_theta(g)) + Calibrator_GenerationalPopGenParameters_bigM(g))))) * ((1.0 - _rt.lpow(Calibrator_GenerationalPopGenParameters_hetDecayFactor(g), t))))

def mutationSharedRetentionAt(g, t):
    return _rt.rexp((((-Calibrator_GenerationalPopGenParameters_theta(g)) * tauAt(g, t))))

def migrationSharedBoostAt(g, t):
    return (1.0 + _rt.rdiv((Calibrator_GenerationalPopGenParameters_bigM(g) * tauAt(g, t)), ((1.0 + Calibrator_GenerationalPopGenParameters_bigM(g)))))

def alleleFreqMismatchPenalty(pSource, pTarget):
    return _rt.rexp(((-_rt.rabs((pTarget - pSource)))))

def betaTargetAt(m, t):
    return ((_rt._proj(m, 'betaSource') + _rt._proj(m, 'targetEffectHeterogeneityAt')(t)) + _rt._proj(m, 'novelCausalEffectTargetAt')(t))

def tagAlleleFreqTargetAt(m, t, i):
    return (_rt._proj(m, 'tagAlleleFreqStandingTargetAt')(t, i) + _rt._proj(m, 'tagAlleleFreqMutationShiftAt')(t, i))

def causalAlleleFreqTargetAt(m, t, j):
    return (_rt._proj(m, 'causalAlleleFreqStandingTargetAt')(t, j) + _rt._proj(m, 'causalAlleleFreqMutationShiftAt')(t, j))

def tagAlleleFreqRetentionAt(m, t, i):
    return alleleFreqMismatchPenalty((_rt._proj(m, 'tagAlleleFreqSource')(i)), (tagAlleleFreqTargetAt(m, t, i)))

def causalAlleleFreqRetentionAt(m, t, j):
    return alleleFreqMismatchPenalty((_rt._proj(m, 'causalAlleleFreqSource')(j)), (causalAlleleFreqTargetAt(m, t, j)))

def novelVariantInnovationAt(g, t):
    return (1.0 - mutationSharedRetentionAt(g, t))

def jointTagLDKernelAt(m, t, i, j):
    return ((((ldCorrelationDecay((_rt._proj(m, 'tagDistance')(i, j)), (_rt._proj(_rt._proj(m, 'popGen'), 'fstTransientAt')(t)), _rt._proj(_rt._proj(m, 'popGen'), 'recomb')) * _rt._proj(_rt._proj(m, 'popGen'), 'mutationSharedRetentionAt')(t)) * _rt._proj(_rt._proj(m, 'popGen'), 'migrationSharedBoostAt')(t)) * tagAlleleFreqRetentionAt(m, t, i)) * tagAlleleFreqRetentionAt(m, t, j))

def jointDirectCausalKernelAt(m, t, i, j):
    return (((_rt._proj(_rt._proj(m, 'popGen'), 'mutationSharedRetentionAt')(t) * _rt._proj(_rt._proj(m, 'popGen'), 'migrationSharedBoostAt')(t)) * tagAlleleFreqRetentionAt(m, t, i)) * causalAlleleFreqRetentionAt(m, t, j))

def jointProxyTaggingKernelAt(m, t, i, j):
    return ((((ldCorrelationDecay((_rt._proj(m, 'tagCausalDistance')(i, j)), (_rt._proj(_rt._proj(m, 'popGen'), 'fstTransientAt')(t)), _rt._proj(_rt._proj(m, 'popGen'), 'recomb')) * _rt._proj(_rt._proj(m, 'popGen'), 'mutationSharedRetentionAt')(t)) * _rt._proj(_rt._proj(m, 'popGen'), 'migrationSharedBoostAt')(t)) * tagAlleleFreqRetentionAt(m, t, i)) * causalAlleleFreqRetentionAt(m, t, j))

def jointNovelDirectCausalKernelAt(m, t, i, j):
    return (((novelVariantInnovationAt(_rt._proj(m, 'popGen'), t) * _rt.rinv((_rt._proj(_rt._proj(m, 'popGen'), 'migrationSharedBoostAt')(t)))) * tagAlleleFreqRetentionAt(m, t, i)) * causalAlleleFreqRetentionAt(m, t, j))

def jointNovelProxyTaggingKernelAt(m, t, i, j):
    return ((((ldCorrelationDecay((_rt._proj(m, 'tagCausalDistance')(i, j)), (_rt._proj(_rt._proj(m, 'popGen'), 'fstTransientAt')(t)), _rt._proj(_rt._proj(m, 'popGen'), 'recomb')) * novelVariantInnovationAt(_rt._proj(m, 'popGen'), t)) * _rt.rinv((_rt._proj(_rt._proj(m, 'popGen'), 'migrationSharedBoostAt')(t)))) * tagAlleleFreqRetentionAt(m, t, i)) * causalAlleleFreqRetentionAt(m, t, j))

def sigmaTagTargetAt(m, t):
    return (lambda i, j: (_rt._proj(m, 'sigmaTagSource')(i, j) * jointTagLDKernelAt(m, t, i, j)))

def directCausalTargetAt(m, t):
    return (lambda i, j: (_rt._proj(m, 'directCausalSource')(i, j) * jointDirectCausalKernelAt(m, t, i, j)))

def novelDirectCausalTargetAt(m, t):
    return (lambda i, j: (_rt._proj(m, 'novelDirectCausalTemplate')(i, j) * jointNovelDirectCausalKernelAt(m, t, i, j)))

def proxyTaggingTargetAt(m, t):
    return (lambda i, j: (_rt._proj(m, 'proxyTaggingSource')(i, j) * jointProxyTaggingKernelAt(m, t, i, j)))

def novelProxyTaggingTargetAt(m, t):
    return (lambda i, j: (_rt._proj(m, 'novelProxyTaggingTemplate')(i, j) * jointNovelProxyTaggingKernelAt(m, t, i, j)))

def sigmaTagCausalTargetAt(m, t):
    return (directCausalTargetAt(m, t) + ((novelDirectCausalTargetAt(m, t) + ((proxyTaggingTargetAt(m, t) + novelProxyTaggingTargetAt(m, t))))))

def targetSourceEffectProjectionAt(m, t):
    return _rt._proj((sigmaTagCausalTargetAt(m, t)), 'mulVec')(_rt._proj(m, 'betaSource'))

def targetEffectHeterogeneityProjectionAt(m, t):
    return _rt._proj((sigmaTagCausalTargetAt(m, t)), 'mulVec')(((_rt._proj(m, 'targetEffectHeterogeneityAt')(t) + _rt._proj(m, 'novelCausalEffectTargetAt')(t))))

def targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget):
    return presentDayR2(V_A, V_E, fstTarget)

def neutralAFBenchmarkRatio(fstSource, fstTarget):
    return _rt.rdiv(((1.0 - fstTarget)), ((1.0 - fstSource)))

def hetRatioBetweenBranches(NeA, NeB, mu, H_0, t):
    return _rt.rdiv(hetTrajectory(NeB, mu, H_0, t), hetTrajectory(NeA, mu, H_0, t))

def brierFromR2(π, r2):
    return calibratedBrier(_rt.pi, r2)

def targetGaussianAUCFromNeutralAFBenchmark(V_A, V_E, fstTarget):
    return presentDayGaussianAUC(V_A, V_E, fstTarget)

def sourceBrierFromR2(π, r2Source):
    return calibratedBrier(_rt.pi, r2Source)

def targetExactCalibratedBrierRisk(π, V_A, V_E, fstTarget):
    return calibratedBrier(_rt.pi, (targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget)))

def targetBrierFromNeutralAFBenchmark(π, V_A, V_E, fstTarget):
    return targetExactCalibratedBrierRisk(_rt.pi, V_A, V_E, fstTarget)

def neutralAFBenchmarkMetricProfile(π, V_A, V_E, fstTarget):
    return profileFromSignalVariance(_rt.pi, V_E, (presentDayPGSVariance(V_A, fstTarget)))

def equalVarianceGaussianAUCFromSNR(snr):
    return Phi((_rt.rsqrt((_rt.rdiv(snr, 2.0)))))

def equalVarianceGaussianAUCFromExplainedR2(r2):
    return Phi((_rt.rsqrt((_rt.rdiv(r2, ((2.0 * ((1.0 - r2)))))))))

def equalVarianceGaussianAUCChart(r2):
    return (1.0 if (1.0 <= r2) else equalVarianceGaussianAUCFromExplainedR2(r2))

def equalVarianceGaussianAUCFromSourceWeights(m, P):
    return gaussianAUCFromSignalVariance((explainedSignalVarianceFromSourceWeights(m, P)), (residualVarianceFromSourceWeights(m, P)))

def sourceMetricProfileFromSourceWeightsAtTargetPrevalence(m):
    return sourceMetricProfileFromSourceWeightsAtPrevalence(m, _rt._proj(m, 'targetPrevalence'))

def targetMetricProfileAtGeneration(m, t):
    return targetMetricProfileFromSourceWeights((toMetricModelAt(m, t)))

def sourceNormalizedTargetR2AtGeneration(m, sourceBaseline, t):
    return (sourceBaseline * (_rt.rdiv(r2FromSourceWeights((toMetricModelAt(m, t)), 1), r2FromSourceWeights((toMetricModelAt(m, t)), 0))))

def targetExactGaussianAUCFromNeutralAFBenchmark(V_A, V_E, fstTarget):
    return targetGaussianAUCFromNeutralAFBenchmark(V_A, V_E, fstTarget)

def brierRegretPoint(η, q):
    return (brierBernoulliRisk(η, q) - brierBernoulliRisk(η, η))

def brierRegretRatio(η, qSource, qTarget):
    return _rt.rdiv(brierRegretPoint(η, qTarget), brierRegretPoint(η, qSource))

def logLossRegretPoint(η, q):
    return (bernoulliLogLoss(η, q) - bernoulliLogLoss(η, η))

def logLossRegretRatio(η, qSource, qTarget):
    return _rt.rdiv(logLossRegretPoint(η, qTarget), logLossRegretPoint(η, qSource))

def expectedSqMeanPGSDiff_pureSplit(V_A, fstS, fstT):
    return Var_Delta_Mu(V_A, ((fstS + fstT)))

def expectedSqMeanPGSDiff_IMEquilibrium(V_A, M):
    return Var_Delta_Mu(V_A, ((2.0 * twoDemeIMEquilibriumDelta(M))))

def ibdFlowStep(Ne, rate, F):
    return ((F + _rt.rdiv(((1.0 - F)), ((2.0 * Ne)))) - ((2.0 * rate) * F))

def Calibrator_MutationDriftModelAssumptions_fstEquilibrium(m):
    return fstMutationDriftEquilibrium(Calibrator_MutationDriftModelAssumptions_theta(m))

def Calibrator_MutationDriftModelAssumptions_fstTransient(m):
    return (Calibrator_MutationDriftModelAssumptions_fstEquilibrium(m) * ((1.0 - _rt.rexp((_rt.rdiv(((-((1.0 + Calibrator_MutationDriftModelAssumptions_theta(m)))) * _rt._proj(m, 't')), ((2.0 * _rt._proj(m, 'Ne')))))))))

def covarianceRetention(freq_corr, ld_overlap):
    return (freq_corr * ld_overlap)

def freqCorrFromFst(fst):
    return (1.0 - fst)

def ldOverlapFromSharedLD(shared_ld):
    return shared_ld

def covarianceDivergenceFromRetention(fst, shared_ld):
    return (1.0 - covarianceRetention((freqCorrFromFst(fst)), (ldOverlapFromSharedLD(shared_ld))))

def covarianceDivergenceMutationDrift(fst_drift, shared_ld):
    return (fst_drift + (((1.0 - fst_drift)) * ((1.0 - shared_ld))))

def presentDayPGSVarianceMutationDrift(V_A, fst_drift, shared_ld):
    return (((1.0 - covarianceDivergenceMutationDrift(fst_drift, shared_ld))) * V_A)

def presentDayR2MutationDrift(V_A, V_E, fst_drift, shared_ld):
    v = presentDayPGSVarianceMutationDrift(V_A, fst_drift, shared_ld)
    return _rt.rdiv(v, ((v + V_E)))

def neutralAFSharedLDBenchmarkRatio(fstSource, fstTarget, shared_ld_source, shared_ld_target):
    return _rt.rdiv(((((1.0 - fstTarget)) * shared_ld_target)), ((((1.0 - fstSource)) * shared_ld_source)))

def fstMigrationDriftEquilibrium(Ne, m):
    return _rt.rdiv(1.0, ((1.0 + ((4.0 * Ne) * m))))

def ibdRecurrenceStep(Ne, rate, x):
    return (_rt.lpow(((1.0 - rate)), 2.0) * ((_rt.rdiv(1.0, ((2.0 * Ne))) + (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * x))))

def ibdRecurrenceFixedPoint(Ne, rate):
    return _rt.rdiv(_rt.lpow(((1.0 - rate)), 2.0), ((_rt.lpow(((1.0 - rate)), 2.0) + (((2.0 * Ne) * rate) * ((2.0 - rate))))))

def islandFstMultiplicativeStep(Ne, m, F):
    return ibdRecurrenceStep(Ne, m, F)

def fstIslandMultiplicativeEquilibrium(Ne, m):
    return ibdRecurrenceFixedPoint(Ne, m)

def fstMigDriftEq(s):
    return fstMigrationDriftEquilibrium(_rt._proj(s, 'Ne'), _rt._proj(s, 'mig'))

def steppingStoneFst(fst_neighbor, α, d):
    return _rt.rmin(1.0, ((fst_neighbor * ((1.0 + (α * (((d) - 1.0))))))))

def sharedLD_from_equilibrium(Ne, m):
    return (1.0 - fstMigrationDriftEquilibrium(Ne, m))

def sharedLDFromMigration(M):
    return _rt.rdiv(M, ((1.0 + M)))

def signalRetentionMigrationDrift(Ne, m):
    return (((1.0 - fstMigrationDriftEquilibrium(Ne, m))) * sharedLDFromMigration((scaledMigrationRate(Ne, m))))

def retainedSignalVarianceMigrationDrift(V_A, Ne, m):
    return (signalRetentionMigrationDrift(Ne, m) * V_A)

def asymmetricFst(Ne, m_into):
    return _rt.rdiv(1.0, ((1.0 + ((4.0 * Ne) * m_into))))

def effectiveSymmetricMigration(m_1_2, m_2_1):
    return _rt.rdiv(((m_1_2 + m_2_1)), 2.0)

def admixtureLDDecay(r, generations_since):
    return _rt.lpow(((1.0 - r)), generations_since)

def admixtureLDBoost(r, t_since, equilibrium_ld):
    return _rt.rdiv(admixtureLDDecay(r, t_since), equilibrium_ld)

def fstMigDriftNext(Ne, m, Fst):
    return (((((1.0 - (2.0 * m)) - _rt.rdiv(1.0, ((2.0 * Ne))))) * Fst) + _rt.rdiv(1.0, ((2.0 * Ne))))

def fstMigDriftEquil(Ne, m):
    return _rt.rdiv(1.0, ((((4.0 * Ne) * m) + 1.0)))

def neutralAFBenchmarkFromRecurrence(Ne, m):
    return (1.0 - fstMigDriftEquil(Ne, m))

def noncentralityParam(n, beta, p):
    return ((n * _rt.lpow(beta, 2.0)) * (((2.0 * p) * ((1.0 - p)))))

def powerAtThreshold(ncp, z_alpha):
    return Phi(((_rt.rsqrt(ncp) - z_alpha)))

def standardError(m):
    return _rt.rdiv(_rt._proj(m, 'sigma'), _rt.rsqrt(_rt._proj(m, 'n')))

def observedBeta(m, epsilon):
    return (_rt._proj(m, 'true_beta') + epsilon)

def isSelected(m, epsilon, z_alpha):
    return ((z_alpha * standardError(m)) < _rt.rabs((_rt._proj(m, 'true_beta') + epsilon)))

def r2ScalingModel(n, C):
    return _rt.rdiv(n, ((n + C)))

def logRateSampleSize(epsilon):
    return _rt.rexp((_rt.rdiv(1.0, epsilon)))

def gradeCertifiedSampleSize(epsilon, K, c):
    return _rt.lpow(epsilon, ((-(_rt.rdiv(K, c)))))

def pair(s, t, _e):
    _t = [s, t]
    return _t[_rt._ix(_e, 2, 'pair')]

def withTarget(f, t):
    return pair((f(0)), t)

def klBern(p, q):
    return bernoulliKL((unitProbToNNReal(p)), (unitProbToNNReal(q)), (unitProbToNNReal_le_one(p)), (unitProbToNNReal_le_one(q)))

def poly_n(n, x):
    return _rt.lpow(x, n)

def altAlleleCount(_e):
    _t = [0.0, 1.0, 2.0]
    return _t[_rt._ix(_e, 3, 'altAlleleCount')]

def refFreq(h):
    return (1.0 - _rt._proj(h, 'altFreq'))

def genotypeProb(h, _e):
    _t = [_rt.lpow(_rt._proj(h, 'refFreq'), 2.0), ((2.0 * _rt._proj(h, 'refFreq')) * _rt._proj(h, 'altFreq')), _rt.lpow(_rt._proj(h, 'altFreq'), 2.0)]
    return _t[_rt._ix(_e, 3, 'genotypeProb')]

def expectedAltAlleleCount(h):
    return sum(((altAlleleCount(g) * genotypeProb(h, g))) for g in range(int(3)))

def centeredAltAlleleCount(h, g):
    return (altAlleleCount(g) - expectedAltAlleleCount(h))

def genotypeVariance(h):
    return sum(((genotypeProb(h, g) * _rt.lpow((centeredAltAlleleCount(h, g)), 2.0))) for g in range(int(3)))

def genotypeThirdAbsMoment(h):
    return sum(((genotypeProb(h, g) * _rt.lpow(_rt.rabs(centeredAltAlleleCount(h, g)), 3.0))) for g in range(int(3)))

def Calibrator_HWEScoreModel_scoreMean(model):
    return sum(((_rt._proj(model, 'effect')(i) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'expectedAltAlleleCount'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def Calibrator_HWEScoreModel_scoreVariance(model):
    return sum(((_rt.lpow((_rt._proj(model, 'effect')(i)), 2.0) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'genotypeVariance'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def scoreThirdAbsMomentBound(model):
    return sum(((_rt.lpow(_rt.rabs(_rt._proj(model, 'effect')(i)), 3.0) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'genotypeThirdAbsMoment'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def Calibrator_berryEsseenErrorBound(berryEsseenConstant, variance, thirdMomentSum):
    return _rt.rdiv((berryEsseenConstant * thirdMomentSum), ((variance * _rt.rsqrt(variance))))

def Calibrator_HWEScoreModel_berryEsseenErrorBound(model, berryEsseenConstant):
    return Calibrator_berryEsseenErrorBound(berryEsseenConstant, Calibrator_HWEScoreModel_scoreVariance(model), scoreThirdAbsMomentBound(model))

def aucApproximationInterval(aucGaussian, epsilon):
    return approximationInterval(aucGaussian, epsilon)

def r2ApproximationInterval(r2Gaussian, epsilon):
    return approximationInterval(r2Gaussian, epsilon)

def Phi(x):
    return _rt.Phi(x)

def latentLiability(s, e):
    return (s + e)

def etaLiabilityThreshold(hN, T, s, x):
    return _rt._proj((noiseMeasureGivenX(hN, x, (diseaseEvent(T, x, s)))), 'toReal')

def chiSquareBudget(P, densityRatio):
    return P(((lambda ω: _rt.lpow((_rt.sub(densityRatio[int(ω)], 1.0)), 2.0))))

def weightedResidualMoment(P, densityRatio, X, residual):
    return rawCrossMoment(P, X, ((lambda ω: _rt.mul((_rt.sub(densityRatio[int(ω)], 1.0)), residual[int(ω)]))))

def coefficientEnergy(B, x):
    return dot(x, (_rt.mulVec(B, x)))

def detectionWeight(s):
    return _rt.rinv(s)

def reconstructionWeight(s):
    return s

def wienerWeight(noise, s):
    return _rt.rdiv(s, ((s + noise)))

def spectralCapture(w, M):
    return sum((_rt.mul(M[int(i)], w[int(i)])) for i in range(int(len(w))))

def spectralTotal(w):
    return sum((w[int(i)]) for i in range(int(len(w))))

def reconstructionEfficiency(spectrum, M):
    return _rt.rdiv(spectralCapture(((lambda i: reconstructionWeight((spectrum[int(i)])))), M), spectralTotal(((lambda i: reconstructionWeight((spectrum[int(i)]))))))

def detectionEfficiency(spectrum, M):
    return _rt.rdiv(spectralCapture(((lambda i: detectionWeight((spectrum[int(i)])))), M), spectralTotal(((lambda i: detectionWeight((spectrum[int(i)]))))))

def sharedCorrectionOptimum(B, beta, theta):
    return _rt.rdiv(dot(beta, (_rt.mulVec(B, theta))), coefficientEnergy(B, beta))

def irreducibleDegradation(B, beta, theta):
    return _rt.sub(coefficientEnergy(B, theta), _rt.rdiv(_rt.lpow(dot(beta, (_rt.mulVec(B, theta))), 2.0), coefficientEnergy(B, beta)))

def quadraticRisk(outcomeSecondMoment, B, b, w):
    return _rt.add(_rt.sub(outcomeSecondMoment, _rt.mul(2.0, dot(w, b))), dot(w, (_rt.mulVec(B, w))))

def quadraticCoefficientDistance(B, w, v):
    return dot(((lambda i: _rt.sub(w[int(i)], v[int(i)]))), (_rt.mulVec(B, ((lambda i: _rt.sub(w[int(i)], v[int(i)]))))))

def bestScalarCorrection(B, u, v):
    return _rt.rdiv(dot(u, (_rt.mulVec(B, v))), dot(u, (_rt.mulVec(B, u))))

def scalarCorrectionFloor(B, u, v):
    return _rt.sub(dot(v, (_rt.mulVec(B, v))), _rt.rdiv(_rt.lpow(dot(u, (_rt.mulVec(B, v))), 2.0), dot(u, (_rt.mulVec(B, u)))))

def mutationSelectionStepRare(mu, s, h, p):
    return ((p * ((1.0 - (h * s)))) + (mu * ((1.0 - p))))

def mutationSelectionBalance(mu, s, h):
    return _rt.rdiv(mu, (((h * s) + mu)))

def mutationSelectionStepRecessive(mu, s, p):
    return ((p - (s * _rt.lpow(p, 2.0))) + (mu * ((1.0 - p))))

def mutationSelectionBalanceRecessive(mu, s):
    return _rt.rdiv(((_rt.rsqrt(((mu * ((mu + (4.0 * s)))))) - mu)), ((2.0 * s)))

def expectedEffectMultiplier(p, α):
    return _rt.lpow(((p * ((1.0 - p)))), ((1.0 + α)))

def markovPoissonKernel(lam, x):
    return _rt.rdiv(((1.0 - _rt.lpow(lam, 2.0))), (((1.0 + _rt.lpow(lam, 2.0)) - ((2.0 * lam) * x))))

def twoStatePersistence(a, b):
    return ((1.0 - a) - b)

def overlapInflation(r2_true, r2_observed):
    return (_rt.rdiv(r2_observed, r2_true) - 1.0)

def partialOverlapR2(r2_true, h2, f, _n_gwas):
    return ((((1.0 - f)) * r2_true) + (f * h2))

def approxLOOPGS(pgs_full, leverage, residual):
    return (pgs_full - (leverage * residual))

def kinshipInflation(r2_true, K, h2_family):
    return (r2_true + (K * h2_family))

def pgsMean(β, p):
    return sum((_rt.mul(β[int(i)], (_rt.mul(2.0, p[int(i)])))) for i in range(int(len(β))))

def pgsVariance(β, p):
    return sum((_rt.mul(_rt.lpow(β[int(i)], 2.0), (_rt.mul(_rt.mul(2.0, p[int(i)]), (_rt.sub(1.0, p[int(i)])))))) for i in range(int(len(β))))

def pgsMeanShift(β, p_source, p_target):
    return sum((_rt.mul(β[int(i)], (_rt.mul(2.0, (_rt.sub(p_target[int(i)], p_source[int(i)])))))) for i in range(int(len(β))))

def thresholdStandardizedCoordinate(threshold, μ, σ):
    return _rt.rdiv(((threshold - μ)), σ)

def benchmarkHighScoreRate(threshold, μ, σ):
    return (1.0 - Phi((thresholdStandardizedCoordinate(threshold, μ, σ))))

def externallyStandardized(pgs, μ_source, σ_source):
    return _rt.rdiv(((pgs - μ_source)), σ_source)

def internallyStandardized(pgs, μ_target, σ_target):
    return _rt.rdiv(((pgs - μ_target)), σ_target)

def rawCrossMoment(E, X, Y):
    return (lambda i: E(((lambda ω: _rt.mul(X[int(ω)][int(i)], Y[int(ω)])))))

def equilibriumEffectVariance(v_mutation, s):
    return _rt.rdiv(v_mutation, s)

def effectVarianceRecurrence(V, v_mut, s):
    return ((((1.0 - s)) * V) + v_mut)

def effectCorrelationStabilizing(Ns):
    return (1.0 - _rt.rdiv(1.0, ((2.0 * Ns))))

def fluctuatingEffectCorrelation(t, τ):
    return _rt.rexp((_rt.rdiv((-t), τ)))

def stabilizingSelectedArchitectureVariance(v_mutation, s):
    return equilibriumEffectVariance(v_mutation, s)

def optimumOUVariance(sigmaTheta, tau):
    return _rt.rdiv((_rt.lpow(sigmaTheta, 2.0) * tau), 2.0)

def fluctuatingSelectedArchitectureVariance(v_mutation, s, sigmaTheta, tau):
    return (equilibriumEffectVariance(v_mutation, s) + optimumOUVariance(sigmaTheta, tau))

def stabilizingNsFromObservedCorrelation(rho):
    return _rt.rdiv(1.0, ((2.0 * ((1.0 - rho)))))

def tauFromObservedEffectCorrelation(t, rho):
    return _rt.rdiv((-t), _rt.rlog(rho))

def sigmaThetaFromObservedSelectedVariance(v_selected, v_mutation, s, t, rho):
    return _rt.rsqrt((_rt.rdiv((2.0 * ((v_selected - stabilizingSelectedArchitectureVariance(v_mutation, s)))), tauFromObservedEffectCorrelation(t, rho))))

def polygenicAdaptationShift(β, Δp):
    return sum((_rt.mul(β[int(i)], Δp[int(i)])) for i in range(int(len(β))))

def gwasNCP(n, β, p):
    return ((n * _rt.lpow(β, 2.0)) * (((2.0 * p) * ((1.0 - p)))))

def selectionSummaryLogLik(validation, summary):
    return (gaussianProfileLogLik(_rt._proj(validation, 'observedEffectCorrelation'), _rt._proj(summary, 'predictedEffectCorrelation'), _rt._proj(validation, 'effectCorrelationNoise')) + gaussianProfileLogLik(_rt._proj(validation, 'observedSelectedVariance'), _rt._proj(summary, 'predictedSelectedVariance'), _rt._proj(validation, 'selectedVarianceNoise')))

def missedSelectedVariance(validation, summary):
    return _rt.rabs((_rt._proj(validation, 'observedSelectedVariance') - _rt._proj(summary, 'predictedSelectedVariance')))

def selectionModelLRT(validation, nullSummary, altSummary):
    return likelihoodRatioStat((selectionSummaryLogLik(validation, nullSummary)), (selectionSummaryLogLik(validation, altSummary)))

def mechanisticPortabilityRatio(m):
    return _rt.rdiv(r2FromSourceWeights(m, 1), r2FromSourceWeights(m, 0))

def sourceSquaredEffectMass(β):
    return sum((_rt.lpow(β[int(i)], 2.0)) for i in range(int(len(β))))

def popgenDrivenTagScale():
    return ((_rt.rdiv(7.0, 6.0)) * _rt.rexp(((-(1.0)))))

def popgenDrivenProxyScale():
    return ((_rt.rdiv(7.0, 6.0)) * _rt.rexp(((-(_rt.rdiv(15.0, 14.0))))))

def optimalReadout(P, b):
    return _rt.rdiv(_rt._proj(P, 'crossSpectrum')(b), _rt._proj(P, 'featureSpectrum')(b))

def risk(P, readout):
    return sum(((_rt.add(_rt.sub(_rt.mul(_rt._proj(P, 'featureSpectrum')(b), _rt.lpow(readout[int(b)], 2.0)), _rt.mul(_rt.mul(2.0, _rt._proj(P, 'crossSpectrum')(b)), readout[int(b)])), _rt._proj(P, 'targetPower')(b)))) for b in range(int(len(readout))))

def degradation(source, target):
    return (risk(target, (optimalReadout(source))) - risk(target, (optimalReadout(target))))

def degradationProfile(source, target, b):
    return (_rt.lpow(((optimalReadout(source, b) - optimalReadout(target, b))), 2.0) * _rt._proj(target, 'featureSpectrum')(b))

def incrementalR2(r2_full, r2_covariates):
    return (r2_full - r2_covariates)

def portabilityRatio(dr2_target, dr2_source):
    return _rt.rdiv(dr2_target, dr2_source)

def effectiveSampleSizeSE(se):
    return _rt.rdiv(1.0, _rt.lpow(se, 2.0))

def fixed_weights(m, i):
    return _rt.rdiv(1.0, _rt._proj(m, 'variances')(i))

def random_weights(m, i):
    return _rt.rdiv(1.0, ((_rt._proj(m, 'variances')(i) + _rt._proj(m, 'tau_sq'))))

def geneticCorrelationLDSC(model):
    return _rt.rdiv((sum(((_rt._proj(model, 'beta_s')(i) * _rt._proj(model, 'beta_t')(i))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'beta_s')), len(_rt._proj(model, 'beta_t'))))))), _rt.rsqrt((((sum((_rt.lpow(_rt._proj(model, 'beta_s')(i), 2.0)) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'beta_s'))))))) * (sum((_rt.lpow(_rt._proj(model, 'beta_t')(i), 2.0)) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'beta_t')))))))))))

def disjointWindowLimitVariance(share):
    return sum((share[int(j)]) for j in range(int(len(share))))

def varBias(m):
    return sum(((_rt.lpow(_rt._proj(m, 'b')(i), 2.0) * _rt._proj(m, 'H')(i))) for i in range(int(_rt.sumdim('i', len(_rt._proj(m, 'b')), len(_rt._proj(m, 'H'))))))

def varBiasTarget(m):
    return (_rt._proj(m, 'attenuation') * _rt._proj(_rt._proj(m, 'toStratificationModel'), 'varBias'))

def pSurv(m):
    return _rt.rdiv((_rt._proj(m, 'p₀') * _rt._proj(m, 's')), (((_rt._proj(m, 'p₀') * _rt._proj(m, 's')) + ((1.0 - _rt._proj(m, 'p₀'))))))

def r2_surv(m):
    return (_rt._proj(m, 'r2_full') * (_rt.rdiv(_rt._proj(m, 'var_surv'), _rt._proj(m, 'var_birth'))))

def pgsAttenuationFactor(r2_gwas):
    return _rt.rsqrt(r2_gwas)

def reliabilityRatio(r2, σ2_noise):
    return _rt.rdiv(r2, ((r2 + σ2_noise)))

def r2EstimatorVariance(r2, n):
    return _rt.rdiv(((4.0 * r2) * _rt.lpow(((1.0 - r2)), 2.0)), n)

def pgsPhenoCov(β_weights, β_causal, ld):
    m = float(len(β_weights))
    return sum((sum((_rt.mul(_rt.mul(β_weights[int(i)], ld[int(i)][int(j)]), β_causal[int(j)])) for j in range(int(len(β_weights))))) for i in range(int(len(β_weights))))

def sharedLDGeneticVariance(β, ld):
    return pgsPhenoCov(β, β, ld)

def sharedLDHeritability(β, ld, var_y):
    return _rt.rdiv(sharedLDGeneticVariance(β, ld), var_y)

def pgsR2(cov_pgs_y, var_pgs, var_y):
    return _rt.rdiv(_rt.lpow(cov_pgs_y, 2.0), ((var_pgs * var_y)))

def sourceTruthR2SharedLD(β_source, ld, var_y):
    return pgsR2((sharedLDGeneticVariance(β_source, ld)), (sharedLDGeneticVariance(β_source, ld)), var_y)

def transportedTargetR2SharedLD(β_source, β_target, ld, var_y):
    return pgsR2((pgsPhenoCov(β_source, β_target, ld)), (sharedLDGeneticVariance(β_source, ld)), var_y)

def ldEffectGeneticCorrelation(β_source, β_target, ld):
    return _rt.rdiv(pgsPhenoCov(β_source, β_target, ld), _rt.rsqrt((_rt.mul(sharedLDGeneticVariance(β_source, ld), sharedLDGeneticVariance(β_target, ld)))))

def effectGeneticCorrelation(β_source, β_target):
    m = float(len(β_source))
    return _rt.rdiv((sum((_rt.mul(β_source[int(i)], β_target[int(i)])) for i in range(int(len(β_source))))), _rt.rsqrt((_rt.mul((sum((_rt.lpow(β_source[int(i)], 2.0)) for i in range(int(len(β_source))))), (sum((_rt.lpow(β_target[int(i)], 2.0)) for i in range(int(len(β_source)))))))))

def standardizedDiagonalLD():
    return (lambda i, j: (1.0 if (i == j) else 0.0))

def additiveGeneticVariance(β):
    m = float(len(β))
    return sum((_rt.lpow(β[int(i)], 2.0)) for i in range(int(len(β))))

def additiveHeritability(β, var_y):
    return _rt.rdiv(additiveGeneticVariance(β), var_y)

def sourceSelfR2DiagonalLD(β_source, var_y):
    return sourceTruthR2SharedLD(β_source, standardizedDiagonalLD, var_y)

def transportedTargetR2DiagonalLD(β_source, β_target, var_y):
    return transportedTargetR2SharedLD(β_source, β_target, standardizedDiagonalLD, var_y)

def benDavidUpperBound(err_source, divergence, lambda_star):
    return ((err_source + divergence) + lambda_star)

def importanceWeightESS(sum_w, sum_w_sq):
    return _rt.rdiv(_rt.lpow(sum_w, 2.0), sum_w_sq)

def AsymptoticallyConsistent(est, truth):
    return AsymptoticallyZero(((lambda n: (est(n) - truth))))

def pcaSignalLossPenalty(signalBaseline, signalRetained, lossWeight):
    return (lossWeight * ((signalBaseline - signalRetained)))

def pcaBiasReduction(ancestryBiasWith, ancestryBiasWithout):
    return (ancestryBiasWith - ancestryBiasWithout)

def pcaNetTargetError(ancestryBias, signalBaseline, signalRetained, lossWeight):
    return (ancestryBias + pcaSignalLossPenalty(signalBaseline, signalRetained, lossWeight))

def infoBottleneckObjective(I_phi_Y, I_phi_A, lam):
    return (I_phi_Y - (lam * I_phi_A))

def gaussianSourceResidualRisk(I_phi_Y):
    return _rt.rexp((((-2.0) * I_phi_Y)))

def pinskerAncestryDivergenceCap(I_phi_A):
    return _rt.rsqrt(((2.0 * I_phi_A)))

def infoCertifiedBenDavidUpperBound(I_phi_Y, I_phi_A, lambda_star):
    return ((gaussianSourceResidualRisk(I_phi_Y) + pinskerAncestryDivergenceCap(I_phi_A)) + lambda_star)

def fineTunedTargetR2(r2_source, divergence_penalty, adaptation_gain):
    return ((r2_source - divergence_penalty) + adaptation_gain)

def scratchTargetR2(oracle_target_r2, estimation_penalty):
    return (oracle_target_r2 - estimation_penalty)

def deployedTransferTargetR2(transported_r2, adaptation_gain, estimation_penalty):
    return ((transported_r2 + adaptation_gain) - estimation_penalty)

def oracleTransportAdaptationGain(transported_r2, oracle_target_r2):
    return (oracle_target_r2 - transported_r2)

def transportPenalty(source_r2, transported_r2):
    return (source_r2 - transported_r2)

def targetOracleR2DiagonalLD(β_target, var_y):
    return sourceSelfR2DiagonalLD(β_target, var_y)

def sampleLimitedScratchTargetR2(oracle_target_r2, noiseVar, nTarget):
    return scratchTargetR2(oracle_target_r2, (_rt.rdiv(noiseVar, nTarget)))

def usableScratchTargetR2(oracle_target_r2, noiseVar, nTarget):
    return _rt.rmax(0.0, (sampleLimitedScratchTargetR2(oracle_target_r2, noiseVar, nTarget)))

def scratchVsFineTuningCriticalSampleSize(r2_source, divergence_penalty, adaptation_gain, oracle_target_r2, noiseVar):
    return _rt.rdiv(noiseVar, ((oracle_target_r2 - fineTunedTargetR2(r2_source, divergence_penalty, adaptation_gain))))

def sourceShrinkageMSE(gapSq, noiseVar, nTarget, lam):
    return ((gapSq * _rt.lpow(lam, 2.0)) + ((_rt.rdiv(noiseVar, nTarget)) * _rt.lpow(((1.0 - lam)), 2.0)))

def optimalSourceShrinkageWeight(gapSq, noiseVar, nTarget):
    return _rt.rdiv((_rt.rdiv(noiseVar, nTarget)), ((gapSq + _rt.rdiv(noiseVar, nTarget))))

def coefficientGapSq(wSource, wTarget):
    return _rt.dotProduct(((lambda i: _rt.sub(wSource[int(i)], wTarget[int(i)]))), ((lambda i: _rt.sub(wSource[int(i)], wTarget[int(i)]))))

def meanPopulationDeviation(deviation, k):
    return (lambda i: (_rt.rinv((k)) * populationDeviationSum(deviation, k, i)))

def metaLearnedSourceWeights(wShared, deviation, k):
    return (lambda i: _rt.add(wShared[int(i)], meanPopulationDeviation(deviation, k, i)))

def centeredPopulationEffectDeviation(wShared, wSource):
    return (lambda j, i: _rt.sub(wSource[int(j)][int(i)], wShared[int(i)]))

def metaLearnedTransferGapSq(wShared, wTarget, deviation, k):
    return coefficientGapSq((metaLearnedSourceWeights(wShared, deviation, k)), wTarget)

def weightedPopulationDeviation(deviation, weight):
    k = float(len(deviation))
    return (lambda i: sum((_rt.mul(weight[int(j)], deviation[int(j)][int(i)])) for j in range(int(len(deviation)))))

def weightedMetaSourceWeights(wShared, deviation, weight):
    return (lambda i: _rt.add(wShared[int(i)], weightedPopulationDeviation(deviation, weight, i)))

def weightedMetaTransferGapSq(wShared, wTarget, deviation, weight):
    return coefficientGapSq((weightedMetaSourceWeights(wShared, deviation, weight)), wTarget)

def uniformMetaWeight(k):
    return (lambda _: _rt.rinv((k)))

def weightedPopulationEffectAverage(wSource, weight):
    k = float(len(wSource))
    return (lambda i: sum((_rt.mul(weight[int(j)], wSource[int(j)][int(i)])) for j in range(int(len(wSource)))))

def optimalFineTuningMSE(gapSq, noiseVar, nTarget):
    return sourceShrinkageMSE(gapSq, noiseVar, nTarget, (optimalSourceShrinkageWeight(gapSq, noiseVar, nTarget)))

def requiredTargetSamplesForOptimalFineTuningMSE(gapSq, noiseVar, tau):
    return _rt.rdiv((noiseVar * ((gapSq - tau))), ((tau * gapSq)))

def targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, w, wStar):
    return _rt.sub(targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, w), targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, wStar))

def exactAdaptationGain(sigmaObsTarget, crossTarget, noiseVar, wBefore, wAfter, wStar):
    return _rt.sub(targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, wBefore, wStar), targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, wAfter, wStar))

def privateArchitectureTransferCeiling(h2_target, f_private, M):
    return ((h2_target * ((1.0 - f_private))) * sharedLDFromMigration(M))

def mean(E, Z):
    return E(Z)

def variance(E, Z):
    return E(((lambda ω: _rt.lpow((_rt.sub(Z[int(ω)], E(Z))), 2.0))))

def covariance(E, X, Y):
    return E(((lambda ω: _rt.mul((_rt.sub(X[int(ω)], E(X))), (_rt.sub(Y[int(ω)], E(Y)))))))

def expMse(E, Y, S):
    return E(((lambda ω: _rt.lpow((_rt.sub(Y[int(ω)], S[int(ω)])), 2.0))))

def bias(E, Y, S):
    return _rt.sub(E(S), E(Y))

def dot(x, y):
    return sum((_rt.mul(x[int(i)], y[int(i)])) for i in range(int(len(x))))

def crossCovVector(E, X, Y):
    return (lambda i: covariance(E, ((lambda ω: X[int(ω)][int(i)])), Y))

def contextCrossCovVector(E, X, h):
    return (lambda j: covariance(E, ((lambda ω: X[int(ω)][int(j)])), h))

def optimalWeightsFromMoments(sigmaInv, E, X, Y):
    return _rt.mulVec(sigmaInv, (crossCovVector(E, X, Y)))

def transportedCovariance(w, K, β):
    return sum((sum((_rt.mul(_rt.mul(w[int(j)], K[int(j)][int(l)]), β[int(l)])) for l in range(int(_rt.sumdim('l', len(K[0]), len(β)))))) for j in range(int(_rt.sumdim('j', len(w), len(K)))))

def locusTerm(w, K, β, l):
    return _rt.mul((sum((_rt.mul(w[int(j)], K[int(j)][int(l)])) for j in range(int(_rt.sumdim('j', len(w), len(K)))))), β[int(l)])

def baselineWeight(aT, l):
    return _rt.rdiv(aT[int(l)], (sum((aT[int(m)]) for m in range(int(len(aT))))))

def transportFactor(aQ, aT, l):
    return _rt.rdiv(aQ[int(l)], aT[int(l)])

def explainableFraction(between, total):
    return _rt.rdiv(between, total)

def prevalence(c):
    return (_rt._proj(c, 'tp') + _rt._proj(c, 'fn'))

def recallRate(c):
    return _rt.rdiv(_rt._proj(c, 'tp'), ((_rt._proj(c, 'tp') + _rt._proj(c, 'fn'))))

def fpr(c):
    return _rt.rdiv(_rt._proj(c, 'fp'), ((_rt._proj(c, 'fp') + _rt._proj(c, 'tn'))))

def precision(c):
    return _rt.rdiv(_rt._proj(c, 'tp'), ((_rt._proj(c, 'tp') + _rt._proj(c, 'fp'))))

def transportedRidgeParameter(τ, a, r):
    return _rt.rdiv((_rt.lpow(τ, 2.0) * a), ((a + r)))

def robustRidgeCandidate(S, τ, a, r):
    return _rt.rdiv((((a + r)) * _rt.lpow(S, 2.0)), (((((a + r)) * _rt.lpow(S, 2.0)) + (_rt.lpow(τ, 2.0) * a))))

def gaussianProfileLogLik(observed, mean, variance):
    return (_rt.rdiv((-(_rt.lpow(((observed - mean)), 2.0))), ((2.0 * variance))) - _rt.rdiv(_rt.rlog((((2.0 * _rt.pi) * variance))), 2.0))

def likelihoodRatioStat(logLNull, logLAlt):
    return ((-2.0) * ((logLNull - logLAlt)))

def narrowSenseH2(V_A, V_D, V_I, V_E):
    return _rt.rdiv(V_A, ((((V_A + V_D) + V_I) + V_E)))

def snpH2(V_A_tagged, V_P):
    return _rt.rdiv(V_A_tagged, V_P)

def additiveVariance(p, α):
    return sum((_rt.mul(_rt.mul(_rt.mul(2.0, p[int(i)]), (_rt.sub(1.0, p[int(i)]))), _rt.lpow((α[int(i)]), 2.0))) for i in range(int(len(p))))

def liabilityScaleH2(h2_observed, prevalence, z_height):
    return _rt.rdiv(((h2_observed * prevalence) * ((1.0 - prevalence))), _rt.lpow(z_height, 2.0))

def rightWhiten(inverseColor, data):
    return rightTransform(inverseColor, data)

def rightColor(color, data):
    return rightTransform(color, data)

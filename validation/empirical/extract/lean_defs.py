"""GENERATED FILE -- do not edit.  NOT AUTHORITATIVE IF COMMITTED.

    THE COPY OF THIS FILE IN GIT IS STALE BY CONSTRUCTION.

`Descent/` changes every few minutes.  A generated table committed
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
Descent/.  Each function below was translated from the parsed body of
the corresponding Lean `def`; no formula in this file was typed by hand.

Regenerate with:  python3 validation/extract/emit.py
"""
# ruff: noqa
import lean_rt as _rt

def averageEffect(m):
    return (_rt._proj(m, 'a') + (_rt._proj(m, 'd') * ((1.0 - (2.0 * _rt._proj(m, 'p'))))))

def genotypicValue(*_a):
    if len(_a) < 2:
        return lambda *_b: genotypicValue(*(_a + _b))
    m, _e = _a[:2]
    _t = [(-_rt._proj(m, 'a')), _rt._proj(m, 'd'), _rt._proj(m, 'a')]
    return _t[_rt._ix(_e, 3, 'genotypicValue')]

def pairwiseCoalescentSurvival(lam, t):
    return _rt.rexp(((-((lam * t)))))

def sampleCost(η, C, k):
    return _rt.lpow((_rt.rdiv(C, η)), ((2.0 * k)))

def weightRatio(P, Q, w):
    return _rt.rdiv(prodWeight(Q, w), prodWeight(P, w))

def defect(P, Q, w, u):
    return _rt.rdiv(weightRatio(P, Q, w), weightRatio(P, Q, u))

def chi(P, Q, w):
    return _rt.rdiv(prodWeight(P, w), prodWeight(Q, w))

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

def Descent_Blindness_BundleFamily_modulus(family, j, t):
    return _rt.rabs((_rt.lpow(_rt._proj(family, 'atomValue')(j, t), 2.0) - 1.0))

def massAt(family, t, v):
    return sum(((_rt._proj(family, 'atomMass')(j, t) if (Descent_Blindness_BundleFamily_modulus(family, j, t) == v) else 0.0)) for j in range(int(_rt.sumdim('j', len(_rt._proj(family, 'atomMass'))))))

def gaussianJetVariance():
    return (_rt.rdiv(_rt.lpow(_rt.pi, 2.0), 2.0) - 4.0)

def criticalDegree(N, c):
    return _rt.rdiv(_rt.rlog(N), c)

def gaussianCriticalMultiplier():
    return _rt.rdiv(1.0, condensationConstant())

def windowVariance(w, v):
    return Phi((_rt.rdiv(w, _rt.rsqrt(v))))

def ghostGain(α, n):
    return (α * _rt.rlog(n))

def countPredictedGain(α, n):
    return _rt.lpow(n, α)

def ghostWitnessExample(u):
    return ghostWitness(1.0, 1.0, u, ghostGain_ne_countPredicted_at_one)

def momentInvariant(m, lam):
    return (lambda p: normalizedMoment(m, lam, p))

def charFnSq(w, a, t):
    return sum((sum((_rt.mul(_rt.mul(w[int(u)], w[int(v)]), _rt.cos((_rt.mul(t, (_rt.sub(a[int(u)], a[int(v)]))))))) for v in range(int(len(w))))) for u in range(int(len(w))))

def locusVarianceShare(β, h, j):
    return _rt.mul(_rt.lpow(β[int(j)], 2.0), h[int(j)])

def Descent_Blindness_scoreVariance(β, h):
    return sum((locusVarianceShare(β, h, j)) for j in range(int(len(β))))

def Descent_Blindness_locusInfluence(β, h, j):
    return _rt.rdiv(locusVarianceShare(β, h, j), Descent_Blindness_scoreVariance(β, h))

def IsProfileTwin(divergence, s, t):
    return all(((divergence[int(s)][int(u)] == divergence[int(t)][int(u)])) for u in range(int(len(divergence))))

def alleleFrequencyDivergence(frequency, s, t):
    return hudsonFst((frequency[int(s)]), (frequency[int(t)]))

def alignmentEnergy(weight, divergence, field):
    return sum((sum((_rt.mul(_rt.mul(_rt.mul(weight[int(s)], weight[int(t)]), divergence[int(s)][int(t)]), _rt.lpow((_rt.sub(field[int(s)], field[int(t)])), 2.0))) for t in range(int(len(weight))))) for s in range(int(len(weight))))

def witnessWeight(_p):
    return _rt.rdiv(1.0, 3.0)

def rareWeight(rare, p):
    return (rare if p else (1.0 - rare))

def rareField():
    return binarySecondAnnotation

def clippedModeError(rootSource, rootGain, budget):
    return (rootSource * _rt.rmax(0.0, ((1.0 - (budget * rootGain)))))

def fourthCumulantFromMoments(secondMoment, fourthMoment):
    return (fourthMoment - (3.0 * _rt.lpow(secondMoment, 2.0)))

def circulantSpectrumA(c):
    return (((8.0 * _rt.lpow(c, 2.0)) + (2.0 * c)) - 4.0)

def circulantSpectrumB(c):
    return (((4.0 * _rt.lpow(c, 2.0)) + (4.0 * c)) - 2.0)

def palindromicCycleDensityA(s, p):
    return ((((_rt.lpow(circulantSpectrumA(1.0), p) + (2.0 * _rt.lpow(circulantSpectrumA((_rt.rdiv(s, 2.0))), p))) + (2.0 * _rt.lpow(circulantSpectrumA(0.0), p))) + (2.0 * _rt.lpow(circulantSpectrumA(((-(_rt.rdiv(s, 2.0))))), p))) + _rt.lpow(circulantSpectrumA(((-1.0))), p))

def palindromicCycleDensityB(s, p):
    return ((((_rt.lpow(circulantSpectrumB(1.0), p) + (2.0 * _rt.lpow(circulantSpectrumB((_rt.rdiv(s, 2.0))), p))) + (2.0 * _rt.lpow(circulantSpectrumB(0.0), p))) + (2.0 * _rt.lpow(circulantSpectrumB(((-(_rt.rdiv(s, 2.0))))), p))) + _rt.lpow(circulantSpectrumB(((-1.0))), p))

def codedDecayProfile(B, x):
    return (lambda n: _rt.rexp((((-(B(n))) - x(n)))))

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
    return halfDiffSq(a, b)

def gramForm(A, x, y):
    return sum((sum((_rt.mul(_rt.mul(x[int(i)], A[int(i)][int(j)]), y[int(j)])) for j in range(int(len(A))))) for i in range(int(len(A))))

def quadForm(A, x):
    return gramForm(A, x, x)

def stationaryLDEntry(decay, separation):
    return power(decay, separation)

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

def latticeInflation(h):
    return _rt.rdiv(h, ((1.0 - _rt.rexp(((-h))))))

def latticeBracket(h, δ):
    return _rt.rdiv((h * _rt.rexp(((-δ)))), ((1.0 - _rt.rexp(((-h))))))

def oneHotWeight(selected, k):
    return (1.0 if (k == selected) else 0.0)

def migratingForbiddenBand(mix):
    return translatedForbiddenBand(0.0, 2.0, 1.0, mix)

def mixedSphericalCovariance(alpha, beta, q):
    return ((_rt.lpow(q, 2.0) + (alpha * _rt.lpow(q, 4.0))) + (beta * _rt.lpow(q, 6.0)))

def sphericalGaplessnessCertificate(alpha, beta, q):
    return (((2.0 * (((2.0 + ((12.0 * alpha) * _rt.lpow(q, 2.0))) + ((30.0 * beta) * _rt.lpow(q, 4.0))))) * (((24.0 * alpha) + ((360.0 * beta) * _rt.lpow(q, 2.0))))) - (3.0 * _rt.lpow(((((24.0 * alpha) * q) + ((120.0 * beta) * _rt.lpow(q, 3.0)))), 2.0)))

def goldenCorrelationThreshold():
    return _rt.rdiv(((_rt.rsqrt(5.0) - 1.0)), 2.0)

def populationOverlapProfile(q, x):
    return overlapProfile(q, x)

def populationGapCertificate(correlation):
    return ((1.0 - (3.0 * _rt.lpow(correlation, 2.0))) + _rt.lpow(correlation, 4.0))

def pooledEnvironmentCorrelation(left, right, leftMass):
    return convexCombination(leftMass, left, right)

def mixedEnvironmentCorrelation(rho, mix):
    return (rho * (((2.0 * mix) - 1.0)))

def criticalMinorityProportion(rho):
    return _rt.rdiv(((1.0 - _rt.rdiv(goldenCorrelationThreshold(), rho))), 2.0)

def configurationOverlap(left, right):
    return _rt.dotProduct(left, right)

def covarianceDisplacementEnergy(sigma, candidate, truth):
    return _rt.dotProduct((_rt.sub(candidate, truth)), (_rt.mulVec(sigma, (_rt.sub(candidate, truth)))))

def overlapEnergyWitnessCovariance():
    return symmetricTwoCoordinateCovariance(2.0, 2.0, 1.0)

def demeRate(a, b, i, j):
    return (0.0 if (i == j) else (a if ((i == 0.0) or (j == 0.0)) else b))

def generatorApply(q, f, i):
    return sum((_rt.mul(q[int(i)][int(j)], (_rt.sub(f[int(j)], f[int(i)])))) for j in range(int(len(q))))

def Lumped(f):
    return (f[int(1.0)] == f[int(2.0)])

def generatorIter(q, f, n):
    _prev = f
    for _ in range(int(n)):
        _prev = generatorApply(q, (_prev))
    return _prev

def speedTiltWeight(theta, mark):
    return _rt.rexp(((-((theta * frontDisplacement(mark))))))

def logDisplacement(gamma, x):
    return ((-(_rt.rdiv(1.0, gamma))) * _rt.rlog(((1.0 - x))))

def linearDisplacementTripleRate(theta):
    return _rt.rdiv(((1.0 - (((1.0 + theta)) * _rt.rexp(((-theta)))))), ((theta * ((1.0 - _rt.rexp(((-theta))))))))

def pioneerFraction(advantage, width, p):
    return _rt.rdiv((_rt.rdiv(advantage, _rt.lpow(width, p))), ((1.0 + _rt.rdiv(advantage, _rt.lpow(width, p)))))

def genealogicalTimescale(width, p):
    return power(width, p)

def speedTiltBetaMergerRate(β, b, k):
    return (speedTiltFullMergerRate(β, ((k - 2.0))) * speedTiltNonMergerFactor(β, k, ((b - k))))

def speedTiltCollisionScaleCoefficient(β):
    return _rt.rdiv(1.0, ((β + 1.0)))

def speedTiltRawMergerCoefficient(β, b, k):
    return (speedTiltCollisionScaleCoefficient(β) * speedTiltBetaMergerRate(β, b, k))

def speedTiltPairCollisionScale(β, d):
    return (d * speedTiltCollisionScaleCoefficient(β))

def speedTiltTwoFamilyCollisionScale(β, d):
    return _rt.rdiv(_rt.lpow(d, 2.0), ((((β + 2.0)) * ((β + 3.0)))))

def speedBiasParameterFromTripleRate(rate):
    return (_rt.rinv(rate) - 2.0)

def frontSpeedBiasParameter(θ, γ):
    return _rt.rdiv(θ, γ)

def frontSpeedTiltFromTripleRate(rate, γ):
    return (γ * speedBiasParameterFromTripleRate(rate))

def criticallyPulledLinearRateLadder(coefficient, n):
    return (coefficient * (((n) + 1.0)))

def stablePowerRateLadder(alpha, n):
    return _rt.lpow((((n) + 1.0)), alpha)

def IsCompleteCatalogue(E, label):
    return all(all(((E(x, y) == (label(x) == label(y)))) for y in range(int(_rt.sumdim('y', len(E[0]), len(label))))) for x in range(int(_rt.sumdim('x', len(E), len(label)))))

def cumulantTensorEnergy(order, tensor):
    return sum((_rt.lpow(tensor(indices), 2.0)) for indices in range(int(_rt.sumdim('indices', len(tensor)))))

def entryPowerSum(covariance, order):
    return sum((sum((_rt.lpow(covariance[int(left)][int(right)], order)) for right in range(int(len(covariance))))) for left in range(int(len(covariance))))

def pushedThirdMomentTensor(mixing, kappa, a, b, c):
    return _rt.mul(kappa, sum((_rt.mul(_rt.mul(mixing[int(a)][int(i)], mixing[int(b)][int(i)]), mixing[int(c)][int(i)])) for i in range(int(len(mixing)))))

def thirdTensorEnergy(tensor):
    return sum((sum((sum((_rt.lpow(tensor(a, b, c), 2.0)) for c in range(int(_rt.sumdim('c', len(tensor[0][0])))))) for b in range(int(_rt.sumdim('b', len(tensor[0])))))) for a in range(int(_rt.sumdim('a', len(tensor)))))

def entryCubeSum(covariance):
    return sum((sum((_rt.lpow(covariance[int(i)][int(j)], 3.0)) for j in range(int(len(covariance))))) for i in range(int(len(covariance))))

def gramCovariance(mixing):
    return _rt.mul(('_rt.transpose', 'mixing'), mixing)

def pushedFourthCumulantTensor(mixing, kappa, a, b, c, d):
    return _rt.mul(kappa, sum((_rt.mul(_rt.mul(_rt.mul(mixing[int(a)][int(i)], mixing[int(b)][int(i)]), mixing[int(c)][int(i)]), mixing[int(d)][int(i)])) for i in range(int(len(mixing)))))

def fourthTensorEnergy(tensor):
    return sum((sum((sum((sum((_rt.lpow(tensor(a, b, c, d), 2.0)) for d in range(int(_rt.sumdim('d', len(tensor[0][0][0])))))) for c in range(int(_rt.sumdim('c', len(tensor[0][0])))))) for b in range(int(_rt.sumdim('b', len(tensor[0])))))) for a in range(int(_rt.sumdim('a', len(tensor)))))

def entryFourthSum(covariance):
    return sum((sum((_rt.lpow(covariance[int(i)][int(j)], 4.0)) for j in range(int(len(covariance))))) for i in range(int(len(covariance))))

def ldPowerScore(covariance, power, j):
    return sum((_rt.lpow(covariance[int(i)][int(j)], power)) for i in range(int(len(covariance))))

def blockEntryCubeMean(covariance):
    return _rt.rdiv(entryCubeSum(covariance), 2.0)

def blockEntryFourthMean(covariance):
    return _rt.rdiv(entryFourthSum(covariance), 2.0)

def lowSNRFourthOrientationCoefficient(fourthCumulant, h4):
    return (-((_rt.rdiv(_rt.lpow(fourthCumulant, 2.0), 48.0) * h4)))

def gaussianDesignFourthSpectralMoment(c, m1, m2, m3, m4):
    return (((m4 + (c * ((((4.0 * m1) * m3) + (2.0 * _rt.lpow(m2, 2.0)))))) + (((6.0 * _rt.lpow(c, 2.0)) * _rt.lpow(m1, 2.0)) * m2)) + (_rt.lpow(c, 3.0) * _rt.lpow(m1, 4.0)))

def lowSNRFourthCoefficient(c, variance, fourthCumulant, m1, m2, m3, m4, h4):
    return ((-((_rt.rdiv(_rt.lpow(variance, 4.0), 8.0) * gaussianDesignFourthSpectralMoment(c, m1, m2, m3, m4)))) - (_rt.rdiv(_rt.lpow(fourthCumulant, 2.0), 48.0) * h4))

def entrySquareSum(covariance):
    return sum((sum((_rt.lpow(covariance[int(i)][int(j)], 2.0)) for j in range(int(len(covariance))))) for i in range(int(len(covariance))))

def lowSNRThirdCoefficient(aspect, variance, thirdMoment, m1, m2, m3, h3):
    return ((_rt.rdiv(_rt.lpow(variance, 3.0), 6.0) * (((m3 + _rt.rdiv(((3.0 * m1) * m2), aspect)) + _rt.rdiv(_rt.lpow(m1, 3.0), _rt.lpow(aspect, 2.0))))) - (_rt.rdiv(_rt.lpow(thirdMoment, 2.0), 12.0) * h3))

def ldOrientationInvariant(order, ld):
    return entryPowerSum(ld, order)

def ldOrientationThirdInvariant(ld):
    return entryCubeSum(ld)

def ldOrientationFourthInvariant(ld):
    return entryFourthSum(ld)

def cauchyConditioningProfile(θ):
    return (2.0 * ((((_rt.rlog(((1.0 + _rt.lpow(θ, 2.0)))) + (((θ - 1.0)) * _rt.rlog(((1.0 - θ))))) - (((1.0 + θ)) * _rt.rlog(((1.0 + θ))))) + ((2.0 * θ) * _rt.arctan((_rt.rdiv(1.0, θ)))))))

def CauchyConditioningStationary(θ):
    return (_rt.arctan((_rt.rdiv(1.0, θ))) == ((_rt.rdiv(1.0, 2.0)) * _rt.rlog((_rt.rdiv(((1.0 + θ)), ((1.0 - θ)))))))

def stableSieveDimension(kappa, L):
    return _rt.rdiv(_rt.rlog(L), kappa)

def algorithmicRiskSignature(risk, design):
    return (lambda algorithm, model, loss: risk(algorithm, design, model, loss))

def AlgorithmicallyEquivalent(risk, left, right):
    return all(all(all(((risk(algorithm, left, model, loss) == risk(algorithm, right, model, loss))) for loss in range(int(_rt.sumdim('loss', len(risk[0][0][0]))))) for model in range(int(_rt.sumdim('model', len(risk[0][0]))))) for algorithm in range(int(_rt.sumdim('algorithm', len(risk)))))

def balancedRankOneGraphSum(p, vertices, edges):
    return _rt.rdiv(_rt.lpow((p), vertices), _rt.lpow((p), ((edges + 1.0))))

def balancedRankOneTrafficCoordinate(hasOddDegree, p, vertices, edges):
    return (0.0 if hasOddDegree else balancedRankOneGraphSum(p, vertices, edges))

def finiteRankOneTrafficCorrection(coefficient, hasOddDegree, vertices, edges, population):
    return sum((_rt.mul(coefficient[int(term)], balancedRankOneTrafficCoordinate((hasOddDegree(term)), population, (vertices(term)), (edges(term))))) for term in range(int(len(coefficient))))

def BalancedRankOneCoordinate(population):
    return Sum((Fin(population)), (Fin(population)))

def constantOneVector():
    return (lambda _coordinate: 1.0)

def balancedRankOneOrthogonalSpin(population):
    return constantOneVector()

def rankOneEnergyDensity(baseline, spikeStrength, population, alignment):
    return (baseline + (spikeStrength * _rt.lpow((_rt.rdiv(alignment, population)), 2.0)))

def cwRate(m):
    return ((_rt.rdiv(((1.0 + m)), 2.0) * _rt.rlog(((1.0 + m)))) + (_rt.rdiv(((1.0 - m)), 2.0) * _rt.rlog(((1.0 - m)))))

def cwObjective(tlam, m):
    return ((_rt.rdiv(tlam, 2.0) * _rt.lpow(m, 2.0)) - cwRate(m))

def cwPinskerGap(m):
    return (cwRate(m) - _rt.rdiv(_rt.lpow(m, 2.0), 2.0))

def cwPinskerGapDerivative(m):
    return (_rt.rdiv(((_rt.rlog(((1.0 + m))) - _rt.rlog(((1.0 - m))))), 2.0) - m)

def cwVariationalPressureGap(tlam):
    return sSup((cwPressureValueSet(tlam)))

def finiteCWMagnetization(population, upSpins):
    return ((2.0 * (upSpins)) - population)

def finiteCWEmpiricalMagnetization(population, upSpins):
    return _rt.rdiv(finiteCWMagnetization(population, upSpins), population)

def cwPositiveTrialWeight(m):
    return _rt.rdiv(((1.0 + m)), 2.0)

def cwNegativeTrialWeight(m):
    return _rt.rdiv(((1.0 - m)), 2.0)

def finiteCWPressureGap(population, tlam):
    return _rt.rdiv(_rt.rlog((finiteCWPartition(population, tlam))), population)

def finiteBaselineRademacherPressure(baseline, temperature):
    return _rt.rdiv((temperature * baseline), 2.0)

def finiteRankOneRademacherPressure(baseline, population, temperature, spikeStrength):
    return (finiteBaselineRademacherPressure(baseline, temperature) + finiteCWPressureGap(population, ((temperature * spikeStrength))))

def diagonalTrafficCorrection(baseline, edges, iteration):
    return (_rt.lpow((_rt.rdiv(1.0, 4.0)), iteration) * ((_rt.lpow(((baseline + 2.0)), edges) - _rt.lpow(baseline, edges))))

def mesoscopicGFOMStep(iteration, vector):
    return (lambda coordinate: ((2.0 * vector(coordinate)) if (_rt._proj(_rt._proj(coordinate, '2'), 'val') == 0.0) else 0.0))

def mesoscopicGFOMUnitInput(iteration):
    return constantOneVector()

def mesoscopicGFOMEnergy(iteration, runtime):
    return (_rt.lpow((4.0), runtime) * _rt.lpow((_rt.rdiv(1.0, 4.0)), iteration))

def amplifiedDegreeOneTrafficDifference(baseline, iteration):
    return (_rt.lpow((4.0), iteration) * diagonalTrafficCorrection(baseline, 1.0, iteration))

def FiniteOutlierCoordinate(population):
    return Option((Fin(population)))

def finiteBulkDiagonal(baseline, population):
    return (lambda _coordinate: baseline)

def normalizedDiagonalSpectralMoment(population, edges, diagonal):
    return _rt.rdiv((sum((_rt.lpow(diagonal(coordinate), edges)) for coordinate in range(int(_rt.sumdim('coordinate', len(diagonal)))))), ((population + 1.0)))

def normalizedDiagonalSpectralObservable(population, observable, diagonal):
    return _rt.rdiv((sum((observable((diagonal(coordinate)))) for coordinate in range(int(_rt.sumdim('coordinate', len(diagonal)))))), ((population + 1.0)))

def IsDiagonalMaximum(diagonal, maximum):
    return ((all(((diagonal[int(coordinate)] <= maximum)) for coordinate in range(int(len(diagonal))))) and any(((diagonal[int(coordinate)] == maximum)) for coordinate in range(int(len(diagonal)))))

def SameEqualityPattern(left, right):
    return all(all((((left(first) == left(second)) == (right(first) == right(second)))) for second in range(int(_rt.sumdim('second', len(left), len(right))))) for first in range(int(_rt.sumdim('first', len(left), len(right)))))

def EqualityPattern(Slot, Label):
    return Quotient((sameEqualityPatternSetoid(Slot, Label)))

def equalityPatternProfile(value, graph):
    return sum(((value(monomial) if (equalityPatternShape(monomial) == graph) else 0.0)) for monomial in range(int(_rt.sumdim('monomial', len(value)))))

def degreeAtMostCanonicalTrafficProfile(value):
    return (lambda degree, graph: equalityPatternProfile((value(degree)), graph))

def degreeAtMostRootedCanonicalTrafficProfile(value):
    return (lambda degree, graph: equalityPatternProfile((value(degree)), graph))

def evaluate(risk, traffic):
    return sum(((_rt._proj(risk, 'coefficient')(graph) * traffic(graph))) for graph in range(int(_rt.sumdim('graph', len(_rt._proj(risk, 'coefficient')), len(traffic)))))

def totalTraffic(D):
    return (lambda _graph: 1.0)

def momentSeparationNode(D, index):
    return (1.0 + _rt.rdiv((index), ((D + 1.0))))

def momentUniformWeight(D):
    return _rt.rdiv(1.0, ((D + 2.0)))

def momentPerturbationScale(D, weight):
    return _rt.rdiv(1.0, ((((D + 2.0)) * ((1.0 + sum((_rt.rabs(weight(index))) for index in range(int(_rt.sumdim('index', len(weight))))))))))

def perturbedMomentWeight(D, weight, index):
    return (momentUniformWeight(D) + (momentPerturbationScale(D, weight) * weight(index)))

def referenceMomentWeight(D, _index):
    return momentUniformWeight(D)

def finiteDiagonalTrafficProfile(D, weight):
    return (lambda degree: sum(((weight(index) * _rt.lpow(momentSeparationNode(D, index), (degree)))) for index in range(int(_rt.sumdim('index', len(weight))))))

def finiteDiagonalNextTrafficCoordinate(D, weight):
    return sum(((weight(index) * _rt.lpow(momentSeparationNode(D, index), ((D + 1.0))))) for index in range(int(_rt.sumdim('index', len(weight)))))

def SeparatesAtNextDiagonalTraffic(D, left, right):
    return (finiteDiagonalNextTrafficCoordinate(D, left) != finiteDiagonalNextTrafficCoordinate(D, right))

def ExponentialProfilePoint(bound):
    return BoundedExponentialProfile(bound)

def exponentialProfileDistance(left, right):
    return dist((show(ExponentialProfilePoint, bound, from_, left)), (show(ExponentialProfilePoint, bound, from_, right)))

def rawNuclearDistance(spectrum):
    return sum((_rt._proj(spectrum, 'singularValue')(coordinate)) for coordinate in range(int(_rt.sumdim('coordinate', len(_rt._proj(spectrum, 'singularValue'))))))

def xiSpeedTiltWeight(theta, mark):
    return _rt.rexp(((-((theta * _rt._proj(mark, '2'))))))

def oneFamilyMassPartition(x):
    return (lambda i: (x if (i == 0.0) else 0.0))

def totalFamilyFraction(η):
    return sum((η[int(i)]) for i in range(int(len(η))))

def paintboxWeight(η):
    return sum((_rt.lpow(η[int(i)], 2.0)) for i in range(int(len(η))))

def disjointPairMergeProbability(η):
    return _rt.mul(3.0, sum((sum(((0.0 if (i == j) else _rt.mul(_rt.lpow(η[int(i)], 2.0), _rt.lpow(η[int(j)], 2.0)))) for j in range(int(len(η))))) for i in range(int(len(η)))))

def HasTwoPositiveFamilies(η):
    return any(any(((((i != j) and (0.0 < η[int(i)])) and (0.0 < η[int(j)]))) for j in range(int(len(η)))) for i in range(int(len(η))))

def boundaryTiltMass(logMgf, criticalParameter, criticalSpeed):
    return (2.0 * _rt.rexp(((((-criticalParameter) * criticalSpeed) + logMgf))))

def boundaryTiltCenteredFirstMoment(logMgf, logMgfDerivative, criticalParameter, criticalSpeed):
    return (((2.0 * criticalParameter) * _rt.rexp(((((-criticalParameter) * criticalSpeed) + logMgf)))) * ((criticalSpeed - logMgfDerivative)))

def derivativeSubtreeContribution(basePotential, additiveMass, derivativeMass):
    return (_rt.rexp(((-basePotential))) * (((basePotential * additiveMass) + derivativeMass)))

def selectedPioneerFlux(weight):
    return sum((weight[int(pioneer)]) for pioneer in range(int(len(weight))))

def paretoExceedanceMass(tailConstant, threshold, weight):
    return _rt.rdiv((tailConstant * weight), threshold)

def distinctPairExceedanceMass(mass):
    return sum((sum(((0.0 if (first == second) else _rt.mul(mass[int(first)], mass[int(second)]))) for second in range(int(len(mass))))) for first in range(int(len(mass))))

def IsSelectedFluxDecomposition(exogenousFlux, selectedFlux, prunedFlux):
    return all(((exogenousFlux(index) == (selectedFlux(index) + prunedFlux(index)))) for index in range(int(_rt.sumdim('index', len(exogenousFlux), len(selectedFlux), len(prunedFlux)))))

def pioneerWeightFraction(w):
    return saturation(w)

def pioneerWeightDisplacement(gamma, w):
    return ((_rt.rdiv(1.0, gamma)) * _rt.rlog(((1.0 + w))))

def amplitudeFront(gamma, amplitude):
    return ((_rt.rdiv(1.0, gamma)) * _rt.rlog(amplitude))

def HasCommonProfileRelaxation(conversion, backgroundAmplitude, pioneerAmplitude, backgroundCount, pioneerCount):
    return ((backgroundAmplitude == (conversion * backgroundCount)) and (pioneerAmplitude == (conversion * pioneerCount)))

def bertrandTerm(n):
    return (1.0 if (n <= 1.0) else _rt.rdiv(1.0, (((n) * _rt.rlog(n)))))

def bsRate(b):
    return ((b) * ((harmonicSum(b) - 1.0)))

def betaFn(a, b):
    return _rt.rdiv((Gamma(a) * Gamma(b)), Gamma(((a + b))))

def betaCoalescentRate(alpha, b, k):
    return betaFn((((k) - alpha)), ((((b) - (k)) + alpha)))

def expectedSegmentLength(k):
    return _rt.rdiv((k), deathRate(k))

def comesDownFromInfinity(γ):
    return Summable((lambda b, ℕ: _rt.rdiv(1.0, γ(((b + 2.0))))))

def descentCurve(t):
    return _rt.rdiv(2.0, t)

def diffusionOnPow(m, x):
    return (_rt.rdiv((x * ((1.0 - x))), 2.0) * ((((((m) + 2.0)) * (((m) + 1.0))) * _rt.lpow(x, m))))

def coalescentOnPow(m, x):
    return (deathRate(((m + 2.0))) * ((_rt.lpow(x, ((m + 1.0))) - _rt.lpow(x, ((m + 2.0))))))

def pairCoalescenceProb(N, v):
    return _rt.rdiv(v, (((N) - 1.0)))

def wrightFisherSecondFactorialMoment(N):
    return _rt.rdiv((((N) - 1.0)), (N))

def neutralFixation(x):
    return identifiedWith(x)

def selectedFixation(α, x):
    return _rt.rdiv(((1.0 - _rt.rexp(((-((α * x))))))), ((1.0 - _rt.rexp(((-α))))))

def selectedFixationDeriv(α, x):
    return _rt.rdiv((α * _rt.rexp(((-((α * x)))))), ((1.0 - _rt.rexp(((-α))))))

def selectedFixationDeriv2(α, x):
    return (-(_rt.rdiv((_rt.lpow(α, 2.0) * _rt.rexp(((-((α * x)))))), ((1.0 - _rt.rexp(((-α))))))))

def branchSurvival(T):
    return _rt.rexp(((-T)))

def discordanceProb(T):
    return ((_rt.rdiv(2.0, 3.0)) * branchSurvival(T))

def blockHoldMeasure(k):
    return holdMeasure((deathRate(k)))

def coalescentLawExp(n, k, m, rate):
    return coalescentLaw(n, k, m, (blockHoldMeasure(rate)))

def EInf():
    return Setoid(ℕ)

def jumpProb(k):
    return _rt.rdiv(1.0, deathRate(k))

def kingmanRate(_b, k):
    return (1.0 if (k == 2.0) else 0.0)

def lookdownApply(i, j, c):
    return (lambda l: (c(i) if (l == j) else c(l)))

def colourIndicator(Z, r, i):
    return (lambda ω: ((1.0) if (Z(i, ω) == r) else 0.0))

def pairTime(c, p, t_3, t_2):
    return (t_3 if (p == c) else (t_3 + t_2))

def pairTime4(s, p, t_4, t_3, t_2):
    return (t_4 if (p == 0.0) else ((t_4 + t_3) if (((((s == 0.0) and (p == 5.0))) or (((s == 1.0) and (((p == 1.0) or (p == 3.0)))))) or (((s == 2.0) and (((p == 2.0) or (p == 4.0)))))) else ((t_4 + t_3) + t_2)))

def transitTime(n, hold):
    return descentTime(n, hold, 1.0)

def pathState(n, chain, hold, t):
    return chain((blockCountAt(n, hold, t)))

def returnProb(n):
    return _rt.rdiv((_rt._proj(((2.0 * n)), 'choose')(n)), _rt.lpow(4.0, n))

def deathRate(k):
    return Descent_Core_pairCount(k)

def survivalFactor(x):
    return _rt.rdiv((((x) - 1.0)), (((x) + 1.0)))

def transitDensityTerm(m, t):
    return ((deathRate(m) * (((2.0 * (m)) - 1.0))) * _rt.rexp(((-((deathRate(m) * t))))))

def recombRate(k, rho):
    return halfLineageRate(k, rho)

def argEventRate(k, rho):
    return (deathRate(k) + recombRate(k, rho))

def recombFirstProb(k, rho):
    return _rt.rdiv(recombRate(k, rho), argEventRate(k, rho))

def coalesceFirstProb(k, rho):
    return _rt.rdiv(deathRate(k), argEventRate(k, rho))

def meanTimeActive(c, r):
    return (1.0 + _rt.rdiv((2.0 * c), r))

def meanTimeDormant(c, r):
    return (_rt.rdiv(1.0, r) + meanTimeActive(c, r))

def expectedSegregatingSites(θ, n):
    return (_rt.rdiv(θ, 2.0) * expectedTotalBranchLength(n))

def wattersonEstimator(S, n):
    return _rt.rdiv(S, harmonicSum(((n - 1.0))))

def expectedPairwiseDifferences(θ):
    return expectedSegregatingSites(θ, 2.0)

def expectedTajimaNumerator(θ, n):
    return (expectedPairwiseDifferences(θ) - wattersonEstimator((expectedSegregatingSites(θ, n)), n))

def branchRate(k, sigma):
    return halfLineageRate(k, sigma)

def asgEventRate(k, sigma):
    return (deathRate(k) + branchRate(k, sigma))

def spectrumBranchLength(i):
    return _rt.rdiv(2.0, (i))

def expectedSpectrum(θ, i):
    return (_rt.rdiv(θ, 2.0) * spectrumBranchLength(i))

def voterStepMap(u):
    return (lambda l: (_rt._proj(u, '1') if (l == _rt._proj(u, '2')) else l))

def voterPedigree(u):
    return (lambda s: voterStepMap((u(s))))

def voterAncestralRel(u, sample, s):
    return ancestralRel((voterPedigree(u)), sample, s)

def varSegregatingSites(θ, n):
    return ((θ * harmonicSum(((n - 1.0)))) + (_rt.lpow(θ, 2.0) * harmonicSumSq(((n - 1.0)))))

def varWattersonEstimator(θ, n):
    return _rt.rdiv(varSegregatingSites(θ, n), _rt.lpow(harmonicSum(((n - 1.0))), 2.0))

def tajimaVarPairwise(θ, n):
    return ((_rt.rdiv((((n) + 1.0)), ((3.0 * (((n) - 1.0))))) * θ) + (_rt.rdiv((2.0 * (((_rt.lpow((n), 2.0) + (n)) + 3.0))), (((9.0 * (n)) * (((n) - 1.0))))) * _rt.lpow(θ, 2.0)))

def ER(n):
    return Setoid((Fin(n)))

def mergeMap(ξ, a, b):
    return (lambda c: (a if (c == b) else c))

def Descent_Coalescent_Covers(ξ, η):
    return ((ξ <= η) and ((blocks(η) + 1.0) == blocks(ξ)))

def stepLaw(ξ, hk):
    return _rt._proj(_rt._proj((jumpStep(ξ, hk)), 'toMeasure'), 'prod')((holdMeasure((deathRate((blocks(ξ)))))))

def meanTimeSame(_M):
    return 2.0

def meanTimeDiff(M):
    return (2.0 + _rt.rdiv(1.0, M))

def fstFromMigration(M):
    return _rt.rdiv(((meanTimeDiff(M) - meanTimeSame(M))), meanTimeDiff(M))

def sharedPath3(c, p, q, t_3, t_2):
    return (t_3 if ((c == p) or (c == q)) else (t_3 + (2.0 * t_2)))

def sharedPath4(s, d, t_3, t_2):
    return (0.0 if (d == 0.0) else ((t_3 + (2.0 * t_2)) if (s == 0.0) else t_3))

def Descent_Coalescent_pairCount(n):
    return _rt.rdiv((n * ((n - 1.0))), 2.0)

def sharingCount(n):
    return _rt.rdiv(((n * ((n - 1.0))) * ((n - 2.0))), 2.0)

def disjointCount(n):
    return _rt.rdiv((((n * ((n - 1.0))) * ((n - 2.0))) * ((n - 3.0))), 8.0)

def varPairwiseFromTree(θ, n):
    return ((_rt.rdiv((((Descent_Coalescent_pairCount(n) + sharingCount(n)) + ((_rt.rdiv(2.0, 3.0)) * disjointCount(n)))), _rt.lpow(Descent_Coalescent_pairCount(n), 2.0)) * θ) + (_rt.rdiv(((Descent_Coalescent_pairCount(n) + (2.0 * ((_rt.rdiv(sharingCount(n), 3.0) + ((_rt.rdiv(2.0, 9.0)) * disjointCount(n))))))), _rt.lpow(Descent_Coalescent_pairCount(n), 2.0)) * _rt.lpow(θ, 2.0)))

def chainTrajFrom(n, ξ):
    return chainTraj(n, ((lambda _: ξ)))

def relativeSize(β, t):
    return _rt.rexp(((-((β * t)))))

def timeChange(β, t):
    return _rt.rdiv(((_rt.rexp(((β * t))) - 1.0)), β)

def pairSurvival(β, t):
    return _rt.rexp(((-(timeChange(β, t)))))

def ancestralPartitionLaw(N, k):
    return _rt._proj((parentAssignment(N, k)), 'map')(ancestralPartition)

def pairDistinct(N, s):
    _prev = 1.0
    for _ in range(int(s)):
        _prev = (noCoalescenceProb(N, 2.0) * _prev)
    return _prev

def MergerShape():
    return Multiset(ℕ)

def copiedBinaryJointExpectation():
    return _rt.rdiv(((((1.0) * 1.0) + (((-1.0)) * ((-1.0))))), 2.0)

def copiedBinaryConditionalProductExpectation():
    return _rt.rdiv(((((_rt.rdiv((((1.0) + ((-1.0)))), 2.0)) * 1.0) + ((_rt.rdiv((((1.0) + ((-1.0)))), 2.0)) * ((-1.0))))), 2.0)

def FullSupport(J):
    return all(((_rt._proj(J, 'mass')(x) != 0.0)) for x in range(int(_rt.sumdim('x', len(_rt._proj(J, 'mass'))))))

def modulusCopyCoupling():
    return (lambda x: (_rt.rdiv(1.0, 2.0) if (x(0.0) == x(1.0)) else 0.0))

def copyWitnessValue():
    return (lambda i: (0.0 if (i == 0.0) else 1.0))

def gainBounded():
    return (lambda _: 1.0)

def gainLog(n):
    return _rt.rlog(n)

def gainPolynomialRow(β, n):
    return (_rt.lpow(n, β) * _rt.rlog(n))

def gainLinear(n):
    return identifiedWith(n)

def toFiberCoupling(C):
    return _rt._proj(C, 'mass')

def observable(M, θ, h):
    return (lambda x, p: _rt.add(_rt._proj(M, 'action')(x, (θ(x)), p), h[int(x)][int(p)]))

def actionGap(M, θ, θ_p):
    return (lambda x, p: (_rt._proj(M, 'action')(x, (θ(x)), p) - _rt._proj(M, 'action')(x, (θ_p(x)), p)))

def labelMass(π, p, x):
    return sum(((p[int(g)] if (π(g) == x) else 0.0)) for g in range(int(len(p))))

def fiberConditional(π, p, x, g):
    return (_rt.rdiv(p[int(g)], labelMass(π, p, x)) if (π(g) == x) else 0.0)

def pointLaw(g):
    return (lambda g_p: (1.0 if (g_p == g) else 0.0))

def totalVariationGap(μ, ν):
    return sum((_rt.rabs(_rt.sub(μ[int(g)], ν[int(g)]))) for g in range(int(len(μ))))

def interactionTraitLaw(theta, g):
    return ((_rt.rdiv(1.0, 4.0)) * ((interactionRisk(theta, _rt._proj(g, '1'), _rt._proj(_rt._proj(g, '2'), '1')) if (_rt._proj(_rt._proj(g, '2'), '2') == 1.0) else (1.0 - interactionRisk(theta, _rt._proj(g, '1'), _rt._proj(_rt._proj(g, '2'), '1'))))))

def traitIndicator(g):
    return (1.0 if (_rt._proj(_rt._proj(g, '2'), '2') == 1.0) else 0.0)

def admissibleInteractionTraitLaw(theta, g):
    return interactionTraitLaw(_rt._proj(theta, '1'), g)

def exposureGivenStratum(g):
    return (confoundedConditionalRisk(_rt._proj(g, '2')) if (_rt._proj(g, '1') == 1.0) else (1.0 - confoundedConditionalRisk(_rt._proj(g, '2'))))

def stratumFrequency(beta, s):
    return (beta if (s == 1.0) else (1.0 - beta))

def confoundedExposureLaw(beta, g):
    return (stratumFrequency(beta, _rt._proj(g, '2')) * exposureGivenStratum(g))

def admissibleConfoundedExposureLaw(beta, g):
    return confoundedExposureLaw(_rt._proj(beta, '1'), g)

def exposureIndicator(g):
    return (1.0 if (_rt._proj(g, '1') == 1.0) else 0.0)

def exampleComponent(k, g):
    return (((_rt.rdiv(1.0, 2.0) if (g == 0.0) else _rt.rdiv(1.0, 4.0))) if (k == 0.0) else ((_rt.rdiv(1.0, 2.0) if (g == 2.0) else _rt.rdiv(1.0, 4.0))))

def exampleReference(k):
    return (_rt.rdiv(1.0, 3.0) if (k == 0.0) else _rt.rdiv(2.0, 3.0))

def exampleTrait(g):
    return ((-1.0) if (g == 0.0) else (1.0 if (g == 2.0) else 0.0))

def exampleComponentResidual():
    return componentRepresentationResidual((conditionalSectionMean(exampleTrait, (fiberConditional((componentPosterior(exampleComponent, exampleReference)), (componentMixtureDensity(exampleComponent, exampleReference)), (componentPosterior(exampleComponent, exampleReference, 0.0)))))), (componentPosterior(exampleComponent, exampleReference, 0.0)), ((lambda k: conditionalSectionMean(exampleTrait, (exampleComponent(k))))))

def probitCurve(a, b, x):
    return Phi((((a * x) + b)))

def IsInvariantWeight(ϖ, L):
    return all((sum(((_rt.mul(ϖ[int(i)], L[int(i)][int(j)]) == 0.0)) for i in range(int(len(ϖ))))) for j in range(int(len(ϖ))))

def KillsConstants(L):
    return all((sum(((L[int(i)][int(j)] == 0.0)) for j in range(int(len(L))))) for i in range(int(len(L))))

def pushForward(M, f, i):
    return sum((_rt.mul(M[int(i)][int(j)], f[int(j)])) for j in range(int(len(M))))

def reconstruct(M, p, κ, i):
    return _rt.rdiv(pushForward(M, ((lambda j: _rt.mul(κ[int(j)], p[int(j)]))), i), pushForward(M, p, i))

def errorEnergy(w, lam, t):
    return sum((_rt.mul(w[int(k)], _rt.rexp((_rt.neg((_rt.mul(_rt.mul(2.0, lam[int(k)]), t))))))) for k in range(int(len(w))))

def convolvedLiability(ν, s):
    return _rt._proj((_rt._proj((gaussianReal(0.0, 1.0)), 'prod')(ν)), 'map')((lambda q: (_rt._proj(q, '2') - (s * _rt._proj(q, '1')))))

def transportMass(P, mass, y):
    return sum((_rt.mul(mass[int(x)], P[int(x)][int(y)])) for x in range(int(len(P))))

def IsMassPreservingKernel(P):
    return all((sum(((P[int(x)][int(y)] == 1.0)) for y in range(int(len(P))))) for x in range(int(len(P))))

def IsNonnegativeKernel(P):
    return all(all(((0.0 <= P[int(x)][int(y)])) for y in range(int(len(P)))) for x in range(int(len(P))))

def markedMass(population, response, x):
    return _rt.mul(population[int(x)], response[int(x)])

def transportedResponse(P, population, response, _hpositive, y):
    return _rt.rdiv(transportMass(P, (markedMass(population, response)), y), transportMass(P, population, y))

def composeKernel(P, Q, x, z):
    return sum((_rt.mul(P[int(x)][int(y)], Q[int(y)][int(z)])) for y in range(int(len(P))))

def reverseBridge(P, population, _hpositive, y, x):
    return _rt.rdiv(_rt.mul(population[int(x)], P[int(x)][int(y)]), transportMass(P, population, y))

def stateZeroResponse(i):
    return (1.0 if (i == 0.0) else 0.0)

def stateOneResponse(i):
    return kronecker(i, 1.0)

def symmetricTwoStateKernel(switch, i, j):
    return ((1.0 - switch) if (i == j) else switch)

def twoStateContrast(i):
    return (1.0 if (i == 0.0) else (-1.0))

def applyKernel(P, f, i):
    return sum((_rt.mul(P[int(i)][int(j)], f[int(j)])) for j in range(int(len(P))))

def twoStateCurve(baseline, amplitude, i):
    return (baseline + (amplitude * twoStateContrast(i)))

def ouVariance(horizon):
    return _rt.rdiv(((1.0 - _rt.rexp(((-(((2.0 * _rt._proj(horizon, 'rate')) * _rt._proj(horizon, 'time')))))))), ((2.0 * _rt._proj(horizon, 'rate'))))

def probitScaleFactor(a0, horizon):
    return _rt.rsqrt(((1.0 + (_rt.lpow(a0, 2.0) * ouVariance(horizon)))))

def probitSlope(a0, horizon):
    return _rt.rdiv((a0 * _rt.rexp(((-((_rt._proj(horizon, 'rate') * _rt._proj(horizon, 'time'))))))), probitScaleFactor(a0, horizon))

def probitIntercept(a0, b0, horizon):
    return _rt.rdiv(b0, probitScaleFactor(a0, horizon))

def ancestryMixtureCorrelation(rho, positiveEnvironmentMass):
    return mixedEnvironmentCorrelation(rho, positiveEnvironmentMass)

def onePointPerformance(weight, score):
    return sum((_rt.mul(weight[int(y)], score[int(y)])) for y in range(int(len(weight))))

def targetOnlyTransportPerformance(weight, transition, score):
    return sum((_rt.mul(weight[int(x)], sum((_rt.mul(transition[int(x)][int(y)], score[int(y)])) for y in range(int(len(weight)))))) for x in range(int(len(weight))))

def crossStatePerformance(weight, transition, quality):
    return sum((_rt.mul(weight[int(x)], sum((_rt.mul(transition[int(x)][int(y)], quality[int(x)][int(y)])) for y in range(int(len(weight)))))) for x in range(int(len(weight))))

def BinaryBiologicalState():
    return Fin(2.0)

def binaryStateWeight(_):
    return _rt.rdiv(1.0, 2.0)

def persistentTransition(x, y):
    return kronecker(x, y)

def switchingTransition(x, y):
    return antiKronecker(x, y)

def targetAnnotation(y):
    return kronecker(y, 1.0)

def contextMatchQuality(x, y):
    return kronecker(x, y)

def jointTransportLaw(transition, g):
    return _rt.mul(binaryStateWeight(_rt._proj(g, '1')), transition[int(_rt._proj(g, '1'))][int(_rt._proj(g, '2'))])

def binaryTransportFamily(persists):
    return jointTransportLaw(((persistentTransition if persists else switchingTransition)))

def contextMatchSectionOscillation(y):
    return finiteSectionOscillation(((lambda persists, y: (labelMass(((lambda g, TransportPair: _rt._proj(g, '2'))), (binaryTransportFamily(persists)), y) != 0.0))), ((lambda persists, y: fiberConditional(((lambda g, TransportPair: _rt._proj(g, '2'))), (binaryTransportFamily(persists)), y))), (conditionalSectionMean(((lambda g, TransportPair: contextMatchQuality(_rt._proj(g, '1'), _rt._proj(g, '2')))))), ((lambda a, b, ℝ: _rt.rabs((a - b)))), y)

def contextMatchTotalVariationDiameter(y):
    return finiteSectionDiameter(((lambda persists, y: (labelMass(((lambda g, TransportPair: _rt._proj(g, '2'))), (binaryTransportFamily(persists)), y) != 0.0))), ((lambda persists, y: fiberConditional(((lambda g, TransportPair: _rt._proj(g, '2'))), (binaryTransportFamily(persists)), y))), totalVariationGap, y)

def binaryDynamicsPosterior(_, _1):
    return _rt.rdiv(1.0, 2.0)

def binaryConditionalContextMatch(persists, y):
    return conditionalSectionMean(((lambda g, TransportPair: contextMatchQuality(_rt._proj(g, '1'), _rt._proj(g, '2')))), (fiberConditional(((lambda g, TransportPair: _rt._proj(g, '2'))), (binaryTransportFamily(persists)), y)))

def persistentOnlyDynamicsPosterior(_, persists):
    return binarySecondAnnotation(persists)

def dynamicsContrast():
    return (lambda persists: (1.0 if persists else (-1.0)))

def dynamicsCommonMode(persists):
    return (binaryFirstAnnotation(persists) + binarySecondAnnotation(persists))

def FunctionalDescends(mass, conditionalSection, b):
    return DescendsOn(((lambda P, x: (0.0 < mass[int(P)][int(x)]))), conditionalSection, b)

def OverlapConsistent(mass, conditionalSection, b):
    return PairwiseCompatibleOn(((lambda P, x: (0.0 < mass[int(P)][int(x)]))), conditionalSection, b)

def conditionalSectionMean(f, mu):
    return sum((_rt.mul(mu[int(y)], f[int(y)])) for y in range(int(len(f))))

def BinaryDescentCovariate():
    return Fin(2.0)

def interactionRisk(theta, u, v):
    return ((_rt.rdiv(1.0, 2.0) + theta) if (u == v) else (_rt.rdiv(1.0, 2.0) - theta))

def confoundedConditionalRisk(v):
    return (_rt.rdiv(1.0, 4.0) if (v == 0.0) else _rt.rdiv(3.0, 4.0))

def confoundedMarginalRisk(beta):
    return ((((1.0 - beta)) * (_rt.rdiv(1.0, 4.0))) + (beta * (_rt.rdiv(3.0, 4.0))))

def componentMixtureDensity(q, w, g):
    return sum((_rt.mul(w[int(k)], q[int(k)][int(g)])) for k in range(int(len(q))))

def componentPosterior(q, w0, g, k):
    return _rt.rdiv(_rt.mul(w0[int(k)], q[int(k)][int(g)]), componentMixtureDensity(q, w0, g))

def posteriorTilt(q, w0, w, g):
    return sum((_rt.mul(componentPosterior(q, w0, g, k), (_rt.rdiv(w[int(k)], w0[int(k)])))) for k in range(int(len(q))))

def componentRepresentationResidual(localValue, a, componentValue):
    return residualAgainst(localValue, a, componentValue)

def localizationResidual(localValue, mixtureValue):
    return difference(localValue, mixtureValue)

def jensenResidual(mixtureValue, a, componentValue):
    return residualAgainst(mixtureValue, a, componentValue)

def twoMechanismMixture(w):
    return ((w * (_rt.rdiv(2.0, 10.0))) + (((1.0 - w)) * (_rt.rdiv(9.0, 10.0))))

def threeMechanismMixture(u, v):
    return (((u * (_rt.rdiv(2.0, 10.0))) + (v * (_rt.rdiv(5.0, 10.0)))) + ((((1.0 - u) - v)) * (_rt.rdiv(9.0, 10.0))))

def expanderAgreementFloor():
    return (_rt.rdiv(1.0, 2.0) - _rt.rdiv(_rt.rsqrt(5.0), 6.0))

def Descent_Core_ploidy():
    return 2.0

def Descent_Core_scaledMutationRate(Ne, μ):
    return (((2.0 * Descent_Core_ploidy()) * Ne) * μ)

def Descent_Core_scaledMigrationRate(Ne, m):
    return (((2.0 * Descent_Core_ploidy()) * Ne) * m)

def Descent_Core_islandDemeCorrection(d):
    return ratio(d, ((d - 1.0)))

def scaledFlow(Ne, m, μ, nDemes):
    return ((Descent_Core_scaledMigrationRate(Ne, m) * Descent_Core_islandDemeCorrection(nDemes)) + Descent_Core_scaledMutationRate(Ne, μ))

def fstFromFlow(x):
    return _rt.rdiv(1.0, ((1.0 + x)))

def fstIslandEquilibrium(Ne, m, μ, nDemes):
    return fstFromFlow((scaledFlow(Ne, m, μ, nDemes)))

def Descent_Core_fstFromTau(tau):
    return saturation(tau)

def Descent_Core_hweHeterozygosity(p):
    return ((Descent_Core_ploidy() * p) * ((1.0 - p)))

def dosage(*_a):
    if len(_a) < 1:
        return lambda *_b: dosage(*(_a + _b))
    _e, = _a[:1]
    _t = [0.0, 1.0, 2.0]
    return _t[_rt._ix(_e, 3, 'dosage')]

def Locus(n):
    return Fin(n)

def altFreq(P, l):
    return _rt.rdiv((sum((_rt._proj((_rt._proj(P, 'call')(i, l)), 'dosage')) for i in range(int(_rt.sumdim('i', len(_rt._proj(P, 'call'))))))), ((Descent_Core_ploidy() * (_rt._proj(P, 'nSamples')))))

def hweProb(*_a):
    if len(_a) < 2:
        return lambda *_b: hweProb(*(_a + _b))
    q, _e = _a[:2]
    _t = [_rt.lpow(((1.0 - q)), 2.0), ((2.0 * q) * ((1.0 - q))), _rt.lpow(q, 2.0)]
    return _t[_rt._ix(_e, 3, 'hweProb')]

def Descent_Core_hetRecurrence(Ne, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * _prev)
    return _prev

def heterozygosityLoss(Ne, t):
    return complement((geometricDecay((_rt.rdiv(1.0, ((2.0 * Ne)))), t)))

def Descent_Core_ScoreMoments_r2(m):
    return _rt.rdiv(_rt.lpow(_rt._proj(m, 'predictiveCovariance'), 2.0), ((_rt._proj(m, 'scoreVariance') * _rt._proj(m, 'outcomeVariance'))))

def Descent_Core_ScoreMoments_calibrationSlope(m):
    return ratio(_rt._proj(m, 'predictiveCovariance'), _rt._proj(m, 'scoreVariance'))

def Descent_Core_ScoreMoments_mse(m):
    return ((_rt._proj(m, 'outcomeVariance') - (2.0 * _rt._proj(m, 'predictiveCovariance'))) + _rt._proj(m, 'scoreVariance'))

def Descent_Core_ScoreMoments_portabilityRatio(V_A, V_E, fst):
    return _rt._proj(_rt._proj(ratio, 'r2'), 'r2')((momentsUnderDrift(V_A, V_E, fst)), (momentsUnderDrift(V_A, V_E, 0.0)))

def deployedR2FromTau(V_A, V_E, tau):
    return _rt._proj((momentsUnderDrift(V_A, V_E, (Descent_Core_fstFromTau(tau)))), 'r2')

def deployedR2(p, V_E):
    return _rt._proj((momentsUnderDrift(_rt._proj(p, 'V_A'), V_E, Descent_Core_PopGenParameters_fstEquilibrium(p))), 'r2')

def brier(π, m):
    return ((π * ((1.0 - π))) * complement(Descent_Core_ScoreMoments_r2(m)))

def aucArgument(m):
    return ratio(Descent_Core_ScoreMoments_r2(m), (complement(Descent_Core_ScoreMoments_r2(m))))

def deployedBrier(π, p, V_E):
    return brier(π, (momentsUnderDrift(_rt._proj(p, 'V_A'), V_E, Descent_Core_PopGenParameters_fstEquilibrium(p))))

def deployedR2FromIsland(Ne, m, μ, nDemes, V_A, V_E):
    return _rt._proj((momentsUnderDrift(V_A, V_E, (fstIslandEquilibrium(Ne, m, μ, nDemes)))), 'r2')

def portabilityRatioFromTau(V_A, V_E, tau):
    return Descent_Core_ScoreMoments_portabilityRatio(V_A, V_E, (Descent_Core_fstFromTau(tau)))

def deployedPortabilityRatio(p, V_E):
    return Descent_Core_ScoreMoments_portabilityRatio(_rt._proj(p, 'V_A'), V_E, Descent_Core_PopGenParameters_fstEquilibrium(p))

def atOrigin(p):
    return (_rt._proj(p, 't_div') == 0.0)

def Descent_Core_PopGenParameters_theta(p):
    return Descent_Core_scaledMutationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mu'))

def Descent_Core_PopGenParameters_bigM(p):
    return Descent_Core_scaledMigrationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mig'))

def Descent_Core_PopGenParameters_fstEquilibrium(p):
    return fstFromFlow(((Descent_Core_PopGenParameters_theta(p) + (2.0 * Descent_Core_PopGenParameters_bigM(p)))))

def pair(*_a):
    if len(_a) < 4:
        return lambda *_b: pair(*(_a + _b))
    s, t, p, _e = _a[:4]
    _t = [s, t]
    return _t[_rt._ix(_e, 2, 'pair')]

def withTarget(f, t):
    return pair((f(0)), t)

def ratio(a, b):
    return _rt.rdiv(a, b)

def product(a, b):
    return (a * b)

def difference(a, b):
    return (a - b)

def Descent_Core_sum(a, b):
    return (a + b)

def proportionalReduction(a, b):
    return (1.0 - _rt.rdiv(a, b))

def share(a, b):
    return _rt.rdiv(a, ((a + b)))

def saturation(x):
    return _rt.rdiv(x, ((1.0 + x)))

def oddsLike(a, b):
    return _rt.rdiv(a, ((a + (2.0 * b))))

def convexCombination(α, x, y):
    return ((α * x) + (((1.0 - α)) * y))

def geometricDecay(r, t):
    return _rt.lpow(((1.0 - r)), t)

def retainedFraction(loss, total):
    return (((1.0 - loss)) * total)

def complement(x):
    return (1.0 - x)

def midpoint(a, b):
    return _rt.rdiv(((a + b)), 2.0)

def complementaryComposition(a, b):
    return (1.0 - (((1.0 - a)) * ((1.0 - b))))

def halfDiffSq(a, b):
    return _rt.rdiv(_rt.lpow(((a - b)), 2.0), 4.0)

def survivalWeightedMix(N, c, x):
    return (_rt.lpow(((1.0 - c)), 2.0) * ((_rt.rdiv(1.0, ((2.0 * N))) + (((1.0 - _rt.rdiv(1.0, ((2.0 * N))))) * x))))

def kronecker(x, y):
    return (1.0 if (x == y) else 0.0)

def antiKronecker(x, y):
    return (0.0 if (x == y) else 1.0)

def overlapProfile(q, x):
    return _rt.rdiv((x * ((1.0 - (q * x)))), ((1.0 - ((q * x) * ((1.0 - x))))))

def scaledSquare(a, b):
    return _rt.rdiv(_rt.lpow(a, 2.0), b)

def ratioOfProduct(a, b, c):
    return _rt.rdiv(a, ((b * c)))

def squaredShare(a, b, c):
    return _rt.rdiv(_rt.lpow(a, 2.0), ((b * c)))

def affineStep(a, b, c):
    return (a + (b * c))

def identifiedWith(x):
    return x

def power(a, n):
    return _rt.lpow(a, n)

def innerSum(f, g):
    return sum((_rt.mul(f[int(i)], g[int(i)])) for i in range(int(len(f))))

def residualAgainst(x, c, b):
    return _rt.sub(x, innerSum(c, b))

def product3(a, b, c):
    return ((a * b) * c)

def pairedEpochCount(k):
    return ((2.0 * k) - 2.0)

def Descent_Core_pairCount(k):
    return _rt.rdiv(((k) * (((k) - 1.0))), 2.0)

def halfLineageRate(k, x):
    return _rt.rdiv(((k) * x), 2.0)

def sum3(a, b, c):
    return ((a + b) + c)

def FinitePrior(n):
    return PMF((Fin(((n + 1.0)))))

def probability(P, i):
    return _rt._proj((P(i)), 'toReal')

def Δ(M, K, h):
    return _rt.rabs(_rt._proj(M, 'raw')(K, h))

def Descent_Decision_CertificateGrading_GradedModulus_zero():
    return (lambda _grade, _step: 0.0)

def liftGarbledRule(channel, δ):
    return (lambda observation: _rt._proj((channel(observation)), 'bind')(δ))

def fairBinaryRule():
    return (lambda _: fairBinaryAction())

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

def heritabilityFractionFromN(n, C):
    return share(n, C)

def logarithmicRiskBenchmark(n):
    return _rt.rdiv(1.0, _rt.rlog(n))

def fixedGradeRiskBenchmark(n, K, c):
    return _rt.lpow(n, ((-(_rt.rdiv(c, K)))))

def logarithmicBenchmarkSampleSize(epsilon):
    return _rt.rexp((_rt.rdiv(1.0, epsilon)))

def fixedGradeBenchmarkSampleSize(epsilon, K, c):
    return _rt.lpow(epsilon, ((-(_rt.rdiv(K, c)))))

def selectionSummaryLogLik(validation, summary):
    return (gaussianProfileLogLik(_rt._proj(validation, 'observedEffectCorrelation'), _rt._proj(summary, 'predictedEffectCorrelation'), _rt._proj(validation, 'effectCorrelationNoise')) + gaussianProfileLogLik(_rt._proj(validation, 'observedSelectedVariance'), _rt._proj(summary, 'predictedSelectedVariance'), _rt._proj(validation, 'selectedVarianceNoise')))

def missedSelectedVariance(validation, summary):
    return _rt.rabs((_rt._proj(validation, 'observedSelectedVariance') - _rt._proj(summary, 'predictedSelectedVariance')))

def selectionModelLRT(validation, nullSummary, altSummary):
    return likelihoodRatioStat((selectionSummaryLogLik(validation, nullSummary)), (selectionSummaryLogLik(validation, altSummary)))

def transportedRidgeParameter(τ, a, r):
    return _rt.rdiv((_rt.lpow(τ, 2.0) * a), ((a + r)))

def robustRidgeCandidate(S, τ, a, r):
    return _rt.rdiv((((a + r)) * _rt.lpow(S, 2.0)), (((((a + r)) * _rt.lpow(S, 2.0)) + (_rt.lpow(τ, 2.0) * a))))

def inflatedRidgeParameter(τ, a, r):
    return (_rt.lpow(τ, 2.0) * ((1.0 + _rt.rdiv(r, a))))

def longMemoryMetric(ε, δ):
    return _rt.rdiv(_rt.lpow(ε, 2.0), _rt.lpow(δ, 3.0))

def longMemoryVariance(ε, δ, n):
    return _rt.rdiv((3.0 * _rt.lpow(δ, 3.0)), ((n * _rt.lpow(ε, 2.0))))

def momentBodyEntropyExponent(α):
    return _rt.rdiv(1.0, α)

def hyperrectangleEntropyExponent(α):
    return _rt.rdiv(2.0, (((2.0 * α) - 1.0)))

def gaussianProfileLogLik(observed, mean, variance):
    return (_rt.rdiv((-(_rt.lpow(((observed - mean)), 2.0))), ((2.0 * variance))) - _rt.rdiv(_rt.rlog((((2.0 * _rt.pi) * variance))), 2.0))

def likelihoodRatioStat(logLNull, logLAlt):
    return ((-2.0) * ((logLNull - logLAlt)))

def ldsrExpectedBetaSq(h2, M, ell_j, N):
    return ((_rt.rdiv(h2, M) * ell_j) + _rt.rdiv(1.0, N))

def ldsrExpectedChi2(N, h2, M, ell_j, a):
    return (((_rt.rdiv((N * h2), M) * ell_j) + (N * a)) + 1.0)

def haplotypeFreqAdmixed(alpha, p_A, q_A, p_B, q_B):
    return (((alpha * p_A) * q_A) + ((((1.0 - alpha)) * p_B) * q_B))

def admixtureLDTwoLocus(alpha, p_A, q_A, p_B, q_B):
    return (haplotypeFreqAdmixed(alpha, p_A, q_A, p_B, q_B) - (convexCombination(alpha, p_A, p_B) * convexCombination(alpha, q_A, q_B)))

def admixtureLDAtGen(alpha, p_A, q_A, p_B, q_B, r, g):
    return (_rt.lpow(((1.0 - r)), g) * admixtureLDTwoLocus(alpha, p_A, q_A, p_B, q_B))

def admixtureLDMagnitude(alpha, p_A, p_B, r, g):
    return (((alpha * ((1.0 - alpha))) * _rt.lpow(((p_A - p_B)), 2.0)) * _rt.lpow(((1.0 - r)), g))

def klBern(p, q):
    return bernoulliKL((unitProbToNNReal(p)), (unitProbToNNReal(q)), (unitProbToNNReal_le_one(p)), (unitProbToNNReal_le_one(q)))

def poly_n(n, x):
    return _rt.lpow(x, n)

def altAlleleCount(*_a):
    if len(_a) < 1:
        return lambda *_b: altAlleleCount(*(_a + _b))
    _e, = _a[:1]
    _t = [0.0, 1.0, 2.0]
    return _t[_rt._ix(_e, 3, 'altAlleleCount')]

def refFreq(h):
    return (1.0 - _rt._proj(h, 'altFreq'))

def genotypeProb(*_a):
    if len(_a) < 2:
        return lambda *_b: genotypeProb(*(_a + _b))
    h, _e = _a[:2]
    _t = [_rt.lpow(refFreq(h), 2.0), ((2.0 * refFreq(h)) * _rt._proj(h, 'altFreq')), _rt.lpow(_rt._proj(h, 'altFreq'), 2.0)]
    return _t[_rt._ix(_e, 3, 'genotypeProb')]

def expectedAltAlleleCount(h):
    return sum(((altAlleleCount(g) * genotypeProb(h, g))) for g in range(int(3)))

def centeredAltAlleleCount(h, g):
    return (altAlleleCount(g) - expectedAltAlleleCount(h))

def genotypeVariance(h):
    return sum(((genotypeProb(h, g) * _rt.lpow((centeredAltAlleleCount(h, g)), 2.0))) for g in range(int(3)))

def genotypeThirdAbsMoment(h):
    return sum(((genotypeProb(h, g) * _rt.lpow(_rt.rabs(centeredAltAlleleCount(h, g)), 3.0))) for g in range(int(3)))

def Descent_Foundations_HWEScoreModel_scoreMean(model):
    return sum(((_rt._proj(model, 'effect')(i) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'expectedAltAlleleCount'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def Descent_Foundations_HWEScoreModel_scoreVariance(model):
    return sum(((_rt.lpow((_rt._proj(model, 'effect')(i)), 2.0) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'genotypeVariance'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def scoreThirdAbsMomentBound(model):
    return sum(((_rt.lpow(_rt.rabs(_rt._proj(model, 'effect')(i)), 3.0) * _rt._proj((_rt._proj(model, 'alleleFreq')(i)), 'genotypeThirdAbsMoment'))) for i in range(int(_rt.sumdim('i', len(_rt._proj(model, 'effect')), len(_rt._proj(model, 'alleleFreq'))))))

def Descent_Foundations_berryEsseenErrorBound(berryEsseenConstant, variance, thirdMomentSum):
    return _rt.rdiv((berryEsseenConstant * thirdMomentSum), ((variance * _rt.rsqrt(variance))))

def Descent_Foundations_HWEScoreModel_berryEsseenErrorBound(model, berryEsseenConstant):
    return Descent_Foundations_berryEsseenErrorBound(berryEsseenConstant, Descent_Foundations_HWEScoreModel_scoreVariance(model), scoreThirdAbsMomentBound(model))

def homoscedastic(sigma2):
    return (lambda _: sigma2)

def latentLiability(s, e):
    return Descent_Core_sum(s, e)

def etaLiabilityThreshold(hN, T, s, x):
    return _rt._proj((noiseMeasureGivenX(hN, x, (diseaseEvent(T, x, s)))), 'toReal')

def variance(E, Z):
    return E(((lambda ω: _rt.lpow((_rt.sub(Z[int(ω)], E(Z))), 2.0))))

def covariance(E, X, Y):
    return E(((lambda ω: _rt.mul((_rt.sub(X[int(ω)], E(X))), (_rt.sub(Y[int(ω)], E(Y)))))))

def expMse(E, Y, S):
    return E(((lambda ω: _rt.lpow((_rt.sub(Y[int(ω)], S[int(ω)])), 2.0))))

def bias(E, Y, S):
    return _rt.sub(E(S), E(Y))

def crossCovVector(E, X, Y):
    return (lambda i: covariance(E, ((lambda ω: X[int(ω)][int(i)])), Y))

def contextCrossCovVector(E, X, h):
    return (lambda j: covariance(E, ((lambda ω: X[int(ω)][int(j)])), h))

def transportedCovariance(w, K, β):
    return sum((sum((_rt.mul(_rt.mul(w[int(j)], K[int(j)][int(l)]), β[int(l)])) for l in range(int(_rt.sumdim('l', len(K[0]), len(β)))))) for j in range(int(_rt.sumdim('j', len(w), len(K)))))

def baselineWeight(aT, l):
    return _rt.rdiv(aT[int(l)], (sum((aT[int(m)]) for m in range(int(len(aT))))))

def transportFactor(aQ, aT, l):
    return _rt.rdiv(aQ[int(l)], aT[int(l)])

def explainableFraction(between, total):
    return ratio(between, total)

def prevalence(c):
    return (_rt._proj(c, 'tp') + _rt._proj(c, 'fn'))

def recallRate(c):
    return _rt.rdiv(_rt._proj(c, 'tp'), ((_rt._proj(c, 'tp') + _rt._proj(c, 'fn'))))

def fpr(c):
    return _rt.rdiv(_rt._proj(c, 'fp'), ((_rt._proj(c, 'fp') + _rt._proj(c, 'tn'))))

def precision(c):
    return _rt.rdiv(_rt._proj(c, 'tp'), ((_rt._proj(c, 'tp') + _rt._proj(c, 'fp'))))

def Hap():
    return Allele

def RefTree():
    return Allele

def Descent_Pangenome_geno(t, h, e):
    return (0.0 if (e == t) else (1.0 if (h == e) else 0.0))

def seqDist(h_1, h_2):
    return (0.0 if (h_1 == h_2) else 1.0)

def piSeq6(sample):
    return (2.0 * sumOver((unorderedPairs(sample)), seqDist))

def piRows6(t, sample):
    return (2.0 * sumOver((unorderedPairs(sample)), (Descent_Pangenome_rowDist(t))))

def thetaW6(t, sample):
    return (4.0 * S(t, sample))

def tajimaNum6(t, sample):
    return ((piSeq6(sample)) - (thetaW6(t, sample)))

def Descent_Pangenome_Gauge_geno(T, w, e):
    return (0.0 if T(e) else w(e))

def totalWalkDist(edges, sample):
    return Descent_Pangenome_Gauge_sum(((lambda w_1: Descent_Pangenome_Gauge_sum(((lambda w_2: walkDist(edges, w_1, w_2))), sample))), sample)

def walkOf(h):
    return (lambda e: (1.0 if (h == e) else 0.0))

def driftVariance(p0, fst):
    return ((p0 * ((1.0 - p0))) * fst)

def twoPopDriftVariance(p0, fst):
    return (2.0 * driftVariance(p0, fst))

def expectedFreqDiffSq(fst, p0):
    return (((2.0 * fst) * p0) * ((1.0 - p0)))

def taggedEffect(causalEffect, tagR):
    return product(causalEffect, tagR)

def gwasHeritability(h2_true, avg_r2_tag):
    return product(h2_true, avg_r2_tag)

def allelicHeterogeneityRetainedSignal(r2_causal, r2_tag, sharedFraction):
    return product3(r2_causal, r2_tag, sharedFraction)

def populationGeneVariance(shared, specific):
    return Descent_Core_sum(shared, specific)

def crossPopulationGeneTransferFraction(shared, targetSpecific):
    return _rt.rdiv(shared, populationGeneVariance(shared, targetSpecific))

def distinctSignalCount(eur, afr, shared):
    return ((eur + afr) - shared)

def geneFlowFstStep(m, Ne, F):
    return ibdFlowStep(Ne, m, F)

def portabilityFromArchitecture(rg, fst, tagging_ratio):
    return ((_rt.lpow(rg, 2.0) * ((1.0 - fst))) * tagging_ratio)

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
    return _rt.rdiv(h2(m), ((1.0 - ((_rt._proj(m, 'r') * h2(m)) * ((1.0 - h2(m)))))))

def pgsR2AM(m, R2_rm):
    return _rt.rdiv(R2_rm, ((1.0 - ((_rt._proj(m, 'r') * h2(m)) * ((1.0 - h2(m)))))))

def amGap(m, R2_rm):
    return (pgsR2AM(m, R2_rm) - R2_rm)

def apparentPortability(d):
    return _rt.rdiv(((1.0 - (_rt._proj(d, 'r_s') * _rt._proj(d, 'h2')))), ((1.0 - (_rt._proj(d, 'r_t') * _rt._proj(d, 'h2')))))

def amCorrectedPortability(port_measured, r_source, r_target, h2):
    return _rt.rdiv((port_measured * ((1.0 - (r_target * h2)))), ((1.0 - (r_source * h2))))

def ibdFst(d, N, sigma_sq):
    return _rt.rdiv(d, ((((4.0 * N) * sigma_sq) + d)))

def Descent_scaledMutationRate(Ne, μ):
    return Descent_Core_scaledMutationRate(Ne, μ)

def Descent_scaledMigrationRate(Ne, m):
    return Descent_Core_scaledMigrationRate(Ne, m)

def fstMutationDriftEquilibrium(θ):
    return fstFromFlow(θ)

def hetDecayFromScaled(Ne, θ):
    return (((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * ((1.0 - _rt.rdiv(θ, ((2.0 * Ne))))))

def fstTransientDecayFromScaled(Ne, θ, bigM):
    return (hetDecayFromScaled(Ne, θ) * ((1.0 - _rt.rdiv(bigM, ((2.0 * Ne))))))

def CausalVec(c):
    return RealVec(c)

def TagVec(t):
    return RealVec(t)

def Descent_HWEPolygenicScoreDGP_scoreMean(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'scoreMean')

def Descent_HWEPolygenicScoreDGP_scoreVariance(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'scoreVariance')

def scoreApproximationError(dgp):
    return _rt._proj(_rt._proj(dgp, 'scoreModel'), 'berryEsseenErrorBound')(_rt._proj(dgp, 'berryEsseenConstant'))

def Descent_SourceTaggedMoments_sigmaTagCausal(mom):
    return (_rt._proj(mom, 'directCausalSource') + _rt._proj(mom, 'proxyTaggingSource'))

def sourceBestLinearWeightsFromLD(mom, betaCausal):
    return _rt._proj(_rt.rinv(_rt._proj(mom, 'sigmaTagSource')), 'mulVec')((_rt._proj(_rt._proj(mom, 'sigmaTagCausal'), 'mulVec')(betaCausal)))

def frobeniusNormSq(A):
    t = float(len(A))
    return sum((sum((_rt.lpow((A[int(i)][int(j)]), 2.0)) for j in range(int(len(A))))) for i in range(int(len(A))))

def r2FromMSE(mse, varY):
    return proportionalReduction(mse, varY)

def explainedR2FromTransportMoments(scoreOutcomeCov, scoreVariance, outcomeVariance):
    return squaredShare(scoreOutcomeCov, scoreVariance, outcomeVariance)

def ldWitnessSourceWeights():
    return sourceBestLinearWeightsFromLD(ldWitnessSourceMoments(), ldWitnessBeta())

def taggingMismatchScale(recombRate, arraySparsity):
    return product(recombRate, arraySparsity)

def demographicCovarianceGapLowerBound(fstSource, fstTarget, recombRate, arraySparsity, kappa):
    return ((kappa * taggingMismatchScale(recombRate, arraySparsity)) * ((fstTarget - fstSource)))

def discreteRecombinationSurvival(recombRate, tmrca):
    return geometricDecay(recombRate, tmrca)

def twoLocusIBDCovariance(ibdWeight, recombRate, tmrca):
    return (ibdWeight * discreteRecombinationSurvival(recombRate, tmrca))

def twoLocusCoalescentCovarianceMatrix(ht, ibdWeight, recombRate, tmrca):
    return (lambda i, j: (twoLocusIBDCovariance(ibdWeight, recombRate, tmrca) if ((i == twoLocusIdx0(ht)) and (j == twoLocusIdx1(ht))) else (twoLocusIBDCovariance(ibdWeight, recombRate, tmrca) if ((i == twoLocusIdx1(ht)) and (j == twoLocusIdx0(ht))) else (1.0 if (i == j) else 0.0))))

def dgpInteractiveBias(k, β_int):
    return {'jointMeasure': stdNormalProdMeasure(k), '__uninhabited__': {'trueExpectation': '∑ over an unannotated index whose index is never applied to a local value: there is nothing in the body to read a dimension from'}}

def dgpAdditiveBias(k, β_env):
    return {'jointMeasure': stdNormalProdMeasure(k), '__uninhabited__': {'trueExpectation': '∑ over an unannotated index whose index is never applied to a local value: there is nothing in the body to read a dimension from'}}

def optimalSlopeLinearNoise(sigma_g_sq, base_error, slope_error, c):
    return _rt.rdiv(sigma_g_sq, (((sigma_g_sq + base_error) + (slope_error * c))))

def totalVariance(arch, c):
    return _rt.add(_rt._proj(arch, 'V_genic')(c), _rt._proj(arch, 'V_cov')(c))

def selectedTotalVariance(arch, c):
    return _rt.add(totalVariance(arch, c), _rt._proj(arch, 'selection_effect')(c))

def optimalSlopeFromVariance(arch, c):
    return _rt.rdiv((totalVariance(arch, c)), (_rt._proj(arch, 'V_genic')(c)))

def prevalenceDGP_trueExpectation(pdgp, p, c):
    return _rt.add(_rt._proj(pdgp, 'prevalence')(c), _rt.mul(_rt._proj(pdgp, 'pgs_effect'), p))

def decaySlope(mech, c):
    return _rt._proj(mech, 'tagging_efficiency')((_rt._proj(mech, 'distance')(c)))

def measureBias(μ, Y, S):
    return _rt.sub(measureMean(μ, S), measureMean(μ, Y))

def signalVariance(dgp, signal):
    return var(dgp, signal)

def trueExp(hdgp):
    return (lambda p, c: ((_rt._proj(hdgp, 'alpha')(c) * p) + _rt._proj(hdgp, 'baseline')(c)))

def tau(p):
    return _rt.rdiv(_rt._proj(p, 't_div'), ((2.0 * _rt._proj(p, 'Ne'))))

def Descent_EvolutionaryParameters_theta(p):
    return Descent_scaledMutationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mu'))

def Descent_EvolutionaryParameters_bigM(p):
    return Descent_scaledMigrationRate(_rt._proj(p, 'Ne'), _rt._proj(p, 'mig'))

def fstDriftMigrationManyDemes(p):
    return _rt.rdiv(1.0, ((1.0 + Descent_EvolutionaryParameters_bigM(p))))

def fstDriftFlowStep(p, F):
    return ((F + _rt.rdiv(((1.0 - F)), ((2.0 * _rt._proj(p, 'Ne'))))) - ((2.0 * ((_rt._proj(p, 'mig') + _rt._proj(p, 'mu')))) * F))

def fstDemeCorrectedFlowStep(p, F):
    return ((F + _rt.rdiv(((1.0 - F)), ((2.0 * _rt._proj(p, 'Ne'))))) - ((2.0 * (((2.0 * _rt._proj(p, 'mig')) + _rt._proj(p, 'mu')))) * F))

def Descent_fstEquilibrium(p):
    return fstFromFlow(((Descent_EvolutionaryParameters_theta(p) + (2.0 * Descent_EvolutionaryParameters_bigM(p)))))

def sharedLDRetention(p):
    return _rt.lpow(((1.0 - _rt._proj(p, 'recomb'))), ((2.0 * _rt._proj(p, 't_div'))))

def mutationLDErosion(p):
    return _rt.rexp((((-Descent_EvolutionaryParameters_theta(p)) * tau(p))))

def migrationLDBoost(p):
    return (1.0 + _rt.rdiv((Descent_EvolutionaryParameters_bigM(p) * tau(p)), ((1.0 + Descent_EvolutionaryParameters_bigM(p)))))

def r2FromSignalVariance(vSignal, vNoise):
    return share(vSignal, vNoise)

def equalVarianceGaussianAUCFromSignalVariance(vSignal, vNoise):
    return ((1.0 if (0.0 < vSignal) else Phi(0.0)) if (vNoise == 0.0) else Phi((_rt.rsqrt((_rt.rdiv(vSignal, ((2.0 * vNoise))))))))

def calibratedBrier(π, r2):
    return ((π * ((1.0 - π))) * ((1.0 - r2)))

def calibratedBrierFromVariances(π, vSignal, vResidual):
    return ((π * ((1.0 - π))) * ((1.0 - _rt.rdiv(vSignal, ((vSignal + vResidual))))))

def Descent_TransportedMetrics_IrreducibleTargetPenalty_total(penalty):
    return (((_rt._proj(penalty, 'brokenTagging') + _rt._proj(penalty, 'ancestrySpecificLD')) + _rt._proj(penalty, 'sourceSpecificOverfit')) + _rt._proj(penalty, 'novelUntaggablePhenotype'))

def profileFromSignalVarianceWithPenalty(π, vNoise, vSignal, penalty):
    return profileFromSignalVariance(π, ((vNoise + Descent_TransportedMetrics_IrreducibleTargetPenalty_total(penalty))), vSignal)

def metricProfileFromTargetSignalWithPenalty(m, vSignalTarget, penalty):
    return profileFromSignalVarianceWithPenalty(_rt._proj(m, 'prevalence'), _rt._proj(m, 'V_E'), vSignalTarget, penalty)

def alleleFreqDivergenceRate(Ne, _mu, _m_rate):
    return _rt.rdiv(1.0, ((2.0 * Ne)))

def ldBreakageRate(r):
    return (2.0 * r)

def contrastSpikeLevel(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), ((meanAlleleFreq(p_1, p_2) * ((1.0 - meanAlleleFreq(p_1, p_2))))))

def demoSteppingStoneFst(d, Ne, m, σ_sq):
    return _rt.rdiv(d, ((d + (((4.0 * Ne) * m) * σ_sq))))

def steppingStoneFstQuadratic(d, Ne, m, σ_sq):
    return _rt.rdiv(d, ((d + (((4.0 * Ne) * _rt.lpow(σ_sq, 2.0)) * _rt.lpow(m, 2.0)))))

def steppingStoneDiffusionTimescale(d, σ_sq, m):
    return _rt.rdiv(d, (((2.0 * σ_sq) * m)))

def steppingStoneMeetingTimeOnLattice(d, demeCount, σ_sq, m):
    return _rt.rdiv((d * ((demeCount - d))), (((2.0 * σ_sq) * m)))

def admixedFst(α, fst_AB):
    return (_rt.lpow(((1.0 - α)), 2.0) * fst_AB)

def admixedFstExact(α, fst_AB, hetRatio):
    return _rt.rdiv((_rt.lpow(((1.0 - α)), 2.0) * fst_AB), hetRatio)

def admixedAlleleFreq(α, p_A, p_B):
    return convexCombination(α, p_A, p_B)

def introgressionVariants(N_0, introgressionRate, t):
    return (N_0 * ((1.0 - _rt.rexp((((-introgressionRate) * t))))))

def founderHeterozygosityLoss(k, t):
    return (1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * (k)))))), t))

def cumulativeDrift(Ne):
    return sum((_rt.rdiv(1.0, (_rt.mul(2.0, Ne[int(i)])))) for i in range(int(len(Ne))))

def heterozygosityLossVariableNe(Ne):
    return _rt.sub(1.0, _rt.rexp((_rt.neg((cumulativeDrift(Ne))))))

def driftLDCreationRate(Ne):
    return driftRatePerGen(Ne)

def bottleneckExcessLD(Ne_b, Ne_stable, c, t_b):
    return (driftLDTrajectory(Ne_b, c, (driftLDEquilibrium(Ne_stable, c)), t_b) - driftLDEquilibrium(Ne_stable, c))

def measuredLoss(M, t):
    return (1.0 - _rt.rdiv(_rt._proj(M, 'het')(t), _rt._proj(M, 'het')(0.0)))

def lossOfRetention(r):
    return complement(r)

def targetHetOfRetention(H_0, r):
    return product(H_0, r)

def targetPgsVarOfRetention(V_A, r):
    return product(V_A, r)

def clusterCrossCheck(r):
    return (targetHetOfRetention(1.0, r) == (1.0 * ((1.0 - lossOfRetention(r)))))

def benchmarkRatio(fstS, fstT):
    return _rt.rdiv(((1.0 - fstT)), ((1.0 - fstS)))

def benchmarkRatioSquared(fstS, fstT):
    return _rt.lpow((_rt.rdiv(((1.0 - fstT)), ((1.0 - fstS)))), 2.0)

def diagonalDesign(g):
    return (lambda x: g(x, x))

def fisherAverageEffect(a, d, p):
    return (a + (d * ((1.0 - (2.0 * p)))))

def pairwiseModel(beta1, beta2, beta12, g1, g2):
    return (((beta1 * g1) + (beta2 * g2)) + ((beta12 * g1) * g2))

def epistaticVariance(beta12, p1, p2):
    return ((_rt.lpow(beta12, 2.0) * (((2.0 * p1) * ((1.0 - p1))))) * (((2.0 * p2) * ((1.0 - p2)))))

def dominanceVariance(p, d):
    return sum((_rt.lpow((_rt.mul(_rt.mul(_rt.mul(2.0, p[int(i)]), (_rt.sub(1.0, p[int(i)]))), d[int(i)])), 2.0)) for i in range(int(len(p))))

def epochSpectrumCoordinateCount(K):
    return ((2.0 * K) - 3.0)

def epochLineageSampleSize(K):
    return pairedEpochCount(K)

def fixedEpochInverseExponent(K):
    return _rt.rinv((epochSpectrumCoordinateCount(K)))

def spectrumPrecisionMultiplier(K, factor):
    return _rt.lpow(factor, epochSpectrumCoordinateCount(K))

def independentSampleMultiplier(K, factor):
    return _rt.lpow(factor, ((2.0 * epochSpectrumCoordinateCount(K))))

def canonicalGenomeMultiplierForEpochCoordinates(kappa, K):
    return _rt.rexp(((kappa * epochSpectrumCoordinateCount(K))))

def fixedEpochSampleRateExponent(K):
    return _rt.rinv(((2.0 * epochSpectrumCoordinateCount(K))))

def collisionHistoryDistance(scale, resolution):
    return product(scale, resolution)

def collisionSpectrumDiscrepancy(order, scale, resolution):
    return (_rt.lpow(scale, order) * alternatingBinomialResponse(order, ((1.0 - resolution))))

def effectiveGeneticEffect(β_G, β_GxE, E_mean):
    return (β_G + (β_GxE * E_mean))

def linearNormOfReaction(a, b, E):
    return affineStep(a, b, E)

def cohortShift(G, gamma, eta, i):
    return ((gamma * _rt._proj(G, 'geneticGradient')(i)) + (eta * _rt._proj(G, 'environmentalGradient')(i)))

def cohortShiftVector(G, parameters):
    return (lambda i: cohortShift(G, _rt._proj(parameters, '1'), _rt._proj(parameters, '2'), i))

def shift(D, i):
    return cohortShift(_rt._proj(D, 'gradients'), _rt._proj(D, 'gamma'), _rt._proj(D, 'eta'), i)

def discoveryNCP(n, β, maf_causal, ld):
    return (((n * _rt.lpow(β, 2.0)) * _rt.lpow(ld, 2.0)) * genotypeVarianceHWE(maf_causal))

def gwasDiscovered(n, β, maf_causal, ld, z):
    return (_rt.lpow(z, 2.0) <= discoveryNCP(n, β, maf_causal, ld))

def taggedScoreEstimationRisk(targetTagVariance, estimatorMSE):
    return innerSum(targetTagVariance, estimatorMSE)

def expectedLinearEffectEstimate(β_true, meanEstimationError):
    return (β_true + meanEstimationError)

def olsEffectEstimationVariance(σ2, varX, n):
    return _rt.rdiv(σ2, ((n * varX)))

def perCausalLocusSignal(h2, k):
    return ratio(h2, k)

def geneticCorrelation(cov_g, vg_1, vg_2):
    return _rt.rdiv(cov_g, _rt.rsqrt(((vg_1 * vg_2))))

def multiTraitEffectiveSampleSize(n_1, n_2, rg, priorVariance):
    return (n_1 + _rt.rdiv(_rt.lpow(rg, 2.0), (((((1.0 - _rt.lpow(rg, 2.0))) * priorVariance) + _rt.rdiv(1.0, n_2)))))

def multiTraitDiscoveryNCP(n_1, n_2, rg, priorVariance, β, maf, ld):
    return discoveryNCP((multiTraitEffectiveSampleSize(n_1, n_2, rg, priorVariance)), β, maf, ld)

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

def uniformOccupancyDistinctHaplotypes(k, n):
    return (_rt.lpow((2.0), k) * ((1.0 - _rt.lpow(((1.0 - _rt.rdiv(1.0, (_rt.lpow((2.0), k))))), n))))

def haplotypeHomozygosity(freq):
    return sum((_rt.lpow(freq[int(i)], 2.0)) for i in range(int(len(freq))))

def effectiveHaplotypeNumber(freq):
    return _rt.rdiv(1.0, haplotypeHomozygosity(freq))

def averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans):
    return convexCombination(freq_cis, interaction_cis, interaction_trans)

def dosagePhaseMisspecificationError(freq_cis, interaction_cis, interaction_trans):
    return ((freq_cis * _rt.lpow(((interaction_cis - averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans))), 2.0)) + (((1.0 - freq_cis)) * _rt.lpow(((interaction_trans - averagePhaseInteraction(freq_cis, interaction_cis, interaction_trans))), 2.0)))

def haplotypePhasePredictionError(freq_cis, switch_err, pred_cis, pred_trans, interaction_cis, interaction_trans):
    return ((freq_cis * (((((1.0 - switch_err)) * _rt.lpow(((interaction_cis - pred_cis)), 2.0)) + (switch_err * _rt.lpow(((interaction_cis - pred_trans)), 2.0))))) + (((1.0 - freq_cis)) * (((((1.0 - switch_err)) * _rt.lpow(((interaction_trans - pred_trans)), 2.0)) + (switch_err * _rt.lpow(((interaction_trans - pred_cis)), 2.0))))))

def dosageTransportBias(freq_cis_source, freq_cis_target, interaction_cis, interaction_trans):
    return _rt.rabs((averagePhaseInteraction(freq_cis_target, interaction_cis, interaction_trans) - averagePhaseInteraction(freq_cis_source, interaction_cis, interaction_trans)))

def haplotypeTransportBias(freq_cis_target, pred_cis, pred_trans, interaction_cis, interaction_trans):
    return _rt.rabs((averagePhaseInteraction(freq_cis_target, pred_cis, pred_trans) - averagePhaseInteraction(freq_cis_target, interaction_cis, interaction_trans)))

def haplotypeEffectVarianceOLS(σ2, n, freq):
    return _rt.rdiv(σ2, (((n * freq) * ((1.0 - freq)))))

def phaseAttenuation(s):
    return _rt.lpow(((1.0 - (2.0 * s))), 2.0)

def ancestrySpecificEffect(beta_pop1, beta_pop2, alpha):
    return convexCombination(alpha, beta_pop1, beta_pop2)

def globalAncestryAveragedEffect(beta_1, beta_2, alpha):
    return ancestrySpecificEffect(beta_1, beta_2, alpha)

def localAncestryMisspecification(beta_1, beta_2, alpha):
    return ((alpha * _rt.lpow(((beta_1 - globalAncestryAveragedEffect(beta_1, beta_2, alpha))), 2.0)) + (((1.0 - alpha)) * _rt.lpow(((beta_2 - globalAncestryAveragedEffect(beta_1, beta_2, alpha))), 2.0)))

def expectedTractLength(g, admixtureFraction):
    return _rt.rdiv(1.0, ((g * ((1.0 - admixtureFraction)))))

def neutralDriftR2Ratio(V_A, V_E, fst):
    return _rt.rdiv(presentDayR2(V_A, V_E, fst), presentDayR2(V_A, V_E, 0.0))

def taggedDriftR2RatioCorrected(V_A, V_E, fst, shared_ld):
    return _rt.rdiv(((((1.0 - fst)) * shared_ld) * ((V_A + V_E))), (((((1.0 - fst)) * V_A) + V_E)))

def ldRetentionPerGen(r, Ne):
    return (((1.0 - r)) * ((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))))

def ldAfterGenerations(D_0, r, Ne, t):
    return (D_0 * _rt.lpow((ldRetentionPerGen(r, Ne)), t))

def tagR2(D_sq, var_tag, var_causal):
    return ratioOfProduct(D_sq, var_tag, var_causal)

def admixtureLD(α, Δp_1, Δp_2):
    return (((α * ((1.0 - α))) * Δp_1) * Δp_2)

def driftLDStep(Ne, c, Q):
    return survivalWeightedMix(Ne, c, Q)

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

def driftRatePerGen(Ne):
    return alleleFreqDivergenceRate(Ne, 0.0, 0.0)

def ldHalfLife(r, Ne):
    return _rt.rdiv(_rt.rlog(2.0), ((-_rt.rlog((ldRetentionPerGen(r, Ne))))))

def ldRetainedFraction(r, Ne, t):
    return _rt.lpow((ldRetentionPerGen(r, Ne)), t)

def ldRecurrence(r, D_0, t):
    _prev = D_0
    for _ in range(int(t)):
        _prev = (((1.0 - r)) * _prev)
    return _prev

def qst(V_between, V_within):
    return oddsLike(V_between, V_within)

def pgsDriftVariance_one_pop(V_A, fst):
    return Var_Delta_Mu(V_A, fst)

def pgsDriftVarianceFromLoci(fst, β):
    n = float(len(β))
    return sum((_rt.mul(fst, _rt.lpow(β[int(i)], 2.0))) for i in range(int(len(β))))

def pgsDiffVariance_two_pop(V_A, fst):
    return (2.0 * pgsDriftVariance_one_pop(V_A, fst))

def expectedPGSDiffVariance(V_A, fst):
    return ((V_A * 4.0) * fst)

def effectCorrelationStabilizingDriftSelection(d, s, N):
    return (1.0 - _rt.rdiv(d, ((1.0 + (s * N)))))

def effectCorrelationFluctuating(d, f, N):
    return _rt.rmax(((-1.0)), ((1.0 - (d * ((1.0 + (f * N)))))))

def expectedSquaredEffect(h2, M):
    return ratio(h2, M)

def spikeAndSlabVariance(pi, sigma_sq_large, sigma_sq_small):
    return convexCombination(pi, sigma_sq_large, sigma_sq_small)

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

def architectureRadius(P):
    return sum((sum((_rt.rabs(_rt._proj(P, 'architecture')(i, j))) for j in range(int(_rt.sumdim('j', len(_rt._proj(P, 'architecture')[0])))))) for i in range(int(_rt.sumdim('i', len(_rt._proj(P, 'architecture'))))))

def effects(P):
    return boundedEffectCarrier(q, architectureRadius(P))

def architectureMoment(P, r, i):
    return sum((_rt.lpow((_rt._proj(P, 'architecture')(i, j)), ((r + 1.0)))) for j in range(int(_rt.sumdim('j', len(_rt._proj(P, 'architecture')[0])))))

def finiteProblem(P):
    return _rt._proj(_rt._proj(P, 'mixtureExperiment'), 'certificateProblem')

def Descent_MeanAbsoluteEffectCertificateProblem_atomCertificationGap(P, K, h):
    return _rt.rdiv(_rt._proj(_rt._proj(P, 'finiteProblem'), 'modulus')(0.0, h), _rt._proj(_rt._proj(P, 'finiteProblem'), 'atomModulus')(K, h))

def logCoveringAtExponent(t, e):
    return _rt.lpow(t, e)

def heritabilityEnrichment(h2_cat, M_cat, h2_total, M_total):
    return _rt.rdiv((_rt.rdiv(h2_cat, M_cat)), (_rt.rdiv(h2_total, M_total)))

def predictedPortability(model):
    return portabilityScore(model)

def weightedRetentionUpperBound(model, retentionUpper):
    return _rt.rdiv((sum((_rt.mul(retentionUpper[int(j)], _rt._proj(model, 'sourceSquaredEffect')(j))) for j in range(int(len(retentionUpper))))), sourceEffectMass(model))

def rgFstWeightedUpperBound(model, rgUpper, fstLower):
    return weightedRetentionUpperBound(model, ((lambda j: _rt.mul(_rt.lpow((rgUpper[int(j)]), 2.0), (_rt.sub(1.0, fstLower[int(j)]))))))

def neiFst(H_T, H_S):
    return _rt.rdiv(((H_T - H_S)), H_T)

def neiGstFromFrequencies(p_1, p_2):
    p_bar = _rt.rdiv(((p_1 + p_2)), 2.0)
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), (((4.0 * p_bar) * ((1.0 - p_bar)))))

def expectedHeterozygosity(θ):
    return _rt.rdiv(θ, ((1.0 + θ)))

def coalFst(t, Ne):
    return oddsLike(t, Ne)

def continentIslandStepSelectionFirst(s, m, p):
    return (((1.0 - m)) * (_rt.rdiv((p * ((1.0 + s))), ((1.0 + (s * p))))))

def continentIslandStepMigrationFirst(s, m, p):
    return _rt.rdiv((((((1.0 - m)) * p)) * ((1.0 + s))), ((1.0 + (s * ((((1.0 - m)) * p))))))

def selectionMigrationEquilibrium(s, m):
    return _rt.rmax(0.0, (_rt.rdiv((((s - m) - (m * s))), s)))

def selectionMigrationEquilibriumMigrationFirst(s, m):
    return _rt.rmax(0.0, (_rt.rdiv((((s - m) - (m * s))), ((s * ((1.0 - m)))))))

def wrightFIT(f_IS, f_ST):
    return complementaryComposition(f_IS, f_ST)

def heterozygosityLossFromDrift(t, Ne):
    return heterozygosityLoss(Ne, t)

def scaledIdentityStep(scaledRate, F):
    return (1.0 - (scaledRate * F))

def fstMutationDriftTransient(θ, t, Ne):
    return (fstMutationDriftEquilibrium(θ) * ((1.0 - _rt.rexp((_rt.rdiv(((-((1.0 + θ))) * t), ((2.0 * Ne))))))))

def expectedNewMutations(θ, t):
    return (_rt.rdiv(θ, 2.0) * t)

def Descent_islandDemeCorrection(d):
    return Descent_Core_islandDemeCorrection(d)

def islandFstFiniteDemes(Ne, m, d):
    return _rt.rdiv(1.0, ((1.0 + (((4.0 * Ne) * m) * Descent_islandDemeCorrection(d)))))

def fstMigrationMutationEquilibriumManyDemes(Ne, m, μ):
    return fstFromFlow(((((4.0 * Ne) * m) + ((4.0 * Ne) * μ))))

def fstIslandEquilibriumFiniteDemes(Ne, m, μ, nDemes):
    return fstFromFlow((((((4.0 * Ne) * m) * Descent_islandDemeCorrection(nDemes)) + ((4.0 * Ne) * μ))))

def steppingStoneCharacteristicLength(m, σ_sq, μ):
    return _rt.rsqrt((_rt.rdiv((m * σ_sq), ((2.0 * μ)))))

def alleleFreqAfterMigration(p_0, p_c, m, t):
    return (p_c + (((p_0 - p_c)) * _rt.lpow(((1.0 - m)), t)))

def ldCorrelationMigrationAnsatz(M):
    return _rt.rdiv(_rt.lpow(M, 2.0), _rt.lpow(((1.0 + M)), 2.0))

def Descent_hetRecurrence(Ne, H_0):
    return Descent_Core_hetRecurrence(Ne, H_0)

def heterozygosityLossDerived(Ne, t):
    return heterozygosityLoss(Ne, t)

def hetMutationDriftRecurrence(Ne, mu, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = ((((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))) * _prev) + ((2.0 * mu) * ((1.0 - _prev))))
    return _prev

def Descent_hetDecayFactor(Ne, θ):
    return hetDecayFromScaled(Ne, θ)

def hetMutationRecurrence(lam, Hstar, H_0, t):
    _prev = H_0
    for _ in range(int(t)):
        _prev = ((lam * _prev) + (((1.0 - lam)) * Hstar))
    return _prev

def fstFromHetRatio(H, H_0):
    return proportionalReduction(H, H_0)

def fstMutationDriftTransientDiscrete(θ, Ne, t):
    return (fstMutationDriftEquilibrium(θ) * ((1.0 - _rt.lpow(Descent_hetDecayFactor(Ne, θ), t))))

def equilibriumEffectVariance(v_mutation, s):
    return ratio(v_mutation, s)

def effectVarianceRecurrence(V, v_mut, s):
    return ((((1.0 - s)) * V) + v_mut)

def effectCorrelationStabilizing(Ns):
    return (1.0 - _rt.rdiv(1.0, ((2.0 * Ns))))

def polygenicAveragingVariance(architectureVariance, locusCount):
    return ratio(architectureVariance, locusCount)

def equalPerLocusHeritability(locusCount, totalHeritability):
    return _rt.rdiv(totalHeritability, locusCount)

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
    return sum((_rt.mul(_rt.mul(β[int(i)], 2.0), Δp[int(i)])) for i in range(int(len(β))))

def gwasNCP(n, β, p):
    return ncp((effectiveFisherInformation(n, p, 1.0)), β)

def selectionPortabilityTimescale(selectionCoefficient):
    return driftLDCreationRate(selectionCoefficient)

def pleiotropicTargetR2(sourceR2, sharedFraction, turnover):
    return (sourceR2 * ((1.0 - (sharedFraction * turnover))))

def serialFounderJoinTime(T0, splitStep, D, k):
    return (0.0 if (k == 0.0) else (T0 + (splitStep * (((D) - 2.0)))))

def serialFounderWithinTime(N, Nanc, tAnc):
    return (((2.0 * N) * ((1.0 - _rt.rexp((_rt.rdiv((-tAnc), ((2.0 * N)))))))) + (_rt.rexp((_rt.rdiv((-tAnc), ((2.0 * N))))) * ((2.0 * Nanc))))

def serialFounderCeilingFst(N, Nanc, tAnc, τ):
    return _rt.rdiv(τ, ((serialFounderWithinTime(N, Nanc, tAnc) + τ)))

def gaussianKurtosisMaf():
    return _rt.rdiv(((3.0 - _rt.rsqrt(3.0))), 6.0)

def reModel(design, model):
    _b = dict(design)
    _b.update({'model': model})
    return _b

def moment(spectrum, k):
    return sum(((_rt._proj(spectrum, 'weight')(j) * sum(((_rt._proj((_rt._proj(spectrum, 'model')(j)), 'genotypeProb')(g) * _rt.lpow(_rt._proj((_rt._proj(spectrum, 'model')(j)), 'standardizedGenotype')(g), k))) for g in range(int(3))))) for j in range(int(_rt.sumdim('j', len(_rt._proj(spectrum, 'weight')), len(_rt._proj(spectrum, 'model'))))))

def centeredSquareThirdMoment(spectrum):
    return ((moment(spectrum, 6.0) - (3.0 * moment(spectrum, 4.0))) + 2.0)

def fourthMomentDispersion(spectrum):
    return ((sum(((_rt._proj(spectrum, 'weight')(j) * _rt.lpow((_rt.rdiv(1.0, _rt._proj((_rt._proj(spectrum, 'model')(j)), 'genotypeVariance'))), 2.0))) for j in range(int(_rt.sumdim('j', len(_rt._proj(spectrum, 'weight')), len(_rt._proj(spectrum, 'model'))))))) - _rt.lpow((moment(spectrum, 4.0)), 2.0))

def squaringScaleSq(fourthMoment):
    return (fourthMoment - 1.0)

def nextFloorFourthMoment(m2, m4, m6, m8):
    return _rt.rdiv((((((m8 - (4.0 * m6)) + (6.0 * m4)) - (4.0 * m2)) + 1.0)), _rt.lpow((((m4 - (2.0 * m2)) + 1.0)), 2.0))

def nextFloorFourthMomentOfY(secondY, fourthY):
    return _rt.rdiv(fourthY, _rt.lpow(secondY, 2.0))

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

def narrowSenseH2(V_A, V_D, V_I, V_E):
    return _rt.rdiv(V_A, ((((V_A + V_D) + V_I) + V_E)))

def snpH2(V_A_tagged, V_P):
    return ratio(V_A_tagged, V_P)

def additiveVariance(p, α):
    return sum((_rt.mul(_rt.mul(_rt.mul(2.0, p[int(i)]), (_rt.sub(1.0, p[int(i)]))), _rt.lpow((α[int(i)]), 2.0))) for i in range(int(len(p))))

def liabilityScaleH2(h2_observed, prevalence, z_height):
    return _rt.rdiv(((h2_observed * prevalence) * ((1.0 - prevalence))), _rt.lpow(z_height, 2.0))

def ancestryRecalibratedSlope(bSource, rho, alpha):
    return _rt.rdiv((rho * ((bSource * alpha))), _rt.lpow(alpha, 2.0))

def ancestryRecalibratedR2(r2Source, rhoSq):
    return product(r2Source, rhoSq)

def effectTurnoverR2Loss(r2Source, rhoSq):
    return retainedFraction(rhoSq, r2Source)

def cubicSplineApproximationScale(h):
    return _rt.lpow(h, 4.0)

def splineCalibrationMSE(bias, variance):
    return (_rt.lpow(bias, 2.0) + variance)

def explainedVarianceFraction(varSignal, varNoise):
    return share(varSignal, varNoise)

def transferredEstimatorMSE(σ_sq, bias_sq, nTarget):
    return (_rt.rdiv(σ_sq, nTarget) + bias_sq)

def targetOnlyEstimatorMSE(σ_sq, σ_extra_sq, nTarget):
    return _rt.rdiv(((σ_sq + σ_extra_sq)), nTarget)

def prevalenceScaledR2(h2, prevalence):
    return _rt.rdiv((h2 * _rt.lpow(standardNormalPdf((liabilityThreshold(prevalence))), 2.0)), ((prevalence * ((1.0 - prevalence)))))

def epistaticVariancePairwise(γ, p_1, p_2):
    return ((_rt.lpow(γ, 2.0) * (((2.0 * p_1) * ((1.0 - p_1))))) * (((2.0 * p_2) * ((1.0 - p_2)))))

def fisherInformation(n, v):
    return product(n, v)

def genotypeVarianceHWE(p):
    return Descent_Core_hweHeterozygosity(p)

def effectiveFisherInformation(n, p, r2_ld):
    return (fisherInformation(n, (genotypeVarianceHWE(p))) * r2_ld)

def standardErrorSq(n, p, r2_ld):
    return _rt.rdiv(1.0, effectiveFisherInformation(n, p, r2_ld))

def ncp(n_eff, β):
    return (n_eff * _rt.lpow(β, 2.0))

def Descent_hweHeterozygosity(p):
    return Descent_Core_hweHeterozygosity(p)

def portableFraction(r2_causal, r2_total):
    return ratio(r2_causal, r2_total)

def proportionalAllocation(pop_size, total_n, total_pop):
    return (total_n * (_rt.rdiv(pop_size, total_pop)))

def posteriorPrecision(m):
    return (_rt.rdiv(1.0, _rt._proj(m, 'prior_var')) + _rt._proj(m, 'data_precision'))

def posteriorVariance(m):
    return _rt.rdiv(1.0, posteriorPrecision(m))

def Descent_BayesianLinearModel_posteriorMean(m, y):
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
    return (π * _rt.lpow(σ_slab, 2.0))

def misspecExcessRisk(π, σ_β_sq):
    return ((π * ((1.0 - π))) * σ_β_sq)

def posteriorPredictiveVariance(residual_var, estimation_var):
    return Descent_Core_sum(residual_var, estimation_var)

def multiAncestryEffectiveN(n_target, rg, n_other, priorVariance):
    return (n_target + _rt.rdiv(_rt.lpow(rg, 2.0), (((((1.0 - _rt.lpow(rg, 2.0))) * priorVariance) + _rt.rdiv(1.0, n_other)))))

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
    return Descent_Core_sum(event_nri, nonevent_nri)

def sensFromR2(m, r2, T_p):
    return liabilitySensitivity(Phi, m, r2, T_p)

def specFromR2(m, r2, T_p, μ_control):
    return liabilitySpecificity(Phi, m, r2, T_p, μ_control)

def ppv(prev, tpr, fpr):
    return _rt.rdiv((prev * tpr), (((prev * tpr) + (((1.0 - prev)) * fpr))))

def proportionCorrectlyClassified(sensitivity, specificity, prevalence):
    return ((sensitivity * prevalence) + (specificity * ((1.0 - prevalence))))

def numberNeededToScreen(sens, π, _hsens, _hπ):
    return _rt.rdiv(1.0, ((sens * π)))

def populationAttributableFraction(p_high, rr):
    return (p_high * ((1.0 - _rt.rdiv(1.0, rr))))

def Descent_posteriorMean(posterior, conditional, x):
    return sum((_rt.mul(posterior[int(x)][int(t)], conditional[int(t)][int(x)])) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(conditional)))))

def posteriorDrift(posterior, conditional, t, x):
    return _rt.sub(conditional[int(t)][int(x)], Descent_posteriorMean(posterior, conditional, x))

def indexWiseCalibrationEnergy(covariateWeight, posterior, conditional, predictor):
    return sum((_rt.mul(covariateWeight[int(x)], sum((_rt.mul(posterior[int(x)][int(t)], _rt.lpow((_rt.sub(conditional[int(t)][int(x)], predictor[int(x)])), 2.0))) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(conditional))))))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(posterior), len(conditional[0]), len(predictor)))))

def aggregateCalibrationEnergy(covariateWeight, posterior, conditional, predictor):
    return sum((_rt.mul(covariateWeight[int(x)], _rt.lpow((_rt.sub(Descent_posteriorMean(posterior, conditional, x), predictor[int(x)])), 2.0))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(predictor)))))

def pairwiseCalibrationDriftEnergy(covariateWeight, posterior, conditional):
    return sum((_rt.mul(covariateWeight[int(x)], posteriorPairwiseDriftEnergy(posterior, conditional, x))) for x in range(int(_rt.sumdim('x', len(covariateWeight)))))

def balancedBinaryWeight(_):
    return _rt.rdiv(1.0, 2.0)

def twoIndexPosterior(q, x, t):
    return (q[int(x)] if t else _rt.sub(1.0, q[int(x)]))

def thresholdDecision(cutoff, risk):
    return (true if (cutoff <= risk) else false)

def aggregateCalibrationMoment(covariateWeight, posterior, conditional, predictor, kernel):
    return sum((_rt.mul(_rt.mul(covariateWeight[int(x)], (_rt.sub(Descent_posteriorMean(posterior, conditional, x), predictor[int(x)]))), kernel[int(x)])) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(predictor), len(kernel)))))

def indexWiseCalibrationMoment(covariateWeight, posterior, conditional, predictor, kernel):
    return sum((sum((_rt.mul(_rt.mul(_rt.mul(covariateWeight[int(x)], posterior[int(x)][int(t)]), (_rt.sub(conditional[int(t)][int(x)], predictor[int(x)]))), kernel[int(x)])) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(posterior), len(conditional[0]), len(predictor), len(kernel)))))) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(conditional)))))

def IsCellBalanced(weight, value, cell, representative):
    return all((((sum(((_rt.mul(weight[int(a)], (_rt.sub(value[int(a)], representative[int(c)]))) if (cell(a) == c) else 0.0)) for a in range(int(_rt.sumdim('a', len(cell), len(weight), len(value)))))) == 0.0)) for c in range(int(_rt.sumdim('c', len(representative)))))

def cellMean(weight, value, cell, c):
    return _rt.rdiv((sum(((_rt.mul(weight[int(a)], value[int(a)]) if (cell(a) == c) else 0.0)) for a in range(int(len(weight))))), (sum(((weight[int(a)] if (cell(a) == c) else 0.0)) for a in range(int(len(weight))))))

def stratifiedCalibrationEnergy(covariateWeight, posterior, conditional, stratify, predictor):
    return sum((_rt.mul(covariateWeight[int(x)], sum((_rt.mul(posterior[int(x)][int(t)], _rt.lpow((_rt.sub(conditional[int(t)][int(x)], predictor[int((stratify(t)))][int(x)])), 2.0))) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(conditional), len(stratify))))))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(posterior), len(conditional[0]), len(predictor[0])))))

def IsStratumCalibrated(posterior, conditional, stratify, predictor):
    return all(all((((sum(((_rt.mul(posterior[int(x)][int(t)], (_rt.sub(conditional[int(t)][int(x)], predictor[int(s)][int(x)]))) if (stratify(t) == s) else 0.0)) for t in range(int(_rt.sumdim('t', len(stratify), len(posterior[0]), len(conditional)))))) == 0.0)) for s in range(int(_rt.sumdim('s', len(predictor))))) for x in range(int(_rt.sumdim('x', len(posterior), len(conditional[0]), len(predictor[0])))))

def stratumGapEnergy(covariateWeight, posterior, stratify, predictor, other):
    return sum((_rt.mul(covariateWeight[int(x)], sum((_rt.mul(posterior[int(x)][int(t)], _rt.lpow((_rt.sub(predictor[int((stratify(t)))][int(x)], other[int((stratify(t)))][int(x)])), 2.0))) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(stratify))))))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(posterior), len(predictor[0]), len(other[0])))))

def stratumResolutionEnergy(covariateWeight, posterior, conditional, stratify, predictor):
    return sum((_rt.mul(covariateWeight[int(x)], sum((_rt.mul(posterior[int(x)][int(t)], _rt.lpow((_rt.sub(predictor[int((stratify(t)))][int(x)], Descent_posteriorMean(posterior, conditional, x))), 2.0))) for t in range(int(_rt.sumdim('t', len(posterior[0]), len(stratify))))))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(posterior), len(predictor[0])))))

def reportResolutionEnergy(covariateWeight, report, profile):
    return sum((_rt.mul(covariateWeight[int(x)], _rt.lpow(profile[int((report(x)))], 2.0))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(report)))))

def visibleDriftEnergy(indexWeight, covariateWeight, report, profile):
    return sum((_rt.mul(indexWeight[int(t)], sum((_rt.mul(covariateWeight[int(x)], _rt.lpow(profile[int(t)][int((report(x)))], 2.0))) for x in range(int(_rt.sumdim('x', len(covariateWeight), len(report))))))) for t in range(int(_rt.sumdim('t', len(indexWeight), len(profile)))))

def gaugeStratify(t):
    return _rt._proj(t, '1')

def gaugePosterior(_x, _t):
    return _rt.rdiv(1.0, 4.0)

def gaugeAlignedConditional(t, _x):
    return (1.0 if _rt._proj(t, '1') else 0.0)

def gaugeCrossedConditional(t, _x):
    return (1.0 if _rt._proj(t, '2') else 0.0)

def gaugeAlignedPredictor(s, _x):
    return binarySecondAnnotation(s)

def gaugeCrossedPredictor(_s, x):
    return balancedBinaryWeight(x)

def swappedConditional(centre, radius, t, _x):
    return ((centre + radius) if t else (centre - radius))

def swappedConditionalMirror(centre, radius, t, _x):
    return ((centre - radius) if t else (centre + radius))

def balancedPosterior(x, t):
    return gaugeCrossedPredictor(t, x)

def treatNetBenefit(cutoff, risk):
    return decisionCurveNetBenefit(risk, ((1.0 - risk)), 1.0, cutoff)

def decisionRegret(cutoff, risk, treat):
    return (_rt.rmax((treatNetBenefit(cutoff, risk)), 0.0) - ((treatNetBenefit(cutoff, risk) if treat else 0.0)))

def driftDecisionRegret(posterior, conditional, cutoff, treat):
    return sum((_rt.mul(posterior[int(t)], decisionRegret(cutoff, (conditional[int(t)]), treat))) for t in range(int(len(posterior))))

def dynamicsContrastCoefficient(β):
    return _rt.rdiv((_rt.sub(β[int(true)], β[int(false)])), 2.0)

def expectedR2FromN(n, h2, M):
    return (h2 * (_rt.rdiv((n * h2), (((n * h2) + M)))))

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

def IsStationaryKernel(π, P):
    return all((sum(((_rt.mul(π[int(x)], P[int(x)][int(y)]) == π[int(y)])) for x in range(int(len(π))))) for y in range(int(len(π))))

def uniformTwo():
    return (lambda _: _rt.rdiv(1.0, 2.0))

def stayKernel(i, j):
    return kronecker(i, j)

def swapKernel(i, j):
    return antiKronecker(i, j)

def agreement(i, j):
    return stayKernel(i, j)

def regretCurve(π, P, ρ):
    return sum((_rt.mul(π[int(x)], sum((_rt.mul(P[int(x)][int(y)], ρ[int(x)][int(y)])) for y in range(int(len(π)))))) for x in range(int(len(π))))

def horizonPolynomial(u):
    return ((((8.0 * _rt.lpow(u, 4.0)) - (12.0 * _rt.lpow(u, 3.0))) + ((_rt.rdiv(148.0, 25.0)) * _rt.lpow(u, 2.0))) - ((_rt.rdiv(24.0, 25.0)) * u))

def attenuatedVariance(beta_sq, het, r2_imp):
    return product3(beta_sq, het, r2_imp)

def imputationErrorVariance(beta_sq, het, r2_imp):
    return ((beta_sq * het) * ((1.0 - r2_imp)))

def panelAdjustedImputationQuality(r2_LD, panelMatch):
    return product(r2_LD, panelMatch)

def ldExtentImputationQuality(c, ld_extent):
    return _rt.rmax(0.0, ((1.0 - _rt.rdiv(c, ld_extent))))

def apparent_portability_loss(r2_source, r2_target_array):
    return difference(r2_source, r2_target_array)

def true_portability_loss(r2_source, r2_target_ideal):
    return difference(r2_source, r2_target_ideal)

def ascertainment_loss(coverage, v_causal):
    return retainedFraction(coverage, v_causal)

def total_portability_loss(loss_genetic, loss_technical):
    return Descent_Core_sum(loss_genetic, loss_technical)

def portabilityAtTime(r2_initial, lambda_total, t):
    return (r2_initial * _rt.rexp((((-lambda_total) * t))))

def ldDecayPerGeneration(r, t):
    return geometricDecay(r, t)

def secularTrendBias(trend_rate, t):
    return product(trend_rate, t)

def temporalMetricProfile(π, signalAtTime):
    return profileFromSignalVariance(π, 1.0, signalAtTime)

def temporalR2(signalAtTime):
    return r2FromSignalVariance(signalAtTime, 1.0)

def ageDependentSignalShape(age, age_peak, width):
    return _rt.rexp((_rt.rdiv(_rt.lpow((-((age - age_peak))), 2.0), ((2.0 * _rt.lpow(width, 2.0))))))

def ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width):
    return (sourceSignalPeak * ageDependentSignalShape(age, age_peak, width))

def ageDependentMetricProfile(π, sourceSignalPeak, age, age_peak, width):
    return temporalMetricProfile(π, (ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width)))

def cohortObservedEffect(geneticEffect, environmentModifier):
    return product(geneticEffect, environmentModifier)

def ageDependentR2(sourceSignalPeak, age, age_peak, width):
    return temporalR2((ageDependentSignalVariance(sourceSignalPeak, age, age_peak, width)))

def temporalCalibrationInTheLarge(π_obs, π_pred):
    return calibrationInTheLarge(π_obs, π_pred)

def temporalExactBrierRisk(π, signalAtTime):
    return _rt._proj((temporalMetricProfile(π, signalAtTime)), 'brier')

def modelStaleness(lambda_, t):
    return (1.0 - _rt.rexp((((-lambda_) * t))))

def mechanisticPortabilityRatio(m):
    return _rt.rdiv(r2FromSourceWeights(m, 1), r2FromSourceWeights(m, 0))

def sourceSquaredEffectMass(β):
    return sum((_rt.lpow(β[int(i)], 2.0)) for i in range(int(len(β))))

def popgenDrivenTagScale():
    return ((_rt.rdiv(7.0, 6.0)) * _rt.rexp(((-(1.0)))))

def popgenDrivenProxyScale():
    return ((_rt.rdiv(7.0, 6.0)) * _rt.rexp(((-(((1.0) + popgenDrivenLDDecayExponent()))))))

def Descent_R2DecompositionData_r2(d):
    return _rt.rdiv(_rt._proj(d, 'varCondE'), _rt._proj(d, 'varY'))

def discrimination(d):
    return _rt.rdiv(_rt._proj(d, 'varYhat'), _rt._proj(d, 'varY'))

def calibration(d):
    return _rt.rdiv(_rt._proj(d, 'varCondE'), _rt._proj(d, 'varYhat'))

def adaptationDifficultyIndex(nParams, infoPerSample):
    return ratio(nParams, infoPerSample)

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

def pooledConditional(π, η):
    return sum((_rt.mul(π[int(i)], η[int(i)])) for i in range(int(len(π))))

def indexwiseLoss(π, η, v):
    return sum((_rt.mul(π[int(i)], _rt.lpow((_rt.sub(η[int(i)], v)), 2.0))) for i in range(int(len(π))))

def driftDefect(π, η):
    return sum((_rt.mul(π[int(i)], _rt.lpow((_rt.sub(η[int(i)], pooledConditional(π, η))), 2.0))) for i in range(int(len(π))))

def threeAncestryWeights():
    return (lambda _: _rt.rdiv(1.0, 3.0))

def fourAncestryWeights():
    return (lambda _: _rt.rdiv(1.0, 4.0))

def coordinateHighVariance():
    return (lambda i: (1.0 if ((i) < 2.0) else (-1.0)))

def coordinateHighDrift():
    return (lambda i: (1.0 if (((i) % 2.0) == 0.0) else (-1.0)))

def scoreAcrossAncestry():
    return (lambda i: (1.0 if ((i) < 2.0) else (-1.0)))

def driftAcrossAncestry():
    return (lambda i: (1.0 if (((i) % 2.0) == 0.0) else (-1.0)))

def capturedEnergy(π, w, field):
    return _rt.lpow((sum((_rt.mul(_rt.mul(π[int(i)], w[int(i)]), field[int(i)])) for i in range(int(len(π))))), 2.0)

def belowThresholdMass(π, η, τ):
    return sum((_rt.mul(π[int(i)], _rt.rmax((_rt.sub(τ, η[int(i)])), 0.0))) for i in range(int(len(π))))

def bitSign():
    return driftFieldB()

def twoBitIndexWeights():
    return binnedRiskByAncestry()

def uResolvedConditional(u):
    return (lambda _: (_rt.rdiv(1.0, 2.0) + ((_rt.rdiv(1.0, 10.0)) * bitSign(u))))

def vResolvedConditional(v):
    return (lambda i: (_rt.rdiv(1.0, 2.0) + (bitSign(i) * (((_rt.rdiv(1.0, 10.0)) * bitSign(v))))))

def ogpOverlapProfile(q, x):
    return overlapProfile(q, x)

def ogpTransitionPolynomial(q):
    return ((1.0 - (3.0 * q)) + _rt.lpow(q, 2.0))

def mixtureCoupling(ρ, π):
    return (ρ * (((2.0 * π) - 1.0)))

def epochSampleSize(K):
    return pairedEpochCount(K)

def spectrumEntries(n):
    return (n - 1.0)

def absoluteLoss(π, η, v):
    return sum((_rt.mul(π[int(i)], _rt.rabs(_rt.sub(η[int(i)], v)))) for i in range(int(len(π))))

def twoCellL2EstimationPenalty(p, n_1, n_2):
    return (_rt.rdiv(p, n_1) + _rt.rdiv(((1.0 - p)), n_2))

def twoCellWorstEstimationPenalty(n_1, n_2):
    return _rt.rmax((_rt.rdiv(1.0, n_1)), (_rt.rdiv(1.0, n_2)))

def aboveThresholdMass(π, η, τ):
    return sum((_rt.mul(π[int(i)], _rt.rmax((_rt.sub(η[int(i)], τ)), 0.0))) for i in range(int(len(π))))

def threeAncestryDistance():
    return (lambda i, j: _rt.rabs((ancestryPosition(i) - ancestryPosition(j))))

def ancestryScore():
    return threeAncestryConditional()

def ancestryAlignmentEnergy(m):
    return _rt.mul((_rt.rdiv(1.0, 9.0)), sum((sum((_rt.mul(threeAncestryDistance(i, j), _rt.lpow((_rt.sub(m[int(i)], m[int(j)])), 2.0))) for j in range(int(len(m))))) for i in range(int(len(m)))))

def rareAncestryRisks():
    return twoAncestryConditional()

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

def ldPanelRetentionFraction(panel):
    return _rt.rdiv((_rt._proj(panel, 'retainedMarkers')), (_rt._proj(panel, 'totalMarkers')))

def ldBlockDetectionShare(decay, panel):
    return ldBandDetectionShare(decay, (ldPanelRetentionFraction(panel)))

def ldBlockPruningDeficit(decay, panel):
    return ldPruningDetectionDeficit(decay, (ldPanelRetentionFraction(panel)))

def ldTightLinkageDetectionShare(panel):
    return (ldPanelRetentionFraction(panel) - _rt.rdiv(_rt.sin(((_rt.pi * ldPanelRetentionFraction(panel)))), _rt.pi))

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
    return difference(r2_source, r2_target)

def portabilityNoiseVariance(variantCount, varianceScale):
    return _rt.rdiv(varianceScale, (variantCount))

def uncorrectedBias(m):
    return (_rt._proj(m, 'c') * sum((_rt._proj(m, 'eigenvals')(i)) for i in range(int(_rt.sumdim('i', len(_rt._proj(m, 'eigenvals')))))))

def spectralResidualBiasEnergy(retention, bias):
    return sum((_rt.lpow((_rt.mul(retention[int(i)], bias[int(i)])), 2.0)) for i in range(int(len(retention))))

def pgsTestAxisBias(scale, expectedPhenotype, residualTargetAxis):
    return _rt.mul(scale, sum((_rt.mul(expectedPhenotype[int(i)], residualTargetAxis[int(i)])) for i in range(int(len(expectedPhenotype)))))

def ancestryGradientSusceptibility(markerAxisVariance, ancestryVariance):
    return product(markerAxisVariance, ancestryVariance)

def pcTargetAxisEfficacy(uncorrectedSusceptibility, residualSusceptibility):
    return proportionalReduction(residualSusceptibility, uncorrectedSusceptibility)

def ascertainmentAmplification(Φ, Λ):
    return _rt.rdiv((((1.0 + Φ) + Λ)), _rt.rsqrt(((1.0 + Λ))))

def pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ):
    return (_rt.rdiv((_rt.rsqrt(expectedSNPCount) * _rt.rsqrt(Hres)), effectSD) * ascertainmentAmplification(Φ, Λ))

def standardizedResidualPGSBias(expectedSNPCount, Hres, effectSD, Φ, Λ, confounding):
    return (pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ) * confounding)

def criticalConfoundingMagnitude(criticalSignal, expectedSNPCount, Hres, effectSD, Φ, Λ):
    return _rt.rdiv(criticalSignal, pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, Φ, Λ))

def modeledPCResidualSusceptibility(markerAxisVariance, ancestryVariance, n, markers, spike):
    return ancestryGradientSusceptibility(markerAxisVariance, ((ancestryVariance * samplePCResidualAxisFraction(n, markers, spike))))

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

def combinedInformationIndex(cohort):
    return ((4.0 * effectiveSubgroupSize(_rt._proj(cohort, 'sampleSize'), _rt._proj(cohort, 'subgroupSize'))) * _rt.rsqrt((_rt.rdiv(totalInformation(cohort), _rt._proj(cohort, 'sampleSize')))))

def CalculatorAdmissible(cohort):
    return ((_rt._proj(cohort, 'subgroupSize') < _rt._proj(cohort, 'sampleSize')) and all(((_rt._proj(cohort, 'differentiation')(i) <= 1.0)) for i in range(int(_rt.sumdim('i', len(_rt._proj(cohort, 'differentiation')))))))

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

def removedAxisFraction(n, M, spike, pcRank, fittedPCs):
    return (samplePCOverlapSq(n, M, spike) if (pcRank <= fittedPCs) else 0.0)

def fittedResidualAxisFraction(n, M, spike, pcRank, fittedPCs):
    return (1.0 - removedAxisFraction(n, M, spike, pcRank, fittedPCs))

def Descent_EmpiricalPCOverlapModel_residualBiasEnergy(m):
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

def calibrationInTheLarge(mean_observed, mean_predicted):
    return difference(mean_observed, mean_predicted)

def calibrationSlopeDeviation(slope):
    return _rt.rabs((slope - 1.0))

def toProfile(mom, link):
    return Descent_calibrationProfile(link, _rt._proj(mom, 'meanObserved'), _rt._proj(mom, 'meanPredicted'), _rt._proj(mom, 'slope'))

def Descent_identityCalibrationProfile(mean_observed, mean_predicted, slope):
    return Descent_calibrationProfile(0, mean_observed, mean_predicted, slope)

def logisticCalibrationProfile(mean_observed, mean_predicted, slope):
    return Descent_calibrationProfile(1, mean_observed, mean_predicted, slope)

def hosmerLemeshowContrib(observed, expected, n_group):
    return _rt.rdiv((n_group * _rt.lpow(((observed - expected)), 2.0)), ((expected * ((1.0 - expected)))))

def prevalenceLogit(pi):
    return _rt.rlog((_rt.rdiv(pi, ((1.0 - pi)))))

def prevalenceCITLShift(pi_source, pi_target):
    return (prevalenceLogit(pi_target) - prevalenceLogit(pi_source))

def totalObservedMeanShift(prevalence, environmental, genetic):
    return sum3(prevalence, environmental, genetic)

def shiftedObservedMean(baseMean, shift, P):
    return (baseMean + pair(0.0, shift, P))

def Descent_CrossPopulationCalibrationShiftModel_observedMeanShift(m):
    return totalObservedMeanShift(_rt._proj(m, 'prevalenceShift'), _rt._proj(m, 'environmentalObservedShift'), _rt._proj(m, 'geneticObservedShift'))

def predictedMeanShift(m):
    return (_rt._proj(m, 'scoreMeanShift') + _rt._proj(m, 'deploymentInterceptShift'))

def Descent_CrossPopulationCalibrationShiftModel_observedMean(m, P):
    return shiftedObservedMean(_rt._proj(m, 'baseObservedMean'), Descent_CrossPopulationCalibrationShiftModel_observedMeanShift(m), P)

def Descent_CrossPopulationCalibrationShiftModel_predictedMean(m, P):
    return (_rt._proj(m, 'basePredictedMean') + pair(0.0, predictedMeanShift(m), P))

def Descent_CrossPopulationCalibrationShiftModel_calibrationProfile(m, P, link):
    return _rt._proj((calibrationMoments(m, P)), 'toProfile')(link)

def Descent_CrossPopulationCalibrationShiftModel_identityCalibrationProfile(m, P):
    return Descent_CrossPopulationCalibrationShiftModel_calibrationProfile(m, P, 0)

def deploymentIntercept(m, P):
    return (_rt._proj(m, 'baseDeploymentIntercept') + pair(0.0, _rt._proj(m, 'deploymentInterceptShift'), P))

def Descent_CrossPopulationMechanisticCalibrationModel_observedMeanShift(m):
    return totalObservedMeanShift(_rt._proj(m, 'prevalenceShift'), _rt._proj(m, 'environmentalObservedShift'), _rt._proj(m, 'geneticObservedShift'))

def Descent_CrossPopulationMechanisticCalibrationModel_scoreMean(m, P):
    return sourceWeightedTagScore(_rt._proj(m, 'metric'), (_rt._proj(m, 'tagMean')(P)))

def scoreMeanShift(m):
    return (Descent_CrossPopulationMechanisticCalibrationModel_scoreMean(m, 1) - Descent_CrossPopulationMechanisticCalibrationModel_scoreMean(m, 0))

def Descent_CrossPopulationMechanisticCalibrationModel_predictedMean(m, P):
    return (deploymentIntercept(m, P) + Descent_CrossPopulationMechanisticCalibrationModel_scoreMean(m, P))

def Descent_CrossPopulationMechanisticCalibrationModel_observedMean(m, P):
    return shiftedObservedMean(_rt._proj(m, 'baseObservedMean'), Descent_CrossPopulationMechanisticCalibrationModel_observedMeanShift(m), P)

def Descent_CrossPopulationMechanisticCalibrationModel_calibrationSlope(m, P):
    return calibrationSlopeFromSourceWeights(_rt._proj(m, 'metric'), P)

def Descent_CrossPopulationMechanisticCalibrationModel_calibrationProfile(m, P, link):
    return _rt._proj(_rt._proj(m, 'toShiftModel'), 'calibrationProfile')(P, link)

def Descent_CrossPopulationMechanisticCalibrationModel_identityCalibrationProfile(m, P):
    return Descent_CrossPopulationMechanisticCalibrationModel_calibrationProfile(m, P, 0)

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

def targetCalibrationProfileAtGenerationClosedForm(m, t, link):
    return {'citl': (((_rt._proj(m, 'baseObservedMean') + (((_rt._proj(m, 'prevalenceShiftAt')(t) + _rt._proj(m, 'environmentalObservedShiftAt')(t)) + _rt._proj(m, 'geneticObservedShiftAt')(t))))) - (((_rt._proj(m, 'baseDeploymentIntercept') + _rt._proj(m, 'deploymentInterceptShiftAt')(t)) + sourceWeightedTagScore((_rt._proj(_rt._proj(m, 'metric'), 'toMetricModelAt')(t)), (_rt._proj(m, 'targetTagMeanAt')(t)))))), 'slope': calibrationSlopeFromSourceWeights((_rt._proj(_rt._proj(m, 'metric'), 'toMetricModelAt')(t)), 1), 'link': link}

def prevalenceLogisticCalibrationProfile(pi_source, pi_target, slope):
    return logisticCalibrationProfile((prevalenceLogit(pi_target)), (prevalenceLogit(pi_source)), slope)

def interceptRecalibrated(pgs, new_intercept):
    return (new_intercept + pgs)

def logisticRecalibrated(pgs, a, b):
    return (a + (b * pgs))

def recalibratedCalibrationSlope(slope, fittedSlope):
    return ratio(slope, fittedSlope)

def recalibrationTraceMSELowerBound(nEvents, nParams, infoPerEvent):
    return _rt.rdiv(nParams, ((nEvents * infoPerEvent)))

def requiredEventsForRecalibration(nParams, infoPerEvent, targetTraceMSE):
    return ratioOfProduct(nParams, infoPerEvent, targetTraceMSE)

def requiredTargetCohortSizeForRecalibration(nParams, prevalence, infoPerEvent, targetTraceMSE):
    return _rt.rdiv(requiredEventsForRecalibration(nParams, infoPerEvent, targetTraceMSE), prevalence)

def classifiedHighRisk(threshold, predictedRisk):
    return (threshold < predictedRisk)

def nri(up_events, down_events, up_nonevents, down_nonevents, n_events, n_nonevents):
    return (_rt.rdiv(((up_events - down_events)), n_events) + _rt.rdiv(((down_nonevents - up_nonevents)), n_nonevents))

def nriFromDownwardInterceptRecalibration(μevent, μnonevent, threshold, δ):
    return nri(0.0, (downReclassificationRate(μevent, threshold, δ)), 0.0, (downReclassificationRate(μnonevent, threshold, δ)), 1.0, 1.0)

def reclassifiedBandEventPrevalence(π, μevent, μnonevent, threshold, δ):
    return _rt.rdiv(((π * thresholdBandRate(μevent, threshold, δ))), (((π * thresholdBandRate(μevent, threshold, δ)) + (((1.0 - π)) * thresholdBandRate(μnonevent, threshold, δ)))))

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

def pathwayNetBenefitError(truePath, predictedPath, t):
    return (((((_rt._proj(predictedPath, 'eventProb')(t) - _rt._proj(truePath, 'eventProb')(t))) * _rt._proj(truePath, 'treatmentBenefit')(t)) + (_rt._proj(predictedPath, 'eventProb')(t) * ((_rt._proj(predictedPath, 'treatmentBenefit')(t) - _rt._proj(truePath, 'treatmentBenefit')(t))))) - ((_rt._proj(predictedPath, 'treatmentHarm')(t) - _rt._proj(truePath, 'treatmentHarm')(t))))

def treatmentMarginErrorTerm(model, truePath, predictedPath, t):
    return (_rt._proj(model, 'discount')(t) * (((((_rt._proj(predictedPath, 'followupWeight')(t) - _rt._proj(truePath, 'followupWeight')(t))) * (((_rt._proj(truePath, 'eventProb')(t) * _rt._proj(truePath, 'treatmentBenefit')(t)) - _rt._proj(truePath, 'treatmentHarm')(t)))) + (_rt._proj(predictedPath, 'followupWeight')(t) * pathwayNetBenefitError(truePath, predictedPath, t)))))

def screeningUtilityFromCounts(model, tp, fp, n):
    return ((_rt._proj(model, 'benefit') * (_rt.rdiv(tp, n))) - (_rt._proj(model, 'harm') * (_rt.rdiv(fp, n))))

def screeningUtilityFromRates(model, sens, spec, prevalence):
    return (((sens * prevalence) * _rt._proj(model, 'benefit')) - ((((1.0 - spec)) * ((1.0 - prevalence))) * _rt._proj(model, 'harm')))

def screeningQalyGain(sens, spec, prevalence, benefit, harm):
    return screeningUtilityFromRates((qalyScreeningDecisionModel(benefit, harm)), sens, spec, prevalence)

def screeningBreakEvenPrevalence(sens, spec, benefit, harm):
    return _rt.rdiv((((1.0 - spec)) * harm), (((sens * benefit) + (((1.0 - spec)) * harm))))

def decisionCurveNetBenefit(tp, fp, n, t):
    return screeningUtilityFromCounts((decisionCurveScreeningModel(t)), tp, fp, n)

def thresholdQalyLoss(model, trueRisk, predictedRisk):
    return (thresholdQalyGainUnderDecision(model, trueRisk, trueRisk) - thresholdQalyGainUnderDecision(model, trueRisk, predictedRisk))

def thresholdDecisionRegretMargin(model, trueRisk, predictedRisk):
    return by(classical, exact, (_rt.rmax(((_rt._proj(model, 'threshold') - trueRisk)), 0.0) if classifiedHighRisk(_rt._proj(model, 'threshold'), predictedRisk) else _rt.rmax(((trueRisk - _rt._proj(model, 'threshold'))), 0.0)))

def neutralPortabilityRatioLD(fst_additional, ld_factor):
    return retainedFraction(fst_additional, ld_factor)

def neutralDriftFactor(Ne, t):
    return _rt.lpow(((1.0 - _rt.rdiv(1.0, ((2.0 * Ne))))), t)

def selectedDriftFactor(Ne, t, s_correction):
    return _rt.lpow((((1.0 - _rt.rdiv(1.0, ((2.0 * Ne)))) + s_correction)), t)

def fstFromDriftFactor(driftFactor):
    return complement(driftFactor)

def causalPortabilityFromLocalFst(sourceSquaredEffect, fstCausal):
    return _rt.rdiv((sum((_rt.mul(sourceSquaredEffect[int(i)], (_rt.sub(1.0, fstCausal[int(i)])))) for i in range(int(len(sourceSquaredEffect))))), (sum((sourceSquaredEffect[int(i)]) for i in range(int(len(sourceSquaredEffect))))))

def polygenicCalibrationFloor(genotypeWeight, ancestryPosterior, ancestryRisk):
    return calibrationDriftDefectSq(genotypeWeight, ancestryPosterior, ancestryRisk)

def neutralPortability(r2_0, fst):
    return _rt.rdiv((r2_0 * ((1.0 - fst))), (((((1.0 - fst)) * r2_0) + ((1.0 - r2_0)))))

def coalescenceSurvivalFromHazard(hazard, t):
    return _rt.rexp(((-(integratedCoalescentHazard(hazard, t)))))

def coalescenceCdfFromHazard(hazard, t):
    return (1.0 - coalescenceSurvivalFromHazard(hazard, t))

def coalescentTau(t, Ne):
    return _rt.rdiv(t, ((2.0 * Ne)))

def Descent_fstFromTau(tau):
    return Descent_Core_fstFromTau(tau)

def fstFromGenerations(t, Ne):
    return Descent_fstFromTau((coalescentTau(t, Ne)))

def pairwiseFstFromBranches(fstS, fstT):
    return complementaryComposition(fstS, fstT)

def pairwiseFstFromBranchTaus(tauS, tauT):
    return Descent_fstFromTau((_rt.rdiv(((tauS + tauT)), 2.0)))

def fstEqLimitLowMutationManyDemes(m):
    return _rt.rdiv(1.0, ((1.0 + Descent_scaledMigrationRate(_rt._proj(m, 'Ne'), _rt._proj(m, 'mig')))))

def hudsonFstFromCoalescenceTimes(ETss, ETst):
    return proportionalReduction(ETss, ETst)

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
    return retainedFraction(fst, het_source)

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

def driftMoments(V_A, V_E, fst):
    return momentsUnderDrift(V_A, V_E, fst)

def deployedBrierAtEquilibrium(π, p, V_E):
    return brier(π, (driftMoments(_rt._proj(p, 'V_A'), V_E, Descent_Core_PopGenParameters_fstEquilibrium(p))))

def presentDayEqualVarianceGaussianAUC(V_A, V_E, fst):
    return equalVarianceGaussianAUCFromSignalVariance((presentDayPGSVariance(V_A, fst)), V_E)

def realWorldPGSVariance(V_A, fst, rhoSq):
    return ((rhoSq * ((1.0 - fst))) * V_A)

def sourceERMWeights(sigmaObsSource, crossSource):
    return _rt._proj(_rt.rinv(sigmaObsSource), 'mulVec')(crossSource)

def sigmaTagCausalSourceAt(m, P):
    return (((_rt._proj(m, 'directCausal')(P) + _rt._proj(m, 'novelDirectCausal')(P))) + ((_rt._proj(m, 'proxyTagging')(P) + _rt._proj(m, 'novelProxyTagging')(P))))

def Descent_totalEffect(m, P):
    return (_rt._proj(m, 'beta')(P) + _rt._proj(m, 'novelCausalEffect')(P))

def targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, w):
    return _rt.sub(_rt.add(noiseVar, _rt.dotProduct(w, (_rt.mulVec(sigmaObsTarget, w)))), _rt.mul(2.0, _rt.dotProduct(w, crossTarget)))

def crossCovariance(m, P):
    return (_rt._proj((sigmaTagCausalSourceAt(m, P)), 'mulVec')((Descent_totalEffect(m, P))) + _rt._proj(m, 'contextCross')(P))

def sourceWeightsFromExplicitDrivers(m):
    return sourceERMWeights((_rt._proj(m, 'sigmaTag')(0)), (crossCovariance(m, 0)))

def sourceWeightedTagScore(m, tagState):
    return _rt.dotProduct((sourceWeightsFromExplicitDrivers(m)), tagState)

def taggingProjection(m, P):
    return _rt._proj((sigmaTagCausalSourceAt(m, P)), 'mulVec')((Descent_totalEffect(m, P)))

def targetEffectHeterogeneity(m):
    return (Descent_totalEffect(m, 1) - (_rt._proj(m, 'beta')(0)))

def targetSourceEffectProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((_rt._proj(m, 'beta')(0)))

def targetEffectHeterogeneityProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((targetEffectHeterogeneity(m)))

def targetNovelMutationEffectProjection(m):
    return _rt._proj((sigmaTagCausalSourceAt(m, 1)), 'mulVec')((_rt._proj(m, 'novelCausalEffect')(1)))

def directCausalProjection(m, P):
    return _rt._proj(((_rt._proj(m, 'directCausal')(P) + _rt._proj(m, 'novelDirectCausal')(P))), 'mulVec')((Descent_totalEffect(m, P)))

def proxyTaggingProjection(m, P):
    return _rt._proj(((_rt._proj(m, 'proxyTagging')(P) + _rt._proj(m, 'novelProxyTagging')(P))), 'mulVec')((Descent_totalEffect(m, P)))

def scoreVarianceFromSourceWeights(m, P):
    wS = sourceWeightsFromExplicitDrivers(m)
    return _rt.dotProduct(wS, (_rt._proj((_rt._proj(m, 'sigmaTag')(P)), 'mulVec')(wS)))

def predictiveCovarianceFromSourceWeights(m, P):
    return _rt.dotProduct((sourceWeightsFromExplicitDrivers(m)), (crossCovariance(m, P)))

def calibrationSlopeFromSourceWeights(m, P):
    return _rt.rdiv(predictiveCovarianceFromSourceWeights(m, P), scoreVarianceFromSourceWeights(m, P))

def brokenTaggingResidual(m):
    delta = _rt._proj((((sigmaTagCausalSourceAt(m, 0)) - (sigmaTagCausalSourceAt(m, 1)))), 'mulVec')((Descent_totalEffect(m, 1)))
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
    return calibratedBrierFromVariances(π, (explainedSignalVarianceFromSourceWeights(m, 0)), (residualVarianceFromSourceWeights(m, 0)))

def targetCalibratedBrierFromSourceWeights(m):
    return calibratedBrierFromVariances(_rt._proj(m, 'targetPrevalence'), (explainedSignalVarianceFromSourceWeights(m, 1)), (residualVarianceFromSourceWeights(m, 1)))

def ldCorrelationDecay(distance, fstGap, lambda_):
    return _rt.rexp(((-(((lambda_ * _rt.rsqrt(fstGap)) * distance)))))

def tauAt(g, t):
    return _rt.rdiv((t), ((2.0 * _rt._proj(g, 'Ne'))))

def Descent_Core_PopGenParameters_hetDecayFactor(g):
    return hetDecayFromScaled(_rt._proj(g, 'Ne'), Descent_Core_PopGenParameters_theta(g))

def fstTransientAt(g, t):
    return ((_rt.rdiv(1.0, (((1.0 + Descent_Core_PopGenParameters_theta(g)) + (2.0 * Descent_Core_PopGenParameters_bigM(g)))))) * ((1.0 - _rt.lpow(fstTransientDecayFromScaled(_rt._proj(g, 'Ne'), Descent_Core_PopGenParameters_theta(g), Descent_Core_PopGenParameters_bigM(g)), t))))

def mutationSharedRetentionAt(g, t):
    return _rt.rexp((((-Descent_Core_PopGenParameters_theta(g)) * tauAt(g, t))))

def migrationSharedBoostAt(g, t):
    return (1.0 + _rt.rdiv((Descent_Core_PopGenParameters_bigM(g) * tauAt(g, t)), ((1.0 + Descent_Core_PopGenParameters_bigM(g)))))

def alleleFreqMismatchPenalty(pSource, pTarget):
    return _rt.rdiv((((2.0 * pTarget) * ((1.0 - pTarget)))), (((2.0 * pSource) * ((1.0 - pSource)))))

def betaTargetAt(m, t):
    return ((_rt._proj(m, 'betaSource') + _rt._proj(m, 'targetEffectHeterogeneityAt')(t)) + _rt._proj(m, 'novelCausalEffectTargetAt')(t))

def tagAlleleFreqTargetAt(m, t, i):
    return (_rt._proj(m, 'tagAlleleFreqStandingTargetAt')(t, i) + _rt._proj(m, 'tagAlleleFreqMutationShiftAt')(t, i))

def causalAlleleFreqTargetAt(m, t, j):
    return (_rt._proj(m, 'causalAlleleFreqStandingTargetAt')(t, j) + _rt._proj(m, 'causalAlleleFreqMutationShiftAt')(t, j))

def tagAlleleFreqRetentionAt(m, t, i):
    return _rt.rdiv((((2.0 * tagAlleleFreqTargetAt(m, t, i)) * ((1.0 - tagAlleleFreqTargetAt(m, t, i))))), (((2.0 * _rt._proj(m, 'tagAlleleFreqSource')(i)) * ((1.0 - _rt._proj(m, 'tagAlleleFreqSource')(i))))))

def causalAlleleFreqRetentionAt(m, t, j):
    return _rt.rdiv((((2.0 * causalAlleleFreqTargetAt(m, t, j)) * ((1.0 - causalAlleleFreqTargetAt(m, t, j))))), (((2.0 * _rt._proj(m, 'causalAlleleFreqSource')(j)) * ((1.0 - _rt._proj(m, 'causalAlleleFreqSource')(j))))))

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

def hetRatioBetweenBranches(NeA, NeB, mu, H_0, t):
    return _rt.rdiv(hetTrajectory(NeB, mu, H_0, t), hetTrajectory(NeA, mu, H_0, t))

def brierFromR2(π, r2):
    return calibratedBrier(π, r2)

def standardNormalPdf(x):
    return _rt.rdiv(_rt.rexp((_rt.rdiv(_rt.lpow((-x), 2.0), 2.0))), _rt.rsqrt(((2.0 * _rt.pi))))

def liabilityCaseMean(K):
    return _rt.rdiv(standardNormalPdf((liabilityThreshold(K))), K)

def liabilityControlMean(K):
    return _rt.rdiv(((-liabilityCaseMean(K)) * K), ((1.0 - K)))

def liabilityCaseVariance(r2, K):
    return (1.0 - ((r2 * liabilityCaseMean(K)) * ((liabilityCaseMean(K) - liabilityThreshold(K)))))

def liabilityControlVariance(r2, K):
    return (1.0 - ((r2 * liabilityControlMean(K)) * ((liabilityControlMean(K) - liabilityThreshold(K)))))

def liabilityThresholdAUCFromExplainedR2(r2, K):
    return Phi((_rt.rdiv((((liabilityCaseMean(K) - liabilityControlMean(K))) * _rt.rsqrt(r2)), _rt.rsqrt(((liabilityCaseVariance(r2, K) + liabilityControlVariance(r2, K)))))))

def sourceBrierFromR2(π, r2Source):
    return calibratedBrier(π, r2Source)

def targetExactCalibratedBrierRisk(π, V_A, V_E, fstTarget):
    return calibratedBrier(π, (targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget)))

def targetBrierFromNeutralAFBenchmark(π, V_A, V_E, fstTarget):
    return targetExactCalibratedBrierRisk(π, V_A, V_E, fstTarget)

def neutralAFBenchmarkMetricProfile(π, V_A, V_E, fstTarget):
    return profileFromSignalVariance(π, V_E, (presentDayPGSVariance(V_A, fstTarget)))

def equalVarianceGaussianAUCFromSNR(snr):
    return Phi((_rt.rsqrt((_rt.rdiv(snr, 2.0)))))

def equalVarianceGaussianAUCFromExplainedR2(r2):
    return (1.0 if (1.0 <= r2) else Phi((_rt.rsqrt((_rt.rdiv(r2, ((2.0 * ((1.0 - r2))))))))))

def targetLiabilityAUCFromNeutralAFBenchmark(V_A, V_E, fstTarget, K):
    return liabilityThresholdAUCFromExplainedR2((presentDayR2(V_A, V_E, fstTarget)), K)

def neutralAFBenchmarkLiabilityMetricProfile(π, V_A, V_E, fstTarget):
    return {'r2': targetR2FromNeutralAFBenchmark(V_A, V_E, fstTarget), 'auc': targetLiabilityAUCFromNeutralAFBenchmark(V_A, V_E, fstTarget, π), 'brier': targetBrierFromNeutralAFBenchmark(π, V_A, V_E, fstTarget)}

def equalVarianceGaussianAUCFromSourceWeights(m, P):
    return equalVarianceGaussianAUCFromSignalVariance((explainedSignalVarianceFromSourceWeights(m, P)), (residualVarianceFromSourceWeights(m, P)))

def sourceMetricProfileFromSourceWeightsAtTargetPrevalence(m):
    return sourceMetricProfileFromSourceWeightsAtPrevalence(m, _rt._proj(m, 'targetPrevalence'))

def targetMetricProfileAtGeneration(m, t):
    return targetMetricProfileFromSourceWeights((toMetricModelAt(m, t)))

def sourceNormalizedTargetR2AtGeneration(m, sourceBaseline, t):
    return (sourceBaseline * (_rt.rdiv(r2FromSourceWeights((toMetricModelAt(m, t)), 1), r2FromSourceWeights((toMetricModelAt(m, t)), 0))))

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

def Descent_MutationDriftModelAssumptions_fstEquilibrium(m):
    return fstMutationDriftEquilibrium(Descent_MutationDriftModelAssumptions_theta(m))

def Descent_MutationDriftModelAssumptions_fstTransient(m):
    return (Descent_MutationDriftModelAssumptions_fstEquilibrium(m) * ((1.0 - _rt.rexp((_rt.rdiv(((-((1.0 + Descent_MutationDriftModelAssumptions_theta(m)))) * _rt._proj(m, 't')), ((2.0 * _rt._proj(m, 'Ne')))))))))

def covarianceRetention(freq_corr, ld_overlap):
    return product(freq_corr, ld_overlap)

def covarianceRetentionFactorFromFst(fst):
    return complement(fst)

def alleleFreqCorrelation(fst, varAncestral, meanHetAncestral):
    return _rt.rdiv(varAncestral, ((varAncestral + (fst * meanHetAncestral))))

def ldOverlapFromSharedLD(shared_ld):
    return identifiedWith(shared_ld)

def covarianceDivergenceFromRetention(fst, shared_ld):
    return (1.0 - covarianceRetention((covarianceRetentionFactorFromFst(fst)), (ldOverlapFromSharedLD(shared_ld))))

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
    return fstFromFlow((((4.0 * Ne) * m)))

def ibdRecurrenceStep(Ne, rate, x):
    return survivalWeightedMix(Ne, rate, x)

def ibdRecurrenceFixedPoint(Ne, rate):
    return _rt.rdiv(_rt.lpow(((1.0 - rate)), 2.0), ((_rt.lpow(((1.0 - rate)), 2.0) + (((2.0 * Ne) * rate) * ((2.0 - rate))))))

def islandFstMultiplicativeStep(Ne, m, F):
    return ibdRecurrenceStep(Ne, m, F)

def fstIslandMultiplicativeEquilibrium(Ne, m):
    return ibdRecurrenceFixedPoint(Ne, m)

def fstMigDriftEq(s):
    return fstMigrationDriftEquilibrium(_rt._proj(s, 'Ne'), _rt._proj(s, 'mig'))

def steppingStoneFst(fst_neighbor, α, d):
    return _rt.rdiv(((d) * fst_neighbor), (((fst_neighbor * (d)) + (α * ((1.0 - fst_neighbor))))))

def sharedLD_from_equilibrium(m, c):
    return share(m, c)

def sharedLDFromMigration(M):
    return saturation(M)

def signalRetentionMigrationDrift(Ne, m):
    return (((1.0 - fstMigrationDriftEquilibrium(Ne, m))) * sharedLDFromMigration((Descent_scaledMigrationRate(Ne, m))))

def retainedSignalVarianceMigrationDrift(V_A, Ne, m):
    return (signalRetentionMigrationDrift(Ne, m) * V_A)

def asymmetricFst(Ne, m_1_2, m_2_1):
    return _rt.rdiv(1.0, ((1.0 + ((4.0 * Ne) * ((m_1_2 + m_2_1))))))

def effectiveSymmetricMigration(m_1_2, m_2_1):
    return midpoint(m_1_2, m_2_1)

def admixtureLDDecay(r, generations_since):
    return geometricDecay(r, generations_since)

def admixtureLDBoost(r, t_since, equilibrium_ld):
    return _rt.rdiv(admixtureLDDecay(r, t_since), equilibrium_ld)

def fstMigDriftNext(Ne, m, Fst):
    return (((((1.0 - (2.0 * m)) - _rt.rdiv(1.0, ((2.0 * Ne))))) * Fst) + _rt.rdiv(1.0, ((2.0 * Ne))))

def neutralAFBenchmarkFromRecurrence(Ne, m):
    return (1.0 - fstMigrationDriftEquilibrium(Ne, m))

def r2OfStatistic(s):
    return _rt.rdiv(_rt.lpow(_rt._proj(_rt._proj(s, '2'), '1'), 2.0), ((_rt._proj(s, '1') * _rt._proj(_rt._proj(s, '2'), '2'))))

def unitWeight():
    return 1.0

def exceedance(P, w, t):
    return _rt._proj(P, 'E')(((lambda ω: (1.0 if (t < score(P, w, ω)) else 0.0))))

def rareVariantSharingApproximation(Ne, p):
    return pgsDriftVariance_one_pop(p, Ne)

def rareHeritabilityShare(rareCount, rareVariance, commonCount, commonVariance):
    return _rt.rdiv((rareCount * rareVariance), (((rareCount * rareVariance) + (commonCount * commonVariance))))

def variantGeneticVarianceContribution(β, p):
    return (_rt.lpow(β, 2.0) * (((2.0 * p) * ((1.0 - p)))))

def rareVariantCountRatio(sourceCount, targetCount):
    return ratio(sourceCount, targetCount)

def independentGeneSharingProbability(singleShare, variantCount):
    return (1.0 - _rt.lpow(((1.0 - singleShare)), variantCount))

def homogeneousGeneBurdenVariance(β, variantCount):
    return ncp(variantCount, β)

def burdenSquaredSignal(β_1, β_2):
    return _rt.lpow(((β_1 + β_2)), 2.0)

def varianceComponentSignal(β_1, β_2):
    return (_rt.lpow(β_1, 2.0) + _rt.lpow(β_2, 2.0))

def portableVariantSignal(β, frequency, sharing):
    return (variantGeneticVarianceContribution(β, frequency) * sharing)

def mutationSelectionStepRare(mu, s, h, p):
    return ((p * ((1.0 - (h * s)))) + (mu * ((1.0 - p))))

def mutationSelectionBalance(mu, s, h):
    return _rt.rdiv(mu, (((h * s) + mu)))

def mutationSelectionDriftParameter(Ne, s, h):
    return (((4.0 * Ne) * h) * s)

def DeterministicMutationSelectionRegime(Ne, s, h):
    return (10.0 <= mutationSelectionDriftParameter(Ne, s, h))

def mutationSelectionStepRecessive(mu, s, p):
    return ((p - (s * _rt.lpow(p, 2.0))) + (mu * ((1.0 - p))))

def mutationSelectionBalanceRecessive(mu, s):
    return _rt.rdiv(((_rt.rsqrt(((mu * ((mu + (4.0 * s)))))) - mu)), ((2.0 * s)))

def recessiveMutationSelectionDriftParameter(Ne, mu, s):
    return ((2.0 * Ne) * _rt.rsqrt(((mu * s))))

def DeterministicRecessiveBalanceRegime(Ne, mu, s):
    return (200.0 <= recessiveMutationSelectionDriftParameter(Ne, mu, s))

def expectedEffectMultiplier(p, α):
    return _rt.lpow(((p * ((1.0 - p)))), ((1.0 + α)))

def overlapInflation(r2_true, r2_observed):
    return (_rt.rdiv(r2_observed, r2_true) - 1.0)

def partialOverlapR2(r2_true, h2, f, _n_gwas):
    return ((((1.0 - f)) * r2_true) + (f * h2))

def approxLOOPGS(pgs_full, leverage, residual):
    return (pgs_full - (leverage * residual))

def kinshipInflation(r2_true, K, h2_family):
    return affineStep(r2_true, K, h2_family)

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

def berryEsseenBound(C, ρ, σ_sq, m):
    return _rt.rdiv(Descent_Foundations_berryEsseenErrorBound(C, σ_sq, ρ), _rt.rsqrt(m))

def effectiveBlockCount(markers, correlationLength):
    return ratio(markers, correlationLength)

def residualDiscreteness(correlationLength, n):
    return _rt.lpow(((1.0 - _rt.rdiv(1.0, correlationLength))), ((n - 1.0)))

def excursionShapeFactor(blockThirdMoment, blockSecondMoment):
    return _rt.rdiv(blockThirdMoment, _rt.lpow(blockSecondMoment, (_rt.rdiv(3.0, 2.0))))

def externallyStandardized(pgs, μ_source, σ_source):
    return _rt.rdiv(((pgs - μ_source)), σ_source)

def internallyStandardized(pgs, μ_target, σ_target):
    return _rt.rdiv(((pgs - μ_target)), σ_target)

def incrementalR2(r2_full, r2_covariates):
    return difference(r2_full, r2_covariates)

def Descent_portabilityRatio(dr2_target, dr2_source):
    return ratio(dr2_target, dr2_source)

def sampleOverlapBias(predictorCount, overlapCount):
    return ratio(predictorCount, overlapCount)

def effectiveSampleSizeFromSE(se, p):
    return _rt.rdiv(1.0, ((_rt.lpow(se, 2.0) * (((2.0 * p) * ((1.0 - p)))))))

def fixed_weights(m, i):
    return _rt.rdiv(1.0, _rt._proj(m, 'variances')(i))

def random_weights(m, i):
    return _rt.rdiv(1.0, ((_rt._proj(m, 'variances')(i) + _rt._proj(m, 'tau_sq'))))

def twoRegionGeneticCorrelation(rhoFirst, rhoSecond, firstWeight, secondWeight):
    return _rt.rdiv((((firstWeight * rhoFirst) + (secondWeight * rhoSecond))), ((firstWeight + secondWeight)))

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
    return squaredShare(cov_pgs_y, var_pgs, var_y)

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
    return sourceTruthR2SharedLD(β_source, standardizedDiagonalLD(), var_y)

def transportedTargetR2DiagonalLD(β_source, β_target, var_y):
    return transportedTargetR2SharedLD(β_source, β_target, standardizedDiagonalLD(), var_y)

def benDavidUpperBound(err_source, divergence, lambda_star):
    return sum3(err_source, divergence, lambda_star)

def importanceWeightESS(sum_w, sum_w_sq):
    return scaledSquare(sum_w, sum_w_sq)

def AsymptoticallyConsistent(est, truth):
    return AsymptoticallyZero(((lambda n: (est(n) - truth))))

def pcaSignalLossPenalty(signalBaseline, signalRetained, lossWeight):
    return (lossWeight * ((signalBaseline - signalRetained)))

def pcaBiasReduction(ancestryBiasWith, ancestryBiasWithout):
    return difference(ancestryBiasWith, ancestryBiasWithout)

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
    return difference(oracle_target_r2, estimation_penalty)

def deployedTransferTargetR2(transported_r2, adaptation_gain, estimation_penalty):
    return ((transported_r2 + adaptation_gain) - estimation_penalty)

def oracleTransportAdaptationGain(transported_r2, oracle_target_r2):
    return (oracle_target_r2 - transported_r2)

def transportPenalty(source_r2, transported_r2):
    return difference(source_r2, transported_r2)

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
    return weightedPopulationDeviation(wSource, weight)

def optimalFineTuningMSE(gapSq, noiseVar, nTarget):
    return sourceShrinkageMSE(gapSq, noiseVar, nTarget, (optimalSourceShrinkageWeight(gapSq, noiseVar, nTarget)))

def requiredTargetSamplesForOptimalFineTuningMSE(gapSq, noiseVar, tau):
    return _rt.rdiv((noiseVar * ((gapSq - tau))), ((tau * gapSq)))

def targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, w, wStar):
    return _rt.sub(targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, w), targetLinearRisk(sigmaObsTarget, crossTarget, noiseVar, wStar))

def exactAdaptationGain(sigmaObsTarget, crossTarget, noiseVar, wBefore, wAfter, wStar):
    return _rt.sub(targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, wBefore, wStar), targetLinearExcessRisk(sigmaObsTarget, crossTarget, noiseVar, wAfter, wStar))

def fineTunedTargetR2OfExactGain():
    return fineTunedTargetR2(source_r2, (transportPenalty(source_r2, transported_r2)), (exactAdaptationGain(sigmaObsTarget, crossTarget, noiseVar, wBefore, wAfter, wStar)))

def isotropicFineTunedTargetR2():
    return fineTunedTargetR2OfExactGain(source_r2, transported_r2, (1.0), crossTarget, noiseVar, wBefore, wAfter, wStar)

def privateArchitectureTransferCeiling(h2_target, f_private, M):
    return ((h2_target * ((1.0 - f_private))) * sharedLDFromMigration(M))

def spectralEnergy(μ, c):
    return sum(((μ(i) * _rt.lpow(c(i), 2.0))) for i in range(int(_rt.sumdim('i', len(μ), len(c)))))

def trueDesignValue(δ, i):
    return (1.0 if (i == 0.0) else (1.0 - δ))

def approxDesignValue(δ, i):
    return ((1.0 - δ) if (i == 0.0) else 1.0)

def transplantSqNorm(v):
    return _rt.dotProduct(v, v)

def transplantDefect():
    return transplantSqNorm((transplantModuleProjection(((lambda i: (transplantTarget(i) - transplantOptimum(i)))))))

def transplantExcess(ε):
    return transplantSqNorm((transplantModuleProjection(((lambda i: (transplantTarget(i) - transplantEstimate(ε, i)))))))

def effectShare(indirect_effect, total_effect):
    return ratio(indirect_effect, total_effect)

def costEffectiveness(improvement, cost):
    return ratio(improvement, cost)

def eValue(rr):
    return (rr + _rt.rsqrt(((rr * ((rr - 1.0))))))

def brierScore(p, y):
    return _rt.lpow(((y - p)), 2.0)

def expectedBrierScore(p, π):
    return ((π * _rt.lpow(((1.0 - p)), 2.0)) + (((1.0 - π)) * _rt.lpow(p, 2.0)))

def TrueCondProb(Z):
    return ProbMap(Z)

def ProbPredictor(Z):
    return ProbMap(Z)

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

def Descent_Program_ploidy():
    return Descent_Core_ploidy

def hweGenotypeVariance(p):
    return Descent_Core_hweHeterozygosity(p)

def coalescentTimeScale(Ne):
    return (Descent_Program_ploidy() * Ne)

def meanAlleleFreq(p_1, p_2):
    return midpoint(p_1, p_2)

def neiGst(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), (((_rt.lpow(Descent_Program_ploidy(), 2.0) * meanAlleleFreq(p_1, p_2)) * ((1.0 - meanAlleleFreq(p_1, p_2))))))

def hudsonFst(p_1, p_2):
    return _rt.rdiv(_rt.lpow(((p_1 - p_2)), 2.0), (((p_1 * ((1.0 - p_2))) + (p_2 * ((1.0 - p_1))))))

def betweenSubgroupVariance(p_1, p_2):
    return halfDiffSq(p_1, p_2)

def neiContrastSpike(n, m, p_1, p_2):
    return demographicSpike(n, (neiGst(p_1, p_2)), m)

def hudsonBbpSpike(n, m, p_1, p_2):
    return demographicSpike(n, (hudsonFst(p_1, p_2)), m)

def ldTaggingDecay(lam_LD, d):
    return _rt.rexp((((-lam_LD) * d)))

def combinedPortability(r2_src, lam_LD, lam_eff, d):
    return ((r2_src * ldTaggingDecay(lam_LD, d)) * _rt.lpow((_rt.rexp((((-lam_eff) * d)))), 2.0))

def snrPortabilityRatio(v_sig_s, v_noise_s, v_sig_t, v_noise_t):
    return _rt.rdiv((_rt.rdiv(v_sig_t, v_noise_t)), (_rt.rdiv(v_sig_s, v_noise_s)))

def f1Score(precision, sensitivity):
    return _rt.rdiv(((2.0 * precision) * sensitivity), ((precision + sensitivity)))

def circulationQuadraticForm(a, x, y):
    return ((x * ((a * y))) + (y * ((-((a * x))))))

def driftGeneratorForm(s, a, x, y):
    return ((s * ((_rt.lpow(x, 2.0) + _rt.lpow(y, 2.0)))) + circulationQuadraticForm(a, x, y))

def frontierTime(s):
    return _rt.rdiv(1.0, s)

def apparentMixingTime(s, a):
    return _rt.rdiv(s, ((_rt.lpow(s, 2.0) + _rt.lpow(a, 2.0))))

def circulationDefect(s, a):
    return _rt.rdiv(_rt.lpow(a, 2.0), ((s * ((_rt.lpow(s, 2.0) + _rt.lpow(a, 2.0))))))

def transferTimeInflation(s, a):
    return (1.0 + _rt.lpow((_rt.rdiv(a, s)), 2.0))

def dirichletEfficiency(τ, energy):
    return (1.0 + (τ * energy))

def driftHorizon(D_1, D_2, C):
    return _rt.rdiv(((D_2 - D_1)), ((2.0 * C)))

def localizedTransferVariance(v, _k):
    return identifiedWith(v)

def delocalizedTransferVariance(v, k):
    return ratio(v, k)

def sampleInverseInflation(n, m):
    return _rt.rdiv(n, (((n - m) - 1.0)))

def stalePremium(lam, τ, V):
    return ((((2.0 * _rt.rexp(((-((lam * τ)))))) - 1.0)) * V)

def stalenessCrossover(lam, _hlam):
    return _rt.rdiv(_rt.rlog(2.0), lam)

def dampedAdjustment(lam, τ, g):
    return (_rt.rexp(((-((lam * τ))))) * g)

def dampedPremium(lam, τ, V):
    return (_rt.rexp(((-(((2.0 * lam) * τ))))) * V)

def myopiaPrice(lam, τ, V):
    return (_rt.lpow(((1.0 - _rt.rexp(((-((lam * τ))))))), 2.0) * V)

def shrinkagePremium(α, ρ, V):
    return ((α * (((2.0 * ρ) - α))) * V)

def fejerChannel3(γ_0, γ_1, γ_2):
    return ((γ_0 + ((_rt.rdiv(4.0, 3.0)) * γ_1)) + ((_rt.rdiv(2.0, 3.0)) * γ_2))

def gaussianPairSquareChannel3(γ_0, γ_1, γ_2):
    return (((3.0 * _rt.lpow(γ_0, 2.0)) + (4.0 * _rt.lpow(γ_1, 2.0))) + (2.0 * _rt.lpow(γ_2, 2.0)))

def twoUnitArrow(f, g, x_0, x_1):
    return _rt.sub(_rt.mul(f[int(x_0)], g[int(x_1)]), _rt.mul(g[int(x_0)], f[int(x_1)]))

def binaryFirstAnnotation(x):
    return (0.0 if x else 1.0)

def binarySecondAnnotation(x):
    return (1.0 if x else 0.0)

def binaryOrientationArrowVariance(θ):
    return (1.0 - _rt.lpow(θ, 2.0))

def threeCycleForwardCrossMoment(f, g):
    return _rt.rdiv((_rt.add(_rt.add(_rt.mul(f[int(0.0)], g[int(1.0)]), _rt.mul(f[int(1.0)], g[int(2.0)])), _rt.mul(f[int(2.0)], g[int(0.0)]))), 3.0)

def threeCycleCrossFeatureArrow(f, g):
    return _rt.sub(threeCycleForwardCrossMoment(f, g), threeCycleForwardCrossMoment(g, f))

def ensembleSquaredLoss(target, deployment):
    return sum((_rt.lpow((_rt.sub(target[int(i)], deployment)), 2.0)) for i in range(int(len(target))))

def ensemblePredictorSquaredLoss(target, predictor):
    return sum((_rt.lpow((_rt.sub(target[int(i)], predictor[int(i)])), 2.0)) for i in range(int(len(target))))

def weightedBandEnsembleLoss(weight, target, deployment):
    return sum((sum((_rt.mul(weight[int(i)][int(b)], _rt.lpow((_rt.sub(target[int(i)][int(b)], deployment[int(b)])), 2.0))) for b in range(int(_rt.sumdim('b', len(weight[0]), len(target[0]), len(deployment)))))) for i in range(int(_rt.sumdim('i', len(weight), len(target)))))

def weightedBandPredictorLoss(weight, target, predictor):
    return sum((sum((_rt.mul(weight[int(i)][int(b)], _rt.lpow((_rt.sub(target[int(i)][int(b)], predictor[int(i)][int(b)])), 2.0))) for b in range(int(len(weight))))) for i in range(int(len(weight))))

def coupledBinarySource(ω, _):
    return ω

def twoSiteCovarianceEnergy(ρ, x, y):
    return ((_rt.lpow(x, 2.0) + _rt.lpow(y, 2.0)) + (((2.0 * ρ) * x) * y))

def localPencilTraceContribution(source, target):
    return _rt.rdiv((((1.0 + _rt.lpow(source, 2.0)) - ((2.0 * source) * target))), ((1.0 - _rt.lpow(source, 2.0))))

def firstModeConditionalMean(mean, r, source):
    return (mean + (r * ((source - mean))))

def diploidStdev(q):
    return _rt.rsqrt((((2.0 * q) * ((1.0 - q)))))

def diploidAtomValue(j, q):
    return _rt.rdiv((((j) - (2.0 * q))), diploidStdev(q))

def diploidAtomMass(j, q):
    return (_rt.lpow(((1.0 - q)), 2.0) if (j == 0.0) else (((2.0 * q) * ((1.0 - q))) if (j == 1.0) else _rt.lpow(q, 2.0)))

def diploidFamily():
    return {'atomValue': diploidAtomValue, 'atomMass': diploidAtomMass}

def invHeterozygosity(q):
    return _rt.rdiv(1.0, (((2.0 * q) * ((1.0 - q)))))

def diploidCovarianceMomentPermeability(q, covarianceDerivative):
    return covarianceMomentPermeability(covarianceDerivative, 1.0, (sum(((diploidAtomMass(j, q) * _rt.lpow(diploidAtomValue(j, q), 4.0))) for j in range(int(3)))))

def diploidPanelCovarianceMomentPermeability(q, covarianceDerivative, taggingResponse):
    return diagonalCovarianceMomentPermeability(((lambda i: _rt.mul(taggingResponse[int(i)], covarianceDerivative[int(i)]))), ((lambda _: 1.0)), ((lambda i: sum((_rt.mul(diploidAtomMass(j, (q[int(i)])), _rt.lpow(diploidAtomValue(j, (q[int(i)])), 4.0))) for j in range(int(3))))))

def totalDiploidCovarianceMomentInformation(m, q, covarianceDerivative):
    return (m * diploidCovarianceMomentPermeability(q, covarianceDerivative))

def ofScalar(D):
    return (lambda _band, pair: D[int(pair)])

def positiveThreshold(x):
    return (1.0 if (0.0 < x) else 0.0)

def requiredCohorts(d, cMinus, eta, R):
    return _rt.rdiv(d, ((((2.0 * cMinus) * _rt.lpow(eta, 2.0)) * R)))

def recoveredVariance(predictableVariance, estimationNoise):
    return (predictableVariance * (_rt.rdiv(predictableVariance, ((predictableVariance + estimationNoise)))))

def perSitePrecisionTrace(decay, m):
    return _rt.rdiv(((1.0 + (((m - 1.0)) * ldWhiteningGain(decay)))), m)

def ababFinite(Eα, Eβ, Eα2, Eβ2, m):
    return ((((2.0 * ((1.0 - _rt.rdiv(1.0, m)))) * Eα2) * Eβ2) + (((4.0 * ((1.0 - _rt.rdiv(2.0, m)))) * _rt.lpow(Eα, 2.0)) * _rt.lpow(Eβ, 2.0)))

def scalarPermeability(covariance, covarianceDerivative):
    return ((_rt.rdiv(1.0, 2.0)) * _rt.lpow((_rt.rdiv(covarianceDerivative, covariance)), 2.0))

def centeredSquareVarianceFromMoments(secondMoment, fourthMoment):
    return (fourthMoment - _rt.lpow(secondMoment, 2.0))

def covarianceScoreInformationFromMoments(covariance, covarianceDerivative, secondMoment, fourthMoment):
    return (_rt.lpow((_rt.rdiv(covarianceDerivative, ((2.0 * _rt.lpow(covariance, 2.0))))), 2.0) * centeredSquareVarianceFromMoments(secondMoment, fourthMoment))

def momentPermeability(response, noiseVariance):
    return scaledSquare(response, noiseVariance)

def covarianceMomentPermeability(covarianceDerivative, secondMoment, fourthMoment):
    return _rt.rdiv(_rt.lpow(covarianceDerivative, 2.0), centeredSquareVarianceFromMoments(secondMoment, fourthMoment))

def binaryOrientationArrowPermeability(θ):
    return momentPermeability(1.0, (binaryOrientationArrowVariance(θ)))

def totalBinaryOrientationArrowPermeability(m, θ):
    return (m * binaryOrientationArrowPermeability(θ))

def threeCycleOrientationArrowPermeability(θ):
    return momentPermeability((_rt.rdiv(1.0, 3.0)), ((_rt.lpow((_rt.rdiv(1.0, 3.0)), 2.0) * ((1.0 - _rt.lpow(θ, 2.0))))))

def totalCovarianceMomentInformation(m, covarianceDerivative, secondMoment, fourthMoment):
    return (m * covarianceMomentPermeability(covarianceDerivative, secondMoment, fourthMoment))

def replicatesForEqualPermeability(sourceReplicates, sourcePermeability, targetPermeability):
    return _rt.rdiv((sourceReplicates * sourcePermeability), targetPermeability)

def diagonalCovarianceMomentPermeability(covarianceDerivative, secondMoment, fourthMoment):
    return sum((covarianceMomentPermeability((covarianceDerivative[int(i)]), (secondMoment[int(i)]), (fourthMoment[int(i)]))) for i in range(int(len(covarianceDerivative))))

def covarianceMomentPermeabilityWithPrecision(precision, response):
    return sum((sum((_rt.mul(_rt.mul(response[int(i)], precision[int(i)][int(j)]), response[int(j)])) for j in range(int(len(precision))))) for i in range(int(len(precision))))

def twoChannelMomentNoiseDet(firstNoise, secondNoise, sharedNoise):
    return ((firstNoise * secondNoise) - _rt.lpow(sharedNoise, 2.0))

def twoChannelMomentNoisePrecision(firstNoise, secondNoise, sharedNoise):
    det = twoChannelMomentNoiseDet(firstNoise, secondNoise, sharedNoise)
    return twoChannelMomentPrecision((_rt.rdiv(secondNoise, det)), (_rt.rdiv(firstNoise, det)), (_rt.rdiv((-sharedNoise), det)))

def twoChannelConditionalMomentResponse(firstNoise, sharedNoise, firstResponse, secondResponse):
    return (secondResponse - ((_rt.rdiv(sharedNoise, firstNoise)) * firstResponse))

def twoChannelConditionalMomentNoise(firstNoise, secondNoise, sharedNoise):
    return (secondNoise - _rt.rdiv(_rt.lpow(sharedNoise, 2.0), firstNoise))

def informationPerUnitCost(information, cost):
    return ratio(information, cost)

def informationAtBudget(budget, information, cost):
    return (budget * informationPerUnitCost(information, cost))

def twoChannelMomentInnovationInformation(firstNoise, secondNoise, sharedNoise, firstResponse, secondResponse):
    return _rt.rdiv(_rt.lpow(twoChannelConditionalMomentResponse(firstNoise, sharedNoise, firstResponse, secondResponse), 2.0), twoChannelConditionalMomentNoise(firstNoise, secondNoise, sharedNoise))

def diagonalPermeability(covariance, covarianceDerivative):
    return sum((scalarPermeability((covariance[int(i)]), (covarianceDerivative[int(i)]))) for i in range(int(len(covariance))))

def multivariateGaussianPermeability(whitenedCovarianceDerivative):
    return _rt.mul((_rt.rdiv(1.0, 2.0)), frobeniusNormSq(whitenedCovarianceDerivative))

def totalMultivariateGaussianInformation(m, whitenedCovarianceDerivative):
    return _rt.mul(m, multivariateGaussianPermeability(whitenedCovarianceDerivative))

def twoChannelWhitenedDerivative(first, second, shared):
    return twoChannelMomentPrecision(first, second, shared)

def totalGaussianInformation(m, covariance, covarianceDerivative):
    return (m * scalarPermeability(covariance, covarianceDerivative))

def covarianceTangentEstimatorVarianceFromMoments(m, covarianceDerivative, secondMoment, fourthMoment):
    return _rt.rdiv(centeredSquareVarianceFromMoments(secondMoment, fourthMoment), ((m * _rt.lpow(covarianceDerivative, 2.0))))

def gaussianCovarianceTangentEstimatorVariance(m, covariance, covarianceDerivative):
    return covarianceTangentEstimatorVarianceFromMoments(m, covarianceDerivative, covariance, ((3.0 * _rt.lpow(covariance, 2.0))))

def gaussianCovarianceHalfSquaredRisk(m, covariance, covarianceDerivative):
    return ((_rt.rdiv(1.0, 2.0)) * gaussianCovarianceTangentEstimatorVariance(m, covariance, covarianceDerivative))

def lagSensitivityMatrix(lag, covarianceDerivative):
    return (lambda i, j: covarianceDerivative((lag(i)), j))

def lagObservationDerivative(lag, covarianceDerivative, tangent):
    return _rt._proj((lagSensitivityMatrix(lag, covarianceDerivative)), 'mulVec')(tangent)

def lagCompletionPermeability(covariance, lag, covarianceDerivative, tangent):
    return diagonalPermeability(covariance, (lagObservationDerivative(lag, covarianceDerivative, tangent)))

def quadraticChannel(θ):
    return _rt.lpow(θ, 2.0)

def hweMellinDrift(q):
    return ((_rt.lpow(((1.0 - (2.0 * q))), 2.0) * _rt.rlog((_rt.rdiv(_rt.lpow(((1.0 - (2.0 * q))), 2.0), (((2.0 * q) * ((1.0 - q)))))))) + (((4.0 * q) * ((1.0 - q))) * _rt.rlog(2.0)))

def maxSafeEpistaticOrder(N, q):
    return _rt.rdiv(_rt.rlog(N), hweMellinDrift(q))

def hweLatticeCondition(q):
    return (_rt.lpow(((1.0 - (2.0 * q))), 2.0) == ((4.0 * q) * ((1.0 - q))))

def latticeCriticalMaf():
    return _rt.rdiv(((2.0 - _rt.rsqrt(2.0))), 4.0)

def hweMellinJetVariance(q):
    return ((((((2.0 * q) * ((1.0 - q))) * _rt.lpow((_rt.rlog((_rt.rdiv((2.0 * q), ((1.0 - q)))))), 2.0)) + (_rt.lpow(((1.0 - (2.0 * q))), 2.0) * _rt.lpow((_rt.rlog((_rt.rdiv(_rt.lpow(((1.0 - (2.0 * q))), 2.0), (((2.0 * q) * ((1.0 - q)))))))), 2.0))) + (((2.0 * q) * ((1.0 - q))) * _rt.lpow((_rt.rlog((_rt.rdiv((2.0 * ((1.0 - q))), q)))), 2.0))) - _rt.lpow(hweMellinDrift(q), 2.0))

def hardCallLatticeSpan():
    return _rt.rlog((_rt.rdiv(((1.0 - latticeCriticalMaf())), latticeCriticalMaf())))

def hardCallLatticeIndex(*_a):
    if len(_a) < 1:
        return lambda *_b: hardCallLatticeIndex(*(_a + _b))
    _e, = _a[:1]
    _t = [(-1.0), 0.0, 1.0]
    return _t[_rt._ix(_e, 3, 'hardCallLatticeIndex')]

def chiSquareBudget(P, densityRatio):
    return P(((lambda ω: _rt.lpow((_rt.sub(densityRatio[int(ω)], 1.0)), 2.0))))

def weightedResidualMoment(P, densityRatio, X, residual):
    return rawCrossMoment(P, X, ((lambda ω: _rt.mul((_rt.sub(densityRatio[int(ω)], 1.0)), residual[int(ω)]))))

def coefficientEnergy(B, x):
    return dot(x, (_rt.mulVec(B, x)))

def detectionWeight(s):
    return _rt.rinv(s)

def reconstructionWeight(s):
    return identifiedWith(s)

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

def quadraticRisk(outcomeSecondMoment, B, b, w):
    return _rt.add(_rt.sub(outcomeSecondMoment, _rt.mul(2.0, dot(w, b))), dot(w, (_rt.mulVec(B, w))))

def quadraticCoefficientDistance(B, w, v):
    return dot(((lambda i: _rt.sub(w[int(i)], v[int(i)]))), (_rt.mulVec(B, ((lambda i: _rt.sub(w[int(i)], v[int(i)]))))))

def markovPoissonKernel(lam, x):
    return _rt.rdiv(((1.0 - _rt.lpow(lam, 2.0))), (((1.0 + _rt.lpow(lam, 2.0)) - ((2.0 * lam) * x))))

def twoStatePersistence(a, b):
    return ((1.0 - a) - b)

def rawCrossMoment(E, X, Y):
    return (lambda i: E(((lambda ω: _rt.mul(X[int(ω)][int(i)], Y[int(ω)])))))

def optimalReadout(P, b):
    return _rt.rdiv(_rt._proj(P, 'crossSpectrum')(b), _rt._proj(P, 'featureSpectrum')(b))

def Descent_Spectral_FiniteSpectralModel_risk(P, readout):
    return sum(((_rt.add(_rt.sub(_rt.mul(_rt._proj(P, 'featureSpectrum')(b), _rt.lpow(readout[int(b)], 2.0)), _rt.mul(_rt.mul(2.0, _rt._proj(P, 'crossSpectrum')(b)), readout[int(b)])), _rt._proj(P, 'targetPower')(b)))) for b in range(int(len(readout))))

def degradation(source, target):
    return (Descent_Spectral_FiniteSpectralModel_risk(target, (optimalReadout(source))) - Descent_Spectral_FiniteSpectralModel_risk(target, (optimalReadout(target))))

def degradationProfile(source, target, b):
    return (_rt.lpow(((optimalReadout(source, b) - optimalReadout(target, b))), 2.0) * _rt._proj(target, 'featureSpectrum')(b))

def rightWhiten(inverseColor, data):
    return rightTransform(inverseColor, data)

def rightColor(color, data):
    return rightTransform(color, data)

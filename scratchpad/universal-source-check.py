from pathlib import Path
import sys

root = Path('/projects/standard/hsiehph/sauer354/descent-universal-20260907')
sys.path.insert(0, str(root / 'validation/code'))
import check

modules = [
    'UniversalMetricIdentification', 'EmpiricalAUCComparison', 'ExactFiniteHistoryLaw',
    'ExactMetricEvaluation', 'DemographyAccuracyFiber', 'MomentAUCNonidentifiability',
    'MeasurePortabilityLaw', 'FiniteDemographicSampling', 'PartialMetricMixture',
]
paths = [root / 'Descent/Portability' / (module + '.lean') for module in modules]
paths.append(root / 'validation/code/CheckUniversalPortabilityAxioms.lean')
errors = [error for path in paths for error in check.style_check_file(path)]
print('NEW_MODULE_STYLE_FILES', len(paths), 'ERRORS', len(errors))
for error in errors:
    print(error)
raise SystemExit(bool(errors))

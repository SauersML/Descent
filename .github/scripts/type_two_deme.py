from pathlib import Path

p = Path('Descent/Coalescent/TwoDemeLDClosedForm.lean')
s = p.read_text()

def rep(old: str, new: str) -> None:
    global s
    c = s.count(old)
    assert c == 1, f'expected 1 match, got {c}: {old!r}'
    s = s.replace(old, new, 1)

rep('(theta : ℝ) (coordinate : TwoDemeLDCoordinate) : ℝ :=\n  theta * publishedTwoDemeLDForcing coordinate',
    '(theta : Descent.Core.Theta) (coordinate : TwoDemeLDCoordinate) : ℝ :=\n  theta.value * publishedTwoDemeLDForcing coordinate')
rep('noncomputable def publishedTwoDemeLDOperatorAtMutation (theta rho M : ℝ) :',
    'noncomputable def publishedTwoDemeLDOperatorAtMutation\n    (theta : Descent.Core.Theta) (rho : Descent.Core.Rho) (M : ℝ) :')
rep('  publishedTwoDemeLDDrift + theta • publishedTwoDemeLDMutation +\n    rho • publishedTwoDemeLDRecombination + M • publishedTwoDemeLDMigration',
    '  publishedTwoDemeLDDrift + theta.value • publishedTwoDemeLDMutation +\n    rho.value • publishedTwoDemeLDRecombination + M • publishedTwoDemeLDMigration')
rep('noncomputable def publishedTwoDemeLDOperator (rho M : ℝ) :',
    'noncomputable def publishedTwoDemeLDOperator (rho : Descent.Core.Rho) (M : ℝ) :')
rep('  publishedTwoDemeLDOperatorAtMutation 1 rho M',
    '  publishedTwoDemeLDOperatorAtMutation (Descent.Core.Theta.ofScaled 1) rho M')

for name in [
    'publishedTwoDemeLDCoordinateValueAtMutation',
    'publishedTwoDemeWithinDAtMutation',
    'publishedTwoDemeCrossDAtMutation',
    'publishedTwoDemeDCorrelationAtMutation',
]:
    rep(f'noncomputable def {name}\n    (theta rho M : ℝ)',
        f'noncomputable def {name}\n    (theta : Descent.Core.Theta) (rho : Descent.Core.Rho) (M : ℝ)')

for name in [
    'publishedTwoDemeLDCoordinateValue',
    'publishedTwoDemeWithinD',
    'publishedTwoDemeCrossD',
    'publishedTwoDemeTargetWithinD',
    'publishedTwoDemeDCorrelation',
]:
    rep(f'noncomputable def {name} (rho M : ℝ)',
        f'noncomputable def {name} (rho : Descent.Core.Rho) (M : ℝ)')

rep('theorem publishedTwoDemeLD_normalized_mutation (rho M : ℝ) :',
    'theorem publishedTwoDemeLD_normalized_mutation\n    (rho : Descent.Core.Rho) (M : ℝ) :')
rep('publishedTwoDemeLDOperator rho M = publishedTwoDemeLDOperatorAtMutation 1 rho M ∧\n      publishedTwoDemeLDForcing = publishedTwoDemeLDForcingAtMutation 1',
    'publishedTwoDemeLDOperator rho M =\n      publishedTwoDemeLDOperatorAtMutation (Descent.Core.Theta.ofScaled 1) rho M ∧\n      publishedTwoDemeLDForcing =\n        publishedTwoDemeLDForcingAtMutation (Descent.Core.Theta.ofScaled 1)')
rep('theorem publishedTwoDemeDCorrelationAtMutation_eq_rational (theta rho M : ℝ)',
    'theorem publishedTwoDemeDCorrelationAtMutation_eq_rational\n    (theta : Descent.Core.Theta) (rho : Descent.Core.Rho) (M : ℝ)')
rep('theorem publishedTwoDemeDCorrelation_eq_at_normalized_mutation (rho M : ℝ) :',
    'theorem publishedTwoDemeDCorrelation_eq_at_normalized_mutation\n    (rho : Descent.Core.Rho) (M : ℝ) :')
rep('publishedTwoDemeDCorrelationAtMutation 1 rho M',
    'publishedTwoDemeDCorrelationAtMutation (Descent.Core.Theta.ofScaled 1) rho M')
rep('(fun row ↦ -publishedTwoDemeLDForcingAtMutation 1 row) =',
    '(fun row ↦ -publishedTwoDemeLDForcingAtMutation\n        (Descent.Core.Theta.ofScaled 1) row) =')

rep('def PublishedTwoDemeOperatorNonsingular (rho migration : ℝ) : Prop :=',
    'def PublishedTwoDemeOperatorNonsingular\n    (rho : Descent.Core.Rho) (migration : ℝ) : Prop :=')
rep('def PublishedTwoDemeWithinNumeratorNonzero (rho migration : ℝ) : Prop :=',
    'def PublishedTwoDemeWithinNumeratorNonzero\n    (rho : Descent.Core.Rho) (migration : ℝ) : Prop :=')
rep('structure PublishedTwoDemeLDPoint where\n  rho : ℝ\n  migration : ℝ\n  rho_nonneg : 0 ≤ rho',
    'structure PublishedTwoDemeLDPoint where\n  rho : Descent.Core.Rho\n  migration : ℝ\n  rho_nonneg : 0 ≤ rho.value')

rep('theorem publishedTwoDemeCrossD_eq_rational (rho M : ℝ) :',
    'theorem publishedTwoDemeCrossD_eq_rational\n    (rho : Descent.Core.Rho) (M : ℝ) :')
rep('theorem publishedTwoDemeDCorrelation_eq_rational (rho M : ℝ)',
    'theorem publishedTwoDemeDCorrelation_eq_rational\n    (rho : Descent.Core.Rho) (M : ℝ)')
rep('publishedTwoDemeLDOperator 0 M =',
    'publishedTwoDemeLDOperator (Descent.Core.Rho.ofScaled 0) M =')
rep('theorem publishedTwoDemeLDOperator_zero_migration (rho : ℝ) :\n    publishedTwoDemeLDOperator rho 0 =\n      publishedTwoDemeLDBase + rho • publishedTwoDemeLDRecombination',
    'theorem publishedTwoDemeLDOperator_zero_migration (rho : Descent.Core.Rho) :\n    publishedTwoDemeLDOperator rho 0 =\n      publishedTwoDemeLDBase + rho.value • publishedTwoDemeLDRecombination')

p.write_text(s)

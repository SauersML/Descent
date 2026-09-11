/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DriftOperatorCoordinates

/-! Axiom audit of the drift operator of NOTE1 equation (7). -/

open Descent.Portability.DriftOperatorCoordinates

#print axioms driftOperator
#print axioms fieldOperator
#print axioms driftOperator_add
#print axioms driftOperator_C_mul
#print axioms driftOperator_C
#print axioms driftOperator_mul
#print axioms driftOperator_X_zero
#print axioms driftOperator_X_one
#print axioms driftOperator_X_two
#print axioms driftOperator_linkage_sq
#print axioms driftOperator_dzObservable
#print axioms coordinates
#print axioms covariance_chainRule
#print axioms JetRepresentation.const
#print axioms JetRepresentation.add
#print axioms JetRepresentation.smul
#print axioms JetRepresentation.mul
#print axioms leftSlot
#print axioms rightSlot
#print axioms linkageSlot
#print axioms JetRepresentation.leftFrequency
#print axioms JetRepresentation.rightFrequency
#print axioms JetRepresentation.linkage
#print axioms heterozygosityPolynomial
#print axioms rightHeterozygosityPolynomial
#print axioms featurePolynomial
#print axioms JetRepresentation.heterozygosity
#print axioms JetRepresentation.rightHeterozygosity
#print axioms JetRepresentation.coordinate
#print axioms coordinateJet_driftAt_eq_driftOperator
#print axioms rightHeterozygosityJet_driftAt_eq_driftOperator
#print axioms lowOrderLDDrift_eq_driftOperator
#print axioms enlargedGenerator_stored_driftRow

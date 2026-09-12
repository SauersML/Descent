/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCorrelationSeries

/-! Axiom audit of EndToEndCorrelationSeries. -/

open Descent.Portability.EndToEndCorrelationSeries

#print axioms seriesTermPolynomial
#print axioms polynomialFunction_seriesTermPolynomial
#print axioms totalDegree_seriesTermPolynomial_le
#print axioms expectedSquaredCorrelation
#print axioms getD_squaredCorrelation_stateLaw
#print axioms measurable_correlationNumerator
#print axioms measurable_correlationDenominator
#print axioms expectedSquaredCorrelation_eq_tsum
#print axioms integral_seriesTerm_historyEventKernel
#print axioms expectedSquaredCorrelation_historyEventKernel
#print axioms expectedSquaredCorrelation_eq_of_moments_eq
#print axioms integral_seriesTerm_rateHistoryKernel
#print axioms expectedSquaredCorrelation_rateHistoryKernel

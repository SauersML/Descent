/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderGaussianQuadrant

/-! Axiom audit of CylinderGaussianQuadrant. -/

open Descent.Portability.CylinderGaussianQuadrant

#print axioms angularDraw_mem_unitInterval
#print axioms boxMuller_mem_quadrant_iff
#print axioms interlacedDraw
#print axioms interlacedDraw_eq_truncatedDraw
#print axioms interlacedDraw_zero_eq
#print axioms interlacedDraw_one_eq
#print axioms interlacedDraw_zero_prefixOf
#print axioms interlacedDraw_one_prefixOf
#print axioms interlacedDraw_take
#print axioms interlacedDraw_succ_bounds
#print axioms measurePreserving_oddBits
#print axioms ae_uniformDraw_ne
#print axioms quadrantIndicator
#print axioms quadrantIndicator_eq
#print axioms quadrantIndicator_eq_indicator
#print axioms gaussianPair_preimage_quadrant
#print axioms quadrantIndicator_nonneg
#print axioms quadrantIndicator_le_one
#print axioms quadrantLower
#print axioms quadrantUpper
#print axioms cast_add_slack
#print axioms cast_quarter
#print axioms slack_lt_one_iff
#print axioms slack_lt_quarter_iff
#print axioms quarter_le_iff
#print axioms quadrantEvaluator
#print axioms integral_quadrantIndicator
#print axioms quadrant_certificate
#print axioms tendsto_quadrant_certificate
#print axioms standardGaussianPair_quadrant

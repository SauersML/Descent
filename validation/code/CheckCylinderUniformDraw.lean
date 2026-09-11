/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderUniformDraw

/-! Axiom audit of CylinderUniformDraw. -/

open Descent.Portability.CylinderUniformDraw

#print axioms binaryDigit_nonneg
#print axioms binaryDigit_le
#print axioms summable_binaryDigit
#print axioms truncatedDraw_le_uniformDraw
#print axioms uniformDraw_le_truncatedDraw_add
#print axioms wordDraw_prefixOf
#print axioms wordDraw_take
#print axioms wordDraw_succ
#print axioms uniformEvaluator
#print axioms measurableSet_bit_true
#print axioms bitMeasure_real_bit_true
#print axioms binaryDigit_eq_indicator
#print axioms integrable_binaryDigit
#print axioms integral_binaryDigit
#print axioms integrable_truncatedDraw
#print axioms integral_truncatedDraw
#print axioms lowerSum_uniformEvaluator
#print axioms upperSum_uniformEvaluator
#print axioms integral_uniformDraw

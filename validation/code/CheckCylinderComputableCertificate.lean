/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderComputableCertificate

/-! Axiom audit of CylinderComputableCertificate, and kernel evaluations of computed
certificates. -/

open Descent.Portability.CylinderComputableCertificate

#print axioms wordSum
#print axioms cylinderSum
#print axioms sum_wordsOfLength_succ_rat
#print axioms sum_wordsOfLength_eq_wordSum
#print axioms lowerSum_eq_cylinderSum
#print axioms upperSum_eq_cylinderSum
#print axioms computed_bracket
#print axioms tendsto_computed
#print axioms uniformLowerCertificate
#print axioms uniformUpperCertificate
#print axioms uniformEvaluator_lowerSum_eq
#print axioms uniformEvaluator_upperSum_eq
#print axioms cast_uniformLowerCertificate
#print axioms cast_uniformUpperCertificate
#print axioms quadrantLowerCertificate
#print axioms quadrantUpperCertificate
#print axioms quadrantEvaluator_lowerSum_eq
#print axioms quadrantEvaluator_upperSum_eq
#print axioms quadrant_computed_bracket
#print axioms tendsto_quadrant_computed

/-- The uniform draw at stage three: `(1 - 1/8) / 2`. -/
example : uniformLowerCertificate 3 = 7 / 16 := by decide +kernel

/-- The uniform draw at stage three: `(1 + 1/8) / 2`. -/
example : uniformUpperCertificate 3 = 9 / 16 := by decide +kernel

/-- The uniform draw at stage four: `(1 - 1/16) / 2`. -/
example : uniformLowerCertificate 4 = 15 / 32 := by decide +kernel

/-- The quadrant indicator at stage one: half the angular digits lie below one quarter. -/
example : quadrantUpperCertificate 1 = 1 / 2 := by decide +kernel

/-- The quadrant indicator at stage two: no cylinder is yet resolved inside the quadrant. -/
example : quadrantLowerCertificate 2 = 0 := by decide +kernel

/-- The quadrant indicator at stage two: the angular digits below one quarter carry one quarter
of the mass. -/
example : quadrantUpperCertificate 2 = 1 / 4 := by decide +kernel

/-- The quadrant indicator at stage three, over the sixty-four words of length six. -/
example : quadrantUpperCertificate 3 = 1 / 4 := by decide +kernel

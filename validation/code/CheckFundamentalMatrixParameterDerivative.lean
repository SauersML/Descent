/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FundamentalMatrixParameterDerivative

/-! Axiom audit of FundamentalMatrixParameterDerivative. -/

open Descent.Portability.FundamentalMatrixParameterDerivative

#print axioms continuous_blockPath
#print axioms toBlocks₁₁_add
#print axioms toBlocks₂₁_add
#print axioms toBlocks₁₁_one
#print axioms toBlocks₂₁_one
#print axioms toBlocks₁₁_integral
#print axioms toBlocks₂₁_integral
#print axioms toBlocks₁₁_blockPath_mul
#print axioms toBlocks₂₁_blockPath_mul
#print axioms toBlocks₁₁_fundamentalMatrix_blockPath
#print axioms toBlocks₂₁_fundamentalMatrix_blockPath_eq_integral
#print axioms fundamentalMatrix_line_sub
#print axioms norm_fundamentalMatrix_blockLine_sub_le
#print axioms hasDerivAt_fundamentalMatrix_line
#print axioms hasDerivAt_fundamentalMatrix_affinePath
#print axioms hasDerivAt_dotProduct_mulVec_of_apply

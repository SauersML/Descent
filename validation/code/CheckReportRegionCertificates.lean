/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReportRegionCertificates

/-! Axiom audit of ReportRegionCertificates. -/

open Descent.Portability.ReportRegionCertificates

#print axioms pairing_sub
#print axioms pairing_contrast_reportRegion
#print axioms mem_reportRegion_iff
#print axioms reportRegion_nonempty
#print axioms reportRegion_isCompact
#print axioms reportRegion_convex
#print axioms report_contrast_le_dual_value
#print axioms dual_value_le_report_contrast
#print axioms exists_extreme_report_contrast
#print axioms not_mem_reportRegion_iff_separating_contrast
#print axioms exists_feasible_pos_on_active
#print axioms report_identified_iff_invisible_directions_vanish

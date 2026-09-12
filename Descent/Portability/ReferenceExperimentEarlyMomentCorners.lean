/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentAtomTable

assert_below Descent.Decision Descent.Program

/-!
# Corner certificates of the NOTE2 section 9 reference experiment: early migration, moments

The per-context corner accumulators of the early migration population target reports listed in
the theorem names, each rewritten onto the tabled atom law of `ReferenceExperimentAtomTable` and
decided in the kernel for one architecture and environment context.
Their context-mass averages are the population rows of `ReferenceExperimentRows`, and the
values are recorded in `validation/reference_experiment_corners.json`.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model,
so no measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentEarlyMomentCorners

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentCorners ReferenceExperimentAtomTable

theorem early_r2Defined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Defined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Defined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Defined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Weighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, false) =
      82739716563576554120212289717 / 5102838200229873204649682534400 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Weighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, true) =
      36007959895639501574471981286619 / 1998138274887992945085039771648000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Weighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, false) =
      14937859607027033112107892349 / 1791289360311594241095421132800 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_r2Weighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, true) =
      72628546319475248438835091715 / 5354033484707493284149349842944 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, false) =
      1 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, true) =
      1 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, false) =
      1 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, true) =
      1 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, false) =
      10556347684728780086379429726443 / 20411352800919492818598730137600 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, true) =
      3855298618103314677058664633619053 / 7421656449583973796030147723264000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, false) =
      1595805343718953624751705286965 / 3152669274148405864327941193728 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_aucWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, true) =
      10904808560123029256837645708333 / 21416133938829973136597399371776 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, false) =
      110124160767462913150943 / 942852683284894187520000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, true) =
      717069186066460986615173417 / 5279510035363380980613120000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, false) =
      395741452703714808952361 / 9611571516095006874009600 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_slopeWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, true) =
      50307758692410251822159 / 806068672825578959667200 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

end Descent.Portability.ReferenceExperimentEarlyMomentCorners

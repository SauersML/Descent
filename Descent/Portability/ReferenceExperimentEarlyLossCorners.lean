/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentAtomTable

assert_below Descent.Decision Descent.Program

/-!
# Corner certificates of the NOTE2 section 9 reference experiment: early migration, losses and ratio

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

namespace Descent.Portability.ReferenceExperimentEarlyLossCorners

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentCorners ReferenceExperimentAtomTable

theorem early_brier_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, false) =
      2143687403084770636740217 / 8750851466737924177920000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_brier_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, true) =
      7654429129952985000396821 / 30934629113457310433280000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_brier_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, false) =
      33308518895833195266601 / 126715054167268157030400 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_brier_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, true) =
      132912811515734601994219 / 510090332022436685414400 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ece_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, false) =
      169958516579118208382402076023 / 1146991603448273197848330240000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ece_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, true) =
      1361338194576692419860514347619 / 9731192897181783823466102784000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ece_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, false) =
      907593914478083489917052110139 / 5314814585539895001052348416000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ece_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, true) =
      5818571450287285558678272907 / 31097004650625498246807552000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_repairedBrier_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, false) =
      285324777079129799578333785173 / 1359397455938694160412835840000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_repairedBrier_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, true) =
      8849443824058026868911537933 / 41426959970973962637148160000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_repairedBrier_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, false) =
      866079733250430662117384665021 / 3936899692992514815594332160000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_repairedBrier_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, true) =
      6207727378375257961230341341 / 29714915555042142769171660800 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, false) =
      24176450189676116616122240117 / 204113528009194928185987301376 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, true) =
      4199508752136724317099778106735813 / 45412233520181657842841812992000000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, false) =
      1204447361564081895670839434267 / 12056755309789576622757642240000 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

theorem early_ratioWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, true) =
      61277721092998762608592682195 / 585597412389882077953835139072 := by
  rw [tableCornerReport_eq_atomCornerReport]
  decide +kernel

end Descent.Portability.ReferenceExperimentEarlyLossCorners

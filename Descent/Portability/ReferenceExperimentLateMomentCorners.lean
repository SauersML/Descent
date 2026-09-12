/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentCorners

assert_below Descent.Decision Descent.Program

/-!
# Corner certificates of the NOTE2 section 9 reference experiment: late migration, moments

The per-context corner accumulators of the late migration population target reports listed in
the theorem names, each decided in the kernel for one architecture and environment context.
Their context-mass averages are the population rows of `ReferenceExperimentRows`, and the
values are recorded in `validation/reference_experiment_corners.json`.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model,
so no measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentLateMomentCorners

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentCorners

theorem late_r2Defined_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, false) =
      887086120860564100859 / 3743575614109306060800 := by
  decide +kernel

theorem late_r2Defined_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, true) =
      386593398281726697861601 / 1559620884470139401011200 := by
  decide +kernel

theorem late_r2Defined_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, false) =
      401108410080243106183 / 1939590962224677519360 := by
  decide +kernel

theorem late_r2Defined_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, true) =
      53938343310218201845309 / 248683980913633853964288 := by
  decide +kernel

theorem late_r2Weighted_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, false) =
      8626505700564460991087856179419 / 272434861690050452759352495308800 := by
  decide +kernel

theorem late_r2Weighted_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, true) =
      210717142033005539647679254987981 / 6044368281536178658882245309235200 := by
  decide +kernel

theorem late_r2Weighted_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, false) =
      46632437564670815344455156841 / 2820214498823908790296064819200 := by
  decide +kernel

theorem late_r2Weighted_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, true) =
      30715138556525215845240192566305 / 1165506164202262444293261593935872 := by
  decide +kernel

theorem late_aucDefined_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, false) =
      1 := by
  decide +kernel

theorem late_aucDefined_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, true) =
      1 := by
  decide +kernel

theorem late_aucDefined_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, false) =
      1 := by
  decide +kernel

theorem late_aucDefined_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, true) =
      1 := by
  decide +kernel

theorem late_aucWeighted_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, false) =
      133789984949496956495770899814411 / 251478333867738879470171534131200 := by
  decide +kernel

theorem late_aucWeighted_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, true) =
      60136153402489257900204529104292951 / 112252553799957603664955984314368000 := by
  decide +kernel

theorem late_aucWeighted_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, false) =
      2535190223051877294021567182145 / 4963577517930079470921074081792 := by
  decide +kernel

theorem late_aucWeighted_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, true) =
      103357253524459959509585004038876197 / 200467060242789140418440994156969984 := by
  decide +kernel

theorem late_slopeDefined_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, false) =
      887086120860564100859 / 3743575614109306060800 := by
  decide +kernel

theorem late_slopeDefined_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, true) =
      386593398281726697861601 / 1559620884470139401011200 := by
  decide +kernel

theorem late_slopeDefined_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, false) =
      401108410080243106183 / 1939590962224677519360 := by
  decide +kernel

theorem late_slopeDefined_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, true) =
      53938343310218201845309 / 248683980913633853964288 := by
  decide +kernel

theorem late_slopeWeighted_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, false) =
      363052252969491760413958183 / 1661149285834102742712320000 := by
  decide +kernel

theorem late_slopeWeighted_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, true) =
      20104790072897805671254532899 / 79852589284871137331773440000 := by
  decide +kernel

theorem late_slopeWeighted_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, false) =
      30731144929425047005760367 / 423710111001188219695923200 := by
  decide +kernel

theorem late_slopeWeighted_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, true) =
      7223142530508741350718128099 / 67907305721482951055848243200 := by
  decide +kernel

end Descent.Portability.ReferenceExperimentLateMomentCorners

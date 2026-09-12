/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentCorners

assert_below Descent.Decision Descent.Program

/-!
# Corner certificates of the NOTE2 section 9 reference experiment: late migration, losses and ratio

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

namespace Descent.Portability.ReferenceExperimentLateLossCorners

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable
  ReferenceExperimentCorners

theorem late_brier_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, false) =
      3097089741843139056593 / 12430186742525460480000 := by
  decide +kernel

theorem late_brier_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, true) =
      118197901279053429611 / 472024980368916480000 := by
  decide +kernel

theorem late_brier_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, false) =
      131114386199524176571 / 494980680340891238400 := by
  decide +kernel

theorem late_brier_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, true) =
      173295842681135429483 / 664180119820881100800 := by
  decide +kernel

theorem late_ece_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, false) =
      75418769847135750362236954021249 / 551129465456895271566122680320000 := by
  decide +kernel

theorem late_ece_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, true) =
      19557135198661355191615645045529 / 147184292569874480329924804608000 := by
  decide +kernel

theorem late_ece_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, false) =
      9155887993809126472993127787017 / 58573685744804259490764423168000 := by
  decide +kernel

theorem late_ece_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, true) =
      236979882756100320375054542976041 / 1390741621175970837623772020736000 := by
  decide +kernel

theorem late_repairedBrier_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, false) =
      47820084302720355469661994694833 / 217730159192847514692789207040000 := by
  decide +kernel

theorem late_repairedBrier_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, true) =
      3996626838071386170217927781499 / 18170900317268454361719111680000 := by
  decide +kernel

theorem late_repairedBrier_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, false) =
      9951579832334799417036833158303 / 43387915366521673696862535680000 := by
  decide +kernel

theorem late_repairedBrier_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, true) =
      60263629948425656493819751389269 / 278148324235194167524754404147200 := by
  decide +kernel

theorem late_ratioDefined_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, false) =
      887086120860564100859 / 3743575614109306060800 := by
  decide +kernel

theorem late_ratioDefined_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, true) =
      386593398281726697861601 / 1559620884470139401011200 := by
  decide +kernel

theorem late_ratioDefined_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, false) =
      401108410080243106183 / 1939590962224677519360 := by
  decide +kernel

theorem late_ratioDefined_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, true) =
      53938343310218201845309 / 248683980913633853964288 := by
  decide +kernel

theorem late_ratioWeighted_corner_zero_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, false) =
      2667595541796680609872091120219 / 10897394467602018110374099812352 := by
  decide +kernel

theorem late_ratioWeighted_corner_zero_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, true) =
      126611812445030139896090128355079391 / 686860031992747574872982421504000000 := by
  decide +kernel

theorem late_ratioWeighted_corner_one_zero :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, false) =
      580603522530829031822949686009 / 2711744710407604606053908480000 := by
  decide +kernel

theorem late_ratioWeighted_corner_one_one :
    tableCornerReport lateTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, true) =
      26734360594894384452151930418545 / 127477236709622454844575486836736 := by
  decide +kernel

end Descent.Portability.ReferenceExperimentLateLossCorners

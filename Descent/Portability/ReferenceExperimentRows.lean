/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable

assert_below Descent.Decision Descent.Program

/-!
# The population target rows of the NOTE2 section 9 reference experiment

The population rows of the section 9 table for both migration histories: the definedness
probabilities and weighted numerators of the target squared correlation, the target calibration
slope and the target to source squared-correlation ratio; the expected target AUC, Brier loss,
calibration error and repaired Brier loss; and the conditional means of the partial rows. The
early weighted numerator of the target squared correlation is in `ReferenceExperimentTable`, and
the early definedness probability in `ReferenceExperimentLaw`.

Every row is assembled from four per-context certificates. A history report computed from its
tabled terminal law (`early_historyReport_table`, `late_historyReport_table`) is the
context-mass average of its corner accumulators (`tableReport_eq_corners`). Each corner
accumulator is decided in the kernel in its own small lemma, and the row is the norm_num
combination of the four corners with the context masses. The corner values were computed on MSI
from the specified model and are recorded in `validation/reference_experiment_corners.json`,
where their context-mass averages are checked against the reference results; the lemmas here
decide them independently, so the record states nothing the kernel does not check.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentRows

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-- The corner accumulator of a report in one architecture and environment context, computed
from a tabled terminal law. -/
def tableCornerReport (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℚ :=
  ∑ atom, if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalTable entries context terminal *
      report context atom terminal

/-- A tabled history report is the context-mass average of its corner accumulators. -/
theorem tableReport_eq_corners (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    tableReport entries report =
      ∑ context, contextMass context * tableCornerReport entries report context := rfl

/-! ## Corner certificates -/

theorem early_r2Defined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  decide +kernel

theorem early_r2Defined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  decide +kernel

theorem early_r2Defined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  decide +kernel

theorem early_r2Defined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome)
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  decide +kernel

theorem early_r2Weighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, false) =
      82739716563576554120212289717 / 5102838200229873204649682534400 := by
  decide +kernel

theorem early_r2Weighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (false, true) =
      36007959895639501574471981286619 / 1998138274887992945085039771648000 := by
  decide +kernel

theorem early_r2Weighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, false) =
      14937859607027033112107892349 / 1791289360311594241095421132800 := by
  decide +kernel

theorem early_r2Weighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal))
        (true, true) =
      72628546319475248438835091715 / 5354033484707493284149349842944 := by
  decide +kernel

theorem early_aucDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, false) =
      1 := by
  decide +kernel

theorem early_aucDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (false, true) =
      1 := by
  decide +kernel

theorem early_aucDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, false) =
      1 := by
  decide +kernel

theorem early_aucDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal))
        (true, true) =
      1 := by
  decide +kernel

theorem early_aucWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, false) =
      10556347684728780086379429726443 / 20411352800919492818598730137600 := by
  decide +kernel

theorem early_aucWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (false, true) =
      3855298618103314677058664633619053 / 7421656449583973796030147723264000 := by
  decide +kernel

theorem early_aucWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, false) =
      1595805343718953624751705286965 / 3152669274148405864327941193728 := by
  decide +kernel

theorem early_aucWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal))
        (true, true) =
      10904808560123029256837645708333 / 21416133938829973136597399371776 := by
  decide +kernel

theorem early_slopeDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  decide +kernel

theorem early_slopeDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  decide +kernel

theorem early_slopeDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  decide +kernel

theorem early_slopeDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal))
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  decide +kernel

theorem early_slopeWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, false) =
      110124160767462913150943 / 942852683284894187520000 := by
  decide +kernel

theorem early_slopeWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (false, true) =
      717069186066460986615173417 / 5279510035363380980613120000 := by
  decide +kernel

theorem early_slopeWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, false) =
      395741452703714808952361 / 9611571516095006874009600 := by
  decide +kernel

theorem early_slopeWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal))
        (true, true) =
      50307758692410251822159 / 806068672825578959667200 := by
  decide +kernel

theorem early_brier_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, false) =
      2143687403084770636740217 / 8750851466737924177920000 := by
  decide +kernel

theorem early_brier_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (false, true) =
      7654429129952985000396821 / 30934629113457310433280000 := by
  decide +kernel

theorem early_brier_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, false) =
      33308518895833195266601 / 126715054167268157030400 := by
  decide +kernel

theorem early_brier_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetBrier context atom terminal)
        (true, true) =
      132912811515734601994219 / 510090332022436685414400 := by
  decide +kernel

theorem early_ece_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, false) =
      169958516579118208382402076023 / 1146991603448273197848330240000 := by
  decide +kernel

theorem early_ece_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (false, true) =
      1361338194576692419860514347619 / 9731192897181783823466102784000 := by
  decide +kernel

theorem early_ece_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, false) =
      907593914478083489917052110139 / 5314814585539895001052348416000 := by
  decide +kernel

theorem early_ece_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetECE context atom terminal)
        (true, true) =
      5818571450287285558678272907 / 31097004650625498246807552000 := by
  decide +kernel

theorem early_repairedBrier_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, false) =
      285324777079129799578333785173 / 1359397455938694160412835840000 := by
  decide +kernel

theorem early_repairedBrier_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (false, true) =
      8849443824058026868911537933 / 41426959970973962637148160000 := by
  decide +kernel

theorem early_repairedBrier_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, false) =
      866079733250430662117384665021 / 3936899692992514815594332160000 := by
  decide +kernel

theorem early_repairedBrier_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal)
        (true, true) =
      6207727378375257961230341341 / 29714915555042142769171660800 := by
  decide +kernel

theorem early_ratioDefined_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, false) =
      17749001596142659 / 132801140411596800 := by
  decide +kernel

theorem early_ratioDefined_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (false, true) =
      5161535759051312863 / 36617695446800793600 := by
  decide +kernel

theorem early_ratioDefined_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, false) =
      337222347318642229 / 2749892668560506880 := by
  decide +kernel

theorem early_ratioDefined_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal))
        (true, true) =
      4892584425047299 / 37737506808004608 := by
  decide +kernel

theorem early_ratioWeighted_corner_zero_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, false) =
      24176450189676116616122240117 / 204113528009194928185987301376 := by
  decide +kernel

theorem early_ratioWeighted_corner_zero_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (false, true) =
      4199508752136724317099778106735813 / 45412233520181657842841812992000000 := by
  decide +kernel

theorem early_ratioWeighted_corner_one_zero :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, false) =
      1204447361564081895670839434267 / 12056755309789576622757642240000 := by
  decide +kernel

theorem early_ratioWeighted_corner_one_one :
    tableCornerReport earlyTerminalEntries
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal))
        (true, true) =
      61277721092998762608592682195 / 585597412389882077953835139072 := by
  decide +kernel

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

/-! ## The section 9 table rows, early migration -/

/-- NOTE2 section 9, early migration: the target AUC is defined in every study context. -/
theorem early_target_auc_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal)) = 1 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_aucDefined_corner_zero_zero,
    early_aucDefined_corner_zero_one, early_aucDefined_corner_one_zero,
    early_aucDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the expected target AUC, `0.512391474…`. -/
theorem early_target_auc_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal)) =
      8885485933860371266227250683021210326870914248073 /
        17341205659207960216603431259424418943771607040000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_aucWeighted_corner_zero_zero,
    early_aucWeighted_corner_zero_one, early_aucWeighted_corner_one_zero,
    early_aucWeighted_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the definedness probability of the target calibration
slope. -/
theorem early_target_slope_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      371745151991563462629371512245851 / 2820650730645240044657068474368000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_slopeDefined_corner_zero_zero,
    early_slopeDefined_corner_zero_one, early_slopeDefined_corner_one_zero,
    early_slopeDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the weighted numerator of the target calibration slope. -/
theorem early_target_slope_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) =
      449334768997953942927408863086189700870489 /
        5286829155710000514806065290734783692800000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_slopeWeighted_corner_zero_zero,
    early_slopeWeighted_corner_zero_one, early_slopeWeighted_corner_one_zero,
    early_slopeWeighted_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the expected target Brier loss, `0.255445425…`. -/
theorem early_target_brier_expectation :
    historyReport earlyMigration (fun context atom terminal ↦ targetBrier context atom terminal) =
      4747838631071499861573778737378417236699 / 18586508750542970559865073287739473920000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_brier_corner_zero_zero,
    early_brier_corner_zero_one, early_brier_corner_one_zero, early_brier_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the expected exact discrete-score calibration error,
`0.166059662…`. -/
theorem early_target_ece_expectation :
    historyReport earlyMigration (fun context atom terminal ↦ targetECE context atom terminal) =
      188162656489677160227374436976321257824310001 /
        1133102732535427087080295295800273639833600000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_ece_corner_zero_zero,
    early_ece_corner_zero_one, early_ece_corner_one_zero, early_ece_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the expected population-repaired target Brier loss,
`0.212511418…`. -/
theorem early_target_repairedBrier_expectation :
    historyReport earlyMigration
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal) =
      2938635605139492444443736923901855805020693 /
        13828130409826412585342045613569395916800000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_repairedBrier_corner_zero_zero,
    early_repairedBrier_corner_zero_one, early_repairedBrier_corner_one_zero,
    early_repairedBrier_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the definedness probability of the target to source
squared-correlation ratio. -/
theorem early_r2Portability_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      371745151991563462629371512245851 / 2820650730645240044657068474368000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_ratioDefined_corner_zero_zero,
    early_ratioDefined_corner_zero_one, early_ratioDefined_corner_one_zero,
    early_ratioDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, early migration: the weighted numerator of the target to source
squared-correlation ratio. -/
theorem early_r2Portability_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) =
      141098976349223166634209424872318756673924941061549 /
        1379414086527905926320727486545124234163650560000000 := by
  rw [early_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, early_ratioWeighted_corner_zero_zero,
    early_ratioWeighted_corner_zero_one, early_ratioWeighted_corner_one_zero,
    early_ratioWeighted_corner_one_one]
  norm_num [contextMass]

/-! ## The section 9 table rows, late migration -/

/-- NOTE2 section 9, late migration: the probability that the population target squared
correlation is defined, `0.225813526…`. -/
theorem late_target_r2_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_r2Defined_corner_zero_zero,
    late_r2Defined_corner_zero_one, late_r2Defined_corner_one_zero,
    late_r2Defined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the weighted numerator of the population target squared
correlation. -/
theorem late_target_r2_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)) =
      3812873519580893603247741863519992880514238894831140793219 /
        139324810495600373361106867242402958049749336832279052288000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_r2Weighted_corner_zero_zero,
    late_r2Weighted_corner_zero_one, late_r2Weighted_corner_one_zero,
    late_r2Weighted_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the target AUC is defined in every study context. -/
theorem late_target_auc_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal)) = 1 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_aucDefined_corner_zero_zero,
    late_aucDefined_corner_zero_one, late_aucDefined_corner_one_zero,
    late_aucDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the expected target AUC, `0.522178997…`. -/
theorem late_target_auc_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal)) =
      2406428509304410598713910325642032448430250438960580486234781 /
        4608436039469858503482765608787174766260939602913845575680000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_aucWeighted_corner_zero_zero,
    late_aucWeighted_corner_zero_one, late_aucWeighted_corner_one_zero,
    late_aucWeighted_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the definedness probability of the target calibration
slope. -/
theorem late_target_slope_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_slopeDefined_corner_zero_zero,
    late_slopeDefined_corner_zero_one, late_slopeDefined_corner_one_zero,
    late_slopeDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the weighted numerator of the target calibration slope. -/
theorem late_target_slope_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) =
      311176239634324851712931547174306553258238212762654961 /
        2029412797526507798885005541951310136037472416563200000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_slopeWeighted_corner_zero_zero,
    late_slopeWeighted_corner_zero_one, late_slopeWeighted_corner_one_zero,
    late_slopeWeighted_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the expected target Brier loss, `0.257340460…`. -/
theorem late_target_brier_expectation :
    historyReport lateMigration (fun context atom terminal ↦ targetBrier context atom terminal) =
      212316259951461104402550109152394901 / 825040338713732713062192528752640000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_brier_corner_zero_zero,
    late_brier_corner_zero_one, late_brier_corner_one_zero, late_brier_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the expected exact discrete-score calibration error,
`0.153101330…`. -/
theorem late_target_ece_expectation :
    historyReport lateMigration (fun context atom terminal ↦ targetECE context atom terminal) =
      318162736910403747256041937669580038254445669429527905143 /
        2078118704667143986058245674958141579302371754560716800000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_ece_corner_zero_zero,
    late_ece_corner_zero_one, late_ece_corner_one_zero, late_ece_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the expected population-repaired target Brier loss,
`0.220473027…`. -/
theorem late_target_repairedBrier_expectation :
    historyReport lateMigration
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal) =
      916338243951452292443459513241372327978775759856217385861 /
        4156237409334287972116491349916283158604743509121433600000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_repairedBrier_corner_zero_zero,
    late_repairedBrier_corner_zero_one, late_repairedBrier_corner_one_zero,
    late_repairedBrier_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the definedness probability of the target to source
squared-correlation ratio. -/
theorem late_r2Portability_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_ratioDefined_corner_zero_zero,
    late_ratioDefined_corner_zero_one, late_ratioDefined_corner_one_zero,
    late_ratioDefined_corner_one_one]
  norm_num [contextMass]

/-- NOTE2 section 9, late migration: the weighted numerator of the target to source
squared-correlation ratio. -/
theorem late_r2Portability_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) =
      23107737031325490896675390382600584273061283929373675533016183 /
        110826553803318478809971371670093262085027881571131064320000000 := by
  rw [late_historyReport_table, tableReport_eq_corners]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, late_ratioWeighted_corner_zero_zero,
    late_ratioWeighted_corner_zero_one, late_ratioWeighted_corner_one_zero,
    late_ratioWeighted_corner_one_one]
  norm_num [contextMass]

/-! ## The conditional means of the partial rows -/

/-- NOTE2 section 9, early migration: the expected population target squared correlation given
that it is defined, `0.106691987…`. -/
theorem early_target_r2_givenDefined :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)) /
      historyReport earlyMigration
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome) =
      1583384432603307658220675633807421840805820233 /
        14840706246976671789386011627338290109423288320 := by
  rw [early_target_r2_weightedNumerator, early_target_r2_definedProbability]
  norm_num

/-- NOTE2 section 9, early migration: the expected target calibration slope given that it is
defined, `0.644879762…`. -/
theorem early_target_slope_givenDefined :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) /
      historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      449334768997953942927408863086189700870489 /
        696772942034286348284724854799161006489600 := by
  rw [early_target_slope_weightedNumerator, early_target_slope_definedProbability]
  norm_num

/-- NOTE2 section 9, early migration: the expected target to source squared-correlation ratio
given that it is defined, `0.776127739…`. -/
theorem early_r2Portability_givenDefined :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) /
      historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      141098976349223166634209424872318756673924941061549 /
        181798651525464229419978642434894053840435281920000 := by
  rw [early_r2Portability_weightedNumerator, early_r2Portability_definedProbability]
  norm_num

/-- NOTE2 section 9, late migration: the expected population target squared correlation given
that it is defined, `0.121192009…`. -/
theorem late_target_r2_givenDefined :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)) /
      historyReport lateMigration
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome) =
      163953561341978424939652900131359693862112272477739054108417 /
        1352841350028512412623103268701145867702448217858978997075968 := by
  rw [late_target_r2_weightedNumerator, late_target_r2_definedProbability]
  norm_num

/-- NOTE2 section 9, late migration: the expected target calibration slope given that it is
defined, `0.679025495…`. -/
theorem late_target_slope_givenDefined :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) /
      historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      933528718902974555138794641522919659774714638287964883 /
        1374806579761092192133126546204798078409269988087859200 := by
  rw [late_target_slope_weightedNumerator, late_target_slope_definedProbability]
  norm_num

/-- NOTE2 section 9, late migration: the expected target to source squared-correlation ratio
given that it is defined, `0.923344221…`. -/
theorem late_r2Portability_givenDefined :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) /
      historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      993632692346996108557041786451825123741635208963068047919695869 /
        1076123801159043964586559418285002394763311082387824202219520000 := by
  rw [late_r2Portability_weightedNumerator, late_r2Portability_definedProbability]
  norm_num

end Descent.Portability.ReferenceExperimentRows

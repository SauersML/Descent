/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentTable

assert_below Descent.Decision Descent.Program

/-!
# The target table rows of the NOTE2 section 9 reference experiment

The rows of the section 9 table, decided exactly in the kernel from the tabled terminal laws of
`ReferenceExperimentTable`: for both migration histories, the definedness probabilities and
weighted numerators of the target squared correlation, the target calibration slope, the target
to source squared-correlation ratio and the size-three empirical target squared correlation;
the expected target AUC, Brier loss, calibration error and repaired Brier loss; and the
conditional means of the partial rows. Every row first rewrites the history report to the
report of the tabled terminal law (`early_historyReport_table`, `late_historyReport_table`),
so no row repeats the genetic evolution.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentRows

open RationalReportClosure ReferenceExperimentLaw ReferenceExperimentTable

/-- NOTE2 section 9, early migration: the target AUC is defined in every study context. -/
theorem early_target_auc_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal)) = 1 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the expected target AUC, `0.512391474…`. -/
theorem early_target_auc_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal)) =
      8885485933860371266227250683021210326870914248073 /
        17341205659207960216603431259424418943771607040000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the definedness probability of the target calibration
slope. -/
theorem early_target_slope_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      371745151991563462629371512245851 / 2820650730645240044657068474368000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the weighted numerator of the target calibration slope. -/
theorem early_target_slope_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) =
      449334768997953942927408863086189700870489 /
        5286829155710000514806065290734783692800000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the expected target Brier loss, `0.255445425…`. -/
theorem early_target_brier_expectation :
    historyReport earlyMigration (fun context atom terminal ↦ targetBrier context atom terminal) =
      4747838631071499861573778737378417236699 / 18586508750542970559865073287739473920000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the expected exact discrete-score calibration error,
`0.166059662…`. -/
theorem early_target_ece_expectation :
    historyReport earlyMigration (fun context atom terminal ↦ targetECE context atom terminal) =
      188162656489677160227374436976321257824310001 /
        1133102732535427087080295295800273639833600000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the expected population-repaired target Brier loss,
`0.212511418…`. -/
theorem early_target_repairedBrier_expectation :
    historyReport earlyMigration
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal) =
      2938635605139492444443736923901855805020693 /
        13828130409826412585342045613569395916800000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the definedness probability of the target to source
squared-correlation ratio. -/
theorem early_r2Portability_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      371745151991563462629371512245851 / 2820650730645240044657068474368000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the weighted numerator of the target to source
squared-correlation ratio. -/
theorem early_r2Portability_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) =
      141098976349223166634209424872318756673924941061549 /
        1379414086527905926320727486545124234163650560000000 := by
  rw [early_historyReport_table]
  decide +kernel

/-! ## The section 9 table rows, late migration -/

/-- NOTE2 section 9, late migration: the probability that the population target squared
correlation is defined, `0.225813526…`. -/
theorem late_target_r2_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ bitValue (targetR2 context atom terminal).isSome) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the population target squared
correlation. -/
theorem late_target_r2_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)) =
      3812873519580893603247741863519992880514238894831140793219 /
        139324810495600373361106867242402958049749336832279052288000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the target AUC is defined in every study context. -/
theorem late_target_auc_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (targetAUC context atom terminal)) = 1 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the expected target AUC, `0.522178997…`. -/
theorem late_target_auc_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetAUC context atom terminal)) =
      2406428509304410598713910325642032448430250438960580486234781 /
        4608436039469858503482765608787174766260939602913845575680000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the definedness probability of the target calibration
slope. -/
theorem late_target_slope_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (targetSlope context atom terminal)) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the target calibration slope. -/
theorem late_target_slope_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (targetSlope context atom terminal)) =
      311176239634324851712931547174306553258238212762654961 /
        2029412797526507798885005541951310136037472416563200000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the expected target Brier loss, `0.257340460…`. -/
theorem late_target_brier_expectation :
    historyReport lateMigration (fun context atom terminal ↦ targetBrier context atom terminal) =
      212316259951461104402550109152394901 / 825040338713732713062192528752640000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the expected exact discrete-score calibration error,
`0.153101330…`. -/
theorem late_target_ece_expectation :
    historyReport lateMigration (fun context atom terminal ↦ targetECE context atom terminal) =
      318162736910403747256041937669580038254445669429527905143 /
        2078118704667143986058245674958141579302371754560716800000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the expected population-repaired target Brier loss,
`0.220473027…`. -/
theorem late_target_repairedBrier_expectation :
    historyReport lateMigration
        (fun context atom terminal ↦ targetRepairedBrier context atom terminal) =
      916338243951452292443459513241372327978775759856217385861 /
        4156237409334287972116491349916283158604743509121433600000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the definedness probability of the target to source
squared-correlation ratio. -/
theorem late_r2Portability_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ definedIndicator (r2Portability context atom terminal)) =
      2065514693150679375200009835043266343763927265757 /
        9146992777312985872378330267208429098726588416000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the target to source
squared-correlation ratio. -/
theorem late_r2Portability_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ weightedValue (r2Portability context atom terminal)) =
      23107737031325490896675390382600584273061283929373675533016183 /
        110826553803318478809971371670093262085027881571131064320000000 := by
  rw [late_historyReport_table]
  decide +kernel

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


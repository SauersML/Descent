/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentLaw

assert_below Descent.Decision Descent.Program

/-!
# The target table of the NOTE2 section 9 reference experiment

This module completes the executed example of NOTE2 section 9 on the target side.
`ReferenceExperimentLaw` defines the model, the source report law, the learner atoms, the
target deme through its bottleneck and growth generations under both migration histories, and
the shared study context of each history. Here the population target metrics of the frozen
score are evaluated on that context law, and the rows of the section 9 table are decided
exactly by computation in the kernel.

The metrics are rational versions of the corpus metric vocabulary of `ExactMetricEvaluation`:
the calibration slope, the Brier loss, the binary AUC with half-credit ties, the discrete-score
calibration error of NOTE2 (22) and the population-optimal repaired Brier loss of NOTE2 (23),
all under the target population law of a terminal census, together with the ratio of the
target to the source squared correlation and the empirical squared correlation of a
size-three cohort of independent target draws. A partial metric is reported by its
definedness probability and its weighted numerator, whose quotient is the reported mean of
NOTE2 (2).

The genetic evolution of the target deme is decided once per history against a table of the
exact terminal carrier-type law (`early_terminalMass_table`, `late_terminalMass_table`), and
every row is then decided from that table (`historyReport_eq_tableReport`), so no row repeats
the evolution.

Proved here, for both migration histories: the definedness probabilities and weighted
numerators of the target squared correlation, the target calibration slope, the target to
source squared-correlation ratio and the size-three empirical target squared correlation; the
expected target AUC, Brier loss, calibration error and repaired Brier loss; and the conditional
means of the partial rows. These are the exact rationals of the reference results, whose
decimal renderings are the rows of the section 9 table.

Not formalized here: the log-loss certificates of section 9. The full-square range table is in
`ReferenceExperimentRegion`.

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass and metric is a finite sum of products of the supplied rationals, so no
measurement can bear on these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentTable

open RationalReportClosure ReferenceExperimentLaw

section RationalMetrics

variable {State : Type} [Fintype State]

/-- The least-squares calibration slope of a score against a binary outcome, defined exactly
when the score varies, as `FiniteReportLaw.calibrationSlope` is. -/
def rationalSlope (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) : Option ℚ :=
  if 0 < rationalCovariance law score score then
    some (rationalCovariance law score (fun state ↦ bitValue (outcome state)) /
      rationalCovariance law score score)
  else none

/-- The Brier loss of a score against a binary outcome, the corpus
`FiniteReportLaw.meanSquaredError`. -/
def rationalBrier (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) : ℚ :=
  law.expectation fun state ↦ (score state - bitValue (outcome state)) ^ 2

/-- One case-control comparison with half credit for a tie, as `empiricalAUCComparison`. -/
def comparisonValue (caseRisk controlRisk : ℚ) : ℚ :=
  if controlRisk < caseRisk then 1 else if caseRisk = controlRisk then 1 / 2 else 0

/-- The population AUC with half-credit ties, defined exactly when both outcome classes carry
mass, as `FiniteReportLaw.binaryAUC` is. -/
def rationalAUC (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) : Option ℚ :=
  if 0 < law.expectation (fun state ↦ bitValue (outcome state)) ∧
      law.expectation (fun state ↦ bitValue (outcome state)) < 1 then
    some ((∑ caseState, ∑ controlState, law.mass caseState * law.mass controlState *
        (if outcome caseState && !outcome controlState then
          comparisonValue (score caseState) (score controlState) else 0)) /
      (law.expectation (fun state ↦ bitValue (outcome state)) *
        (1 - law.expectation (fun state ↦ bitValue (outcome state)))))
  else none

/-- The mass of the score group `value`. -/
def valueGroupMass (law : RationalReportLaw State) (score : State → ℚ) (value : ℚ) : ℚ :=
  law.expectation fun state ↦ if score state = value then 1 else 0

/-- The joint mass of the score group `value` and a case. -/
def valueCaseMass (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) (value : ℚ) : ℚ :=
  law.expectation fun state ↦ if score state = value then bitValue (outcome state) else 0

/-- NOTE2 (22): the exact discrete-score calibration error. -/
def rationalECE (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) : ℚ :=
  ∑ value ∈ Finset.univ.image score,
    |valueCaseMass law score outcome value - value * valueGroupMass law score value|

/-- NOTE2 (23): the population-optimal score-conditional repair of the Brier loss; an empty
score group contributes nothing. -/
def rationalRepairedBrier (law : RationalReportLaw State) (score : State → ℚ)
    (outcome : State → Bool) : ℚ :=
  law.expectation (fun state ↦ bitValue (outcome state)) -
    ∑ value ∈ Finset.univ.image score,
      valueCaseMass law score outcome value ^ 2 / valueGroupMass law score value

end RationalMetrics

/-! ## The population target reports -/

/-- The definedness indicator of a partial report. -/
def definedIndicator (report : Option ℚ) : ℚ := bitValue report.isSome

/-- The weighted value of a partial report: an undefined report contributes nothing. -/
def weightedValue (report : Option ℚ) : ℚ := report.getD 0

/-- The frozen score of a target population draw under a learner atom. -/
def memberScore (atom : LearnerAtom) (terminal : TerminalTypes) (state : Bool × Bool) : ℚ :=
  atomScore atom (memberTypes terminal state.1)

/-- The population target calibration slope. -/
def targetSlope (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    Option ℚ :=
  rationalSlope (targetLaw context terminal) (memberScore atom terminal) (fun state ↦ state.2)

/-- The population target Brier loss. -/
def targetBrier (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) : ℚ :=
  rationalBrier (targetLaw context terminal) (memberScore atom terminal) (fun state ↦ state.2)

/-- The population target AUC. -/
def targetAUC (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    Option ℚ :=
  rationalAUC (targetLaw context terminal) (memberScore atom terminal) (fun state ↦ state.2)

/-- The exact discrete-score calibration error of the target population. -/
def targetECE (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) : ℚ :=
  rationalECE (targetLaw context terminal) (memberScore atom terminal) (fun state ↦ state.2)

/-- The population-repaired target Brier loss. -/
def targetRepairedBrier (context : Bool × Bool) (atom : LearnerAtom)
    (terminal : TerminalTypes) : ℚ :=
  rationalRepairedBrier (targetLaw context terminal) (memberScore atom terminal)
    (fun state ↦ state.2)

/-- The population source squared correlation of the frozen score of a learner atom. -/
def atomSourceR2 (context : Bool × Bool) (atom : LearnerAtom) : Option ℚ :=
  rationalR2 (sourceLaw context)
    (fun draw ↦ atomScore atom (carrier (donor draw.1) 0, carrier (donor draw.1) 1))
    (fun draw ↦ draw.2)

/-- NOTE2 section 9: the ratio of the target to the source squared correlation, defined when
both squared correlations are. -/
def r2Portability (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    Option ℚ :=
  match targetR2 context atom terminal, atomSourceR2 context atom with
  | some target, some source => some (target / source)
  | _, _ => none

/-! ## The size-three evaluation cohort -/

/-- A size-three evaluation cohort: three independent target population draws in draw
order. -/
abbrev Cohort : Type := (Bool × Bool) × (Bool × Bool) × (Bool × Bool)

/-- The mass of a size-three cohort of independent draws from the target population law. -/
def cohortMass (context : Bool × Bool) (terminal : TerminalTypes) (cohort : Cohort) : ℚ :=
  targetMass context terminal cohort.1 * targetMass context terminal cohort.2.1 *
    targetMass context terminal cohort.2.2

/-- The uniform law of three draws: the empirical law of a size-three cohort. -/
def uniformThree : RationalReportLaw (Fin 3) where
  mass := fun _ ↦ 1 / 3
  mass_nonneg := by decide +kernel
  mass_sum := by decide +kernel

/-- The member and outcome of one draw of a cohort. -/
def cohortDraw (cohort : Cohort) : Fin 3 → Bool × Bool
  | 0 => cohort.1
  | 1 => cohort.2.1
  | 2 => cohort.2.2

/-- The empirical squared correlation of a size-three cohort whose two census members carry
the score indices `firstIndex` and `secondIndex`. Indexing by the score alphabet lets equal
cohorts share one evaluation. -/
def cohortR2 (firstIndex secondIndex : Fin 5) (cohort : Cohort) : Option ℚ :=
  rationalR2 uniformThree
    (fun draw ↦ riskValue (if (cohortDraw cohort draw).1 then secondIndex else firstIndex))
    (fun draw ↦ (cohortDraw cohort draw).2)

/-- The score index of a carrier type under a learner atom. -/
def atomScoreIndex (atom : LearnerAtom) (types : Bool × Bool) : Fin 5 :=
  if carrierAt atom.1 types then atom.2.2 else atom.2.1

/-- The probability, within one study context and terminal census, that the size-three
empirical target squared correlation is defined. -/
def cohortDefinedMass (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    ℚ :=
  ∑ cohort : Cohort, cohortMass context terminal cohort *
    definedIndicator
      (cohortR2 (atomScoreIndex atom terminal.1) (atomScoreIndex atom terminal.2) cohort)

/-- The weighted numerator, within one study context and terminal census, of the size-three
empirical target squared correlation. -/
def cohortWeightedR2 (context : Bool × Bool) (atom : LearnerAtom) (terminal : TerminalTypes) :
    ℚ :=
  ∑ cohort : Cohort, cohortMass context terminal cohort *
    weightedValue
      (cohortR2 (atomScoreIndex atom terminal.1) (atomScoreIndex atom terminal.2) cohort)

/-! ## The tabled terminal laws -/

/-- The value that a list of context and terminal entries gives one terminal census, zero when
the census is not listed. -/
def terminalTable (entries : List ((Bool × Bool) × TerminalTypes × ℚ)) (context : Bool × Bool)
    (terminal : TerminalTypes) : ℚ :=
  ((entries.find? fun entry ↦ entry.1 == context && entry.2.1 == terminal).map
    fun entry ↦ entry.2.2).getD 0

/-- The exact terminal carrier-type law of the early migration history, one entry per context and
terminal census, decided from the evolution in `early_terminalMass_table`. -/
def earlyTerminalEntries : List ((Bool × Bool) × TerminalTypes × ℚ) :=
  [ ((false, false), ((false, false), (false, false)),
      8544914678961116312726401 / 90626497062579610694189056),
    ((false, false), ((false, false), (false, true)),
      3353536338950457300555903 / 90626497062579610694189056),
    ((false, false), ((false, false), (true, false)),
      217604119754742200503773 / 8238772460234510063108096),
    ((false, false), ((false, false), (true, true)),
      99127862122969904080419 / 8238772460234510063108096),
    ((false, false), ((false, true), (false, false)),
      3353536338950457300555903 / 90626497062579610694189056),
    ((false, false), ((false, true), (false, true)),
      15257130807321034661979009 / 90626497062579610694189056),
    ((false, false), ((false, true), (true, false)),
      99127862122969904080419 / 8238772460234510063108096),
    ((false, false), ((false, true), (true, true)),
      498439769079619243976157 / 8238772460234510063108096),
    ((false, false), ((true, false), (false, false)),
      217604119754742200503773 / 8238772460234510063108096),
    ((false, false), ((true, false), (false, true)),
      99127862122969904080419 / 8238772460234510063108096),
    ((false, false), ((true, false), (true, false)),
      8410378123032076368372609 / 90626497062579610694189056),
    ((false, false), ((true, false), (true, true)),
      4219063913254388323328127 / 90626497062579610694189056),
    ((false, false), ((true, true), (false, false)),
      99127862122969904080419 / 8238772460234510063108096),
    ((false, false), ((true, true), (false, true)),
      498439769079619243976157 / 8238772460234510063108096),
    ((false, false), ((true, true), (true, false)),
      4219063913254388323328127 / 90626497062579610694189056),
    ((false, false), ((true, true), (true, true)),
      23154281461089064545246081 / 90626497062579610694189056),
    ((false, true), ((false, false), (false, false)),
      42181197718710223776714601 / 480552735663297966590918656),
    ((false, true), ((false, false), (false, true)),
      17126499250906902022526103 / 480552735663297966590918656),
    ((false, true), ((false, false), (true, false)),
      12392060899629598571697303 / 480552735663297966590918656),
    ((false, true), ((false, false), (true, true)),
      5747401831572235938088809 / 480552735663297966590918656),
    ((false, true), ((false, true), (false, false)),
      17126499250906902022526103 / 480552735663297966590918656),
    ((false, true), ((false, true), (false, true)),
      80032325098583450092226409 / 480552735663297966590918656),
    ((false, true), ((false, true), (true, false)),
      5747401831572235938088809 / 480552735663297966590918656),
    ((false, true), ((false, true), (true, true)),
      29424638916495634199960727 / 480552735663297966590918656),
    ((false, true), ((true, false), (false, false)),
      12392060899629598571697303 / 480552735663297966590918656),
    ((false, true), ((true, false), (false, true)),
      5747401831572235938088809 / 480552735663297966590918656),
    ((false, true), ((true, false), (true, false)),
      45145115925351243298293609 / 480552735663297966590918656),
    ((false, true), ((true, false), (true, true)),
      22845322034806289646181527 / 480552735663297966590918656),
    ((false, true), ((true, true), (false, false)),
      5747401831572235938088809 / 480552735663297966590918656),
    ((false, true), ((true, true), (false, true)),
      29424638916495634199960727 / 480552735663297966590918656),
    ((false, true), ((true, true), (true, false)),
      22845322034806289646181527 / 480552735663297966590918656),
    ((false, true), ((true, true), (true, true)),
      126627447390687256790597481 / 480552735663297966590918656),
    ((true, false), ((false, false), (false, false)),
      22790793316455983891931649 / 262459979532834321039622144),
    ((true, false), ((false, false), (false, true)),
      8729845020610392731918847 / 262459979532834321039622144),
    ((true, false), ((false, false), (true, false)),
      7012451573686206968078847 / 262459979532834321039622144),
    ((true, false), ((false, false), (true, true)),
      3159857451894714065738241 / 262459979532834321039622144),
    ((true, false), ((false, true), (false, false)),
      8729845020610392731918847 / 262459979532834321039622144),
    ((true, false), ((false, true), (false, true)),
      1694166208274024234118567 / 11411303457949318306070528),
    ((true, false), ((false, true), (true, false)),
      3159857451894714065738241 / 262459979532834321039622144),
    ((true, false), ((false, true), (true, true)),
      15692204285452872382196223 / 262459979532834321039622144),
    ((true, false), ((true, false), (false, false)),
      7012451573686206968078847 / 262459979532834321039622144),
    ((true, false), ((true, false), (false, true)),
      3159857451894714065738241 / 262459979532834321039622144),
    ((true, false), ((true, false), (true, false)),
      645262584690274809407001 / 6401462915434983439990784),
    ((true, false), ((true, false), (true, true)),
      322432390145111645552103 / 6401462915434983439990784),
    ((true, false), ((true, true), (false, false)),
      3159857451894714065738241 / 262459979532834321039622144),
    ((true, false), ((true, true), (false, true)),
      15692204285452872382196223 / 262459979532834321039622144),
    ((true, false), ((true, true), (true, false)),
      322432390145111645552103 / 6401462915434983439990784),
    ((true, false), ((true, true), (true, true)),
      1763407558409696517430809 / 6401462915434983439990784),
    ((true, true), ((false, false), (false, false)),
      1352976839370541365783201 / 16508286419467857093984256),
    ((true, true), ((false, false), (false, true)),
      536828021352572431767903 / 16508286419467857093984256),
    ((true, true), ((false, false), (true, false)),
      39113568529310165941373 / 1500753310860714281271296),
    ((true, true), ((false, false), (true, true)),
      17941005294183793670019 / 1500753310860714281271296),
    ((true, true), ((false, true), (false, false)),
      536828021352572431767903 / 16508286419467857093984256),
    ((true, true), ((false, true), (false, true)),
      2463262401675492885979809 / 16508286419467857093984256),
    ((true, true), ((false, true), (true, false)),
      17941005294183793670019 / 1500753310860714281271296),
    ((true, true), ((false, true), (true, true)),
      90755298403590077535357 / 1500753310860714281271296),
    ((true, true), ((true, false), (false, false)),
      39113568529310165941373 / 1500753310860714281271296),
    ((true, true), ((true, false), (false, true)),
      17941005294183793670019 / 1500753310860714281271296),
    ((true, true), ((true, false), (true, false)),
      1664452957514921654543009 / 16508286419467857093984256),
    ((true, true), ((true, false), (true, true)),
      838661789517023847653727 / 16508286419467857093984256),
    ((true, true), ((true, true), (false, false)),
      17941005294183793670019 / 1500753310860714281271296),
    ((true, true), ((true, true), (false, true)),
      90755298403590077535357 / 1500753310860714281271296),
    ((true, true), ((true, true), (true, false)),
      838661789517023847653727 / 16508286419467857093984256),
    ((true, true), ((true, true), (true, true)),
      4630095293699816350866081 / 16508286419467857093984256)]

/-- The exact terminal carrier-type law of the late migration history, one entry per context and
terminal census, decided from the evolution in `late_terminalMass_table`. -/
def lateTerminalEntries : List ((Bool × Bool) × TerminalTypes × ℚ) :=
  [ ((false, false), ((false, false), (false, false)),
      849884683714995712529417543 / 43546031838569502938557841408),
    ((false, false), ((false, false), (false, true)),
      85458651450092317494597213 / 3349694756813038687581372416),
    ((false, false), ((false, false), (true, false)),
      798738916427871540022165689 / 43546031838569502938557841408),
    ((false, false), ((false, false), (true, true)),
      120881659455715982660078499 / 3349694756813038687581372416),
    ((false, false), ((false, true), (false, false)),
      85458651450092317494597213 / 3349694756813038687581372416),
    ((false, false), ((false, true), (false, true)),
      4028963646524075028152448327 / 43546031838569502938557841408),
    ((false, false), ((false, true), (true, false)),
      1452155238936210552387049287 / 43546031838569502938557841408),
    ((false, false), ((false, true), (true, true)),
      455063352223453371797444811 / 3958730167142682085323440128),
    ((false, false), ((true, false), (false, false)),
      798738916427871540022165689 / 43546031838569502938557841408),
    ((false, false), ((true, false), (false, true)),
      1452155238936210552387049287 / 43546031838569502938557841408),
    ((false, false), ((true, false), (true, false)),
      1763473567782731202626795847 / 43546031838569502938557841408),
    ((false, false), ((true, false), (true, true)),
      3168592169441832768343830201 / 43546031838569502938557841408),
    ((false, false), ((true, true), (false, false)),
      120881659455715982660078499 / 3349694756813038687581372416),
    ((false, false), ((true, true), (false, true)),
      455063352223453371797444811 / 3958730167142682085323440128),
    ((false, false), ((true, true), (true, false)),
      3168592169441832768343830201 / 43546031838569502938557841408),
    ((false, false), ((true, true), (true, true)),
      10688495458468881290177734983 / 43546031838569502938557841408),
    ((false, true), ((false, false), (false, false)),
      126762125901724027861019147 / 7268360126907381744687644672),
    ((false, true), ((false, false), (false, true)),
      169877991403757430730644981 / 7268360126907381744687644672),
    ((false, true), ((false, false), (true, false)),
      11359268107413009799171071 / 660760011537034704062513152),
    ((false, true), ((false, false), (true, true)),
      249620929868405286362493963 / 7268360126907381744687644672),
    ((false, true), ((false, true), (false, false)),
      169877991403757430730644981 / 7268360126907381744687644672),
    ((false, true), ((false, true), (false, true)),
      646203233233242757114173963 / 7268360126907381744687644672),
    ((false, true), ((false, true), (true, false)),
      21649290979521954868370433 / 660760011537034704062513152),
    ((false, true), ((false, true), (true, true)),
      842304128454075782393615349 / 7268360126907381744687644672),
    ((false, true), ((true, false), (false, false)),
      11359268107413009799171071 / 660760011537034704062513152),
    ((false, true), ((true, false), (false, true)),
      21649290979521954868370433 / 660760011537034704062513152),
    ((false, true), ((true, false), (true, false)),
      2412105960638012948138403 / 60069091957912245823864832),
    ((false, true), ((true, false), (true, true)),
      58512708793645592321799 / 785683723587437222428672),
    ((false, true), ((true, true), (false, false)),
      249620929868405286362493963 / 7268360126907381744687644672),
    ((false, true), ((true, true), (false, true)),
      842304128454075782393615349 / 7268360126907381744687644672),
    ((false, true), ((true, true), (true, false)),
      58512708793645592321799 / 785683723587437222428672),
    ((false, true), ((true, true), (true, true)),
      1871133409070138422190358027 / 7268360126907381744687644672),
    ((true, false), ((false, false), (false, false)),
      146417920509936349636641441 / 8677583073304334739372507136),
    ((true, false), ((false, false), (false, true)),
      180615294599890806350503263 / 8677583073304334739372507136),
    ((true, false), ((false, false), (true, false)),
      155302987044487786499008863 / 8677583073304334739372507136),
    ((true, false), ((false, false), (true, true)),
      301825906866100936456795809 / 8677583073304334739372507136),
    ((true, false), ((false, true), (false, false)),
      180615294599890806350503263 / 8677583073304334739372507136),
    ((true, false), ((false, true), (false, true)),
      658083316588212826586383009 / 8677583073304334739372507136),
    ((true, false), ((false, true), (true, false)),
      272688895995708234034575009 / 8677583073304334739372507136),
    ((true, false), ((false, true), (true, true)),
      945896854311039073012033887 / 8677583073304334739372507136),
    ((true, false), ((true, false), (false, false)),
      155302987044487786499008863 / 8677583073304334739372507136),
    ((true, false), ((true, false), (false, true)),
      272688895995708234034575009 / 8677583073304334739372507136),
    ((true, false), ((true, false), (true, false)),
      389352498904268144883624609 / 8677583073304334739372507136),
    ((true, false), ((true, false), (true, true)),
      704288490433620646887208287 / 8677583073304334739372507136),
    ((true, false), ((true, true), (false, false)),
      301825906866100936456795809 / 8677583073304334739372507136),
    ((true, false), ((true, true), (false, true)),
      945896854311039073012033887 / 8677583073304334739372507136),
    ((true, false), ((true, true), (true, false)),
      704288490433620646887208287 / 8677583073304334739372507136),
    ((true, false), ((true, true), (true, true)),
      2362492478800222451785607841 / 8677583073304334739372507136),
    ((true, true), ((false, false), (false, false)),
      2390217195985626582044663929 / 154526846797330093069308002304),
    ((true, true), ((false, false), (false, true)),
      1011730431291544339778393389 / 51508948932443364356436000768),
    ((true, true), ((false, false), (true, false)),
      2607388944661470986426968967 / 154526846797330093069308002304),
    ((true, true), ((false, false), (true, true)),
      1714185603296776947434907347 / 51508948932443364356436000768),
    ((true, true), ((false, true), (false, false)),
      1011730431291544339778393389 / 51508948932443364356436000768),
    ((true, true), ((false, true), (false, true)),
      1283370744980934168775416049 / 17169649644147788118812000256),
    ((true, true), ((false, true), (true, false)),
      1600532402050872494667982547 / 51508948932443364356436000768),
    ((true, true), ((false, true), (true, true)),
      1893169397095224504624288527 / 17169649644147788118812000256),
    ((true, true), ((true, false), (false, false)),
      2607388944661470986426968967 / 154526846797330093069308002304),
    ((true, true), ((true, false), (false, true)),
      1600532402050872494667982547 / 51508948932443364356436000768),
    ((true, true), ((true, false), (true, false)),
      6784124309649015979759749241 / 154526846797330093069308002304),
    ((true, true), ((true, false), (true, true)),
      4205259004777149793411783981 / 51508948932443364356436000768),
    ((true, true), ((true, true), (false, false)),
      1714185603296776947434907347 / 51508948932443364356436000768),
    ((true, true), ((true, true), (false, true)),
      1893169397095224504624288527 / 17169649644147788118812000256),
    ((true, true), ((true, true), (true, false)),
      4205259004777149793411783981 / 51508948932443364356436000768),
    ((true, true), ((true, true), (true, true)),
      4813344100147999831186145521 / 17169649644147788118812000256)]

/-- NOTE2 (6) through both generations, early migration: the evolved terminal carrier-type law
is the tabled law. -/
theorem early_terminalMass_table :
    ∀ context terminal,
      terminalMass earlyMigration context terminal =
        terminalTable earlyTerminalEntries context terminal := by
  decide +kernel

/-- NOTE2 (6) through both generations, late migration: the evolved terminal carrier-type law
is the tabled law. -/
theorem late_terminalMass_table :
    ∀ context terminal,
      terminalMass lateMigration context terminal =
        terminalTable lateTerminalEntries context terminal := by
  decide +kernel

/-- A history report computed from a tabled terminal law. -/
def tableReport (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) : ℚ :=
  ∑ context, contextMass context * ∑ atom,
    if atomMass context atom = 0 then 0
    else atomMass context atom * ∑ terminal, terminalTable entries context terminal *
      report context atom terminal

/-- A history report is the report computed from any table that agrees with its terminal
law. -/
theorem historyReport_eq_tableReport (history : History)
    (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (htable : ∀ context terminal,
      terminalMass history context terminal = terminalTable entries context terminal)
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    historyReport history report = tableReport entries report := by
  simp only [historyReport, tableReport, htable]

/-- Every early migration report is computed from the tabled early terminal law. -/
theorem early_historyReport_table (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    historyReport earlyMigration report = tableReport earlyTerminalEntries report :=
  historyReport_eq_tableReport earlyMigration earlyTerminalEntries early_terminalMass_table report

/-- Every late migration report is computed from the tabled late terminal law. -/
theorem late_historyReport_table (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) :
    historyReport lateMigration report = tableReport lateTerminalEntries report :=
  historyReport_eq_tableReport lateMigration lateTerminalEntries late_terminalMass_table report

/-! ## The section 9 table rows, early migration -/

/-- NOTE2 section 9, early migration: the weighted numerator of the population target squared
correlation. -/
theorem early_target_r2_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ weightedValue (targetR2 context atom terminal)) =
      1583384432603307658220675633807421840805820233 /
        112605231553298442964957345840418304829685760000 := by
  rw [early_historyReport_table]
  decide +kernel

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

/-- NOTE2 section 9, early migration: the probability that the size-three empirical target
squared correlation is defined, `0.070854469…`. -/
theorem early_cohort_r2_definedProbability :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      2622808655603568101589881171237344566748039 /
        37016841404766089074607937488631921377280000 := by
  rw [early_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, early migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem early_cohort_r2_weightedNumerator :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      8868146603782821480477967380455098332442037 /
        218735881028163253622683266978279535411200000 := by
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

/-- NOTE2 section 9, late migration: the probability that the size-three empirical target
squared correlation is defined, `0.125309857…`. -/
theorem late_cohort_r2_definedProbability :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      4629489007808721611581847193695585961360948528887668663 /
        36944332527415893085479923110366961409819942303301632000 := by
  rw [late_historyReport_table]
  decide +kernel

/-- NOTE2 section 9, late migration: the weighted numerator of the size-three empirical target
squared correlation. -/
theorem late_cohort_r2_weightedNumerator :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) =
      201309347462493699395313125940107393567746924890805006589 /
        2770824939556191981410994233277522105736495672747622400000 := by
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

/-- NOTE2 section 9, early migration: the expected size-three empirical target squared
correlation given that it is defined, `0.572197010…`. -/
theorem early_cohort_r2_givenDefined :
    historyReport earlyMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) /
      historyReport earlyMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      97549612641611036285257641185006081656862407 /
        170482562614231926603342276130427396838622535 := by
  rw [early_cohort_r2_weightedNumerator, early_cohort_r2_definedProbability]
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

/-- NOTE2 section 9, late migration: the expected size-three empirical target squared
correlation given that it is defined, `0.579788531…`. -/
theorem late_cohort_r2_givenDefined :
    historyReport lateMigration
        (fun context atom terminal ↦ cohortWeightedR2 context atom terminal) /
      historyReport lateMigration
        (fun context atom terminal ↦ cohortDefinedMass context atom terminal) =
      201309347462493699395313125940107393567746924890805006589 /
        347211675585654120868638539527168947102071139666575149725 := by
  rw [late_cohort_r2_weightedNumerator, late_cohort_r2_definedProbability]
  norm_num

end Descent.Portability.ReferenceExperimentTable

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

The genetic evolution of the target deme is decided once per history and context against a
table of the exact terminal carrier-type law (`early_terminalMass_table`,
`late_terminalMass_table`), and any report is then computed from that table
(`historyReport_eq_tableReport`), so no report repeats the evolution.

Proved here: the tabled terminal laws of both migration histories, the rewriting of every
history report to the report of its table, and, as the first row, the weighted numerator of
the early population target squared correlation. The remaining rows of the section 9 table and
their conditional means are decided in `ReferenceExperimentRows`, and the full-square range
table is in `ReferenceExperimentRegion`.

Not formalized here: the log-loss certificates of section 9.

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

theorem early_terminalMass_table_zero_zero :
    ∀ terminal, terminalMass earlyMigration (false, false) terminal =
      terminalTable earlyTerminalEntries (false, false) terminal := by
  decide +kernel

theorem early_terminalMass_table_zero_one :
    ∀ terminal, terminalMass earlyMigration (false, true) terminal =
      terminalTable earlyTerminalEntries (false, true) terminal := by
  decide +kernel

theorem early_terminalMass_table_one_zero :
    ∀ terminal, terminalMass earlyMigration (true, false) terminal =
      terminalTable earlyTerminalEntries (true, false) terminal := by
  decide +kernel

theorem early_terminalMass_table_one_one :
    ∀ terminal, terminalMass earlyMigration (true, true) terminal =
      terminalTable earlyTerminalEntries (true, true) terminal := by
  decide +kernel

/-- NOTE2 (6) through both generations, early migration: the evolved terminal carrier-type law
is the tabled law, decided context by context. -/
theorem early_terminalMass_table :
    ∀ context terminal,
      terminalMass earlyMigration context terminal =
        terminalTable earlyTerminalEntries context terminal := by
  rintro ⟨architecture, environment⟩
  cases architecture <;> cases environment
  exacts [early_terminalMass_table_zero_zero, early_terminalMass_table_zero_one,
    early_terminalMass_table_one_zero, early_terminalMass_table_one_one]

theorem late_terminalMass_table_zero_zero :
    ∀ terminal, terminalMass lateMigration (false, false) terminal =
      terminalTable lateTerminalEntries (false, false) terminal := by
  decide +kernel

theorem late_terminalMass_table_zero_one :
    ∀ terminal, terminalMass lateMigration (false, true) terminal =
      terminalTable lateTerminalEntries (false, true) terminal := by
  decide +kernel

theorem late_terminalMass_table_one_zero :
    ∀ terminal, terminalMass lateMigration (true, false) terminal =
      terminalTable lateTerminalEntries (true, false) terminal := by
  decide +kernel

theorem late_terminalMass_table_one_one :
    ∀ terminal, terminalMass lateMigration (true, true) terminal =
      terminalTable lateTerminalEntries (true, true) terminal := by
  decide +kernel

/-- NOTE2 (6) through both generations, late migration: the evolved terminal carrier-type law
is the tabled law, decided context by context. -/
theorem late_terminalMass_table :
    ∀ context terminal,
      terminalMass lateMigration context terminal =
        terminalTable lateTerminalEntries context terminal := by
  rintro ⟨architecture, environment⟩
  cases architecture <;> cases environment
  exacts [late_terminalMass_table_zero_zero, late_terminalMass_table_zero_one,
    late_terminalMass_table_one_zero, late_terminalMass_table_one_one]

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

end Descent.Portability.ReferenceExperimentTable

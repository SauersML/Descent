/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransferLearningPGS.ImportanceWeighting
import Descent.Portability.TransferLearningPGS.FeatureRepresentation
import Descent.Portability.TransferLearningPGS.FineTuning

assert_below Descent.Decision Descent.Program

/-!
# `TransferLearningPGS` -- the head of a split file

This was 3,558 lines. It is now 4 modules under `TransferLearningPGS/`, chained in the order
the original was written, and this file names the last of them -- so every existing
`import` of this module keeps working and keeps meaning the same thing.
-/

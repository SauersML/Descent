/-
Released under the GNU Affero General Public License v3.0 as described in the file LICENSE.
-/
import Descent.PCCorrectability.Design
import Descent.PCCorrectability.Frequency
import Descent.PCCorrectability.ImitationCapacity
import Descent.PCCorrectability.Nonidentifiability
import Descent.PCCorrectability.EndToEnd

/-!
# Population-structure correctability for PC and mixed-model adjustment

The implementation is split into a linear-algebra core, spectral phase bounds,
the frequency-resolved application diagnostic, and the imitation-capacity
linear program so incremental proof edits compile independently.

`Descent.PCCorrectability.ImitationCapacity` is where the spectral proxy
threshold of `Threshold.lean` acquires a justification rather than a stipulation:
the detection threshold is the value of a linear program over the background
class, its certificate is a constraint index, and the AR(1) whitening gain
`(1+ρ²)/(1-ρ²)` is identified as that certificate's value.  The same file
records why a participation-ratio effective-marker count cannot be substituted
for `M` in `bbpProxyThreshold`.

References:
- Zaidi and Mathieson (2020), eLife 9:e61548.
- Blanc and Berg (2025), Genetics 230(2):iyaf071.
- Blanc, Mawass, and Berg (2025), bioRxiv 2025.12.04.692430.
- Patterson, Price, and Reich (2006), PLoS Genetics 2:e190.
- Johnstone and Paul (2018), Proceedings of the IEEE 106:1277--1292.
- Onatski, Moreira, and Hallin (2013), Annals of Statistics 41:1204--1231.
-/

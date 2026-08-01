import Calibrator.PCCorrectability.Diagnostic
import Calibrator.PCCorrectability.Design
import Calibrator.PCCorrectability.Frequency
import Calibrator.PCCorrectability.Geometry
import Calibrator.PCCorrectability.Nonidentifiability
import Calibrator.PCCorrectability.Overlap

/-!
# Population-structure correctability for PC and mixed-model adjustment

The implementation is split into a linear-algebra core, spectral phase bounds,
and the frequency-resolved application diagnostic so incremental proof edits
compile independently.

References:
- Zaidi and Mathieson (2020), eLife 9:e61548.
- Blanc and Berg (2025), Genetics 230(2):iyaf071.
- Blanc, Mawass, and Berg (2025), bioRxiv 2025.12.04.692430.
- Patterson, Price, and Reich (2006), PLoS Genetics 2:e190.
- Johnstone and Paul (2018), Proceedings of the IEEE 106:1277--1292.
- Onatski, Moreira, and Hallin (2013), Annals of Statistics 41:1204--1231.
-/

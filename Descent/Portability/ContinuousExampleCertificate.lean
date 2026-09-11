/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniformPenetranceArchitecture

assert_below Descent.Decision Descent.Program

/-!
# The eighty-term certificate of the continuous-architecture example

NOTE2 section 9.1 takes a shared penetrance `Θ ~ Uniform(0,1)` and certifies the expected
population squared correlation `E[R²] = 2 log 2 - 1` by the positive replica expansion of
NOTE2 (15)-(18) on the reduced pair `N = θ/2`, `D = 1 - θ/2`.  The note says that at `K = 80`
the certified interval has width below `10^-24`, and `continuous_example_results.json` records
the rational endpoints.  `UniformPenetranceArchitecture` proves the certificate for every `K`
(`replica_certificate`, `integral_replica_tail`, `integral_replica_resolved`); this module is its
instance at `K = 80`, evaluated to the numbers the note reports.

`replicaTail_eighty` gives the unresolved mass `τ_80 = 1/97922991388784963151200256`, and
`replicaTail_eighty_factored` records that the denominator is `2^80 · 81`.
`integral_replica_tail_eighty` and `integral_replica_resolved_eighty` read the same mass and its
complement `H_80 = 97922991388784963151200255/97922991388784963151200256` as integrals over the
parameter range.  `replicaLowerSum_eighty` evaluates the eighty-term lower sum to the file's
`conditional_lower`, and `replicaLowerSum_add_replicaTail_eighty` the upper endpoint to its
`conditional_upper`.  `replica_certificate_eighty` is the bracket of `2 log 2 - 1` between
those two rationals, and `certificate_width_eighty_lt` says their difference is `τ_80`, which
is below `1/10^24`.

Scope: only `K = 80` is evaluated.  The defined-mass upper endpoint `1` of the results file is
the trivial bound and is not restated.  Nothing here reruns `continuous_example.py`; the
endpoints are proved equal to the module's closed forms, which is what makes the file's numbers
certified rather than merely printed.

## Empirical status

None.  The bodies here are rational arithmetic on closed forms already proved for every `K`, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousExampleCertificate

open UniformPenetranceArchitecture

/-- **The unresolved mass at eighty replica terms.**  `τ_80 = 1/97922991388784963151200256`,
the `interval_width` of `continuous_example_results.json`. -/
theorem replicaTail_eighty : replicaTail 80 = 1 / 97922991388784963151200256 := by
  norm_num [replicaTail]

/-- The denominator of `τ_80` is `2^80 · 81`, as the closed form `1/(2^K (K+1))` says. -/
theorem replicaTail_eighty_factored : replicaTail 80 = 1 / (2 ^ 80 * 81) := by
  norm_num [replicaTail]

/-- The unresolved definedness mass after eighty replica terms, as an integral over the
penetrance range: `∫₀¹ (1 - D θ)^80 dθ = τ_80`. -/
theorem integral_replica_tail_eighty :
    ∫ θ in (0:ℝ)..1, (1 - replicaDenominator θ) ^ 80 = 1 / 97922991388784963151200256 := by
  rw [integral_replica_tail]
  norm_num

/-- **The resolved definedness mass at eighty replica terms.**  `H_80 = 1 - τ_80`, the
`defined_mass_lower` of `continuous_example_results.json`. -/
theorem integral_replica_resolved_eighty :
    ∫ θ in (0:ℝ)..1, (1 - (1 - replicaDenominator θ) ^ 80) =
      97922991388784963151200255 / 97922991388784963151200256 := by
  rw [integral_replica_resolved]
  norm_num

/-- **The eighty-term lower sum** is the `conditional_lower` endpoint of
`continuous_example_results.json`. -/
theorem replicaLowerSum_eighty :
    replicaLowerSum 80 =
      5679994527198814242296868376532930356969908379107308733613 /
        14703798706075253105255947079583361818635779183871420006400 := by
  norm_num [replicaLowerSum, Finset.sum_range_succ]

/-- **The eighty-term upper endpoint**, the lower sum plus the unresolved mass, is the
`conditional_upper` endpoint of `continuous_example_results.json`. -/
theorem replicaLowerSum_add_replicaTail_eighty :
    replicaLowerSum 80 + replicaTail 80 =
      5679994527198814242296868526689686166201310747731254593013 /
        14703798706075253105255947079583361818635779183871420006400 := by
  rw [replicaLowerSum_eighty, replicaTail_eighty]
  norm_num

/-- **NOTE2 section 9.1 at `K = 80`.**  The expected population squared correlation
`2 log 2 - 1` lies between the two rational endpoints of `continuous_example_results.json`. -/
theorem replica_certificate_eighty :
    (5679994527198814242296868376532930356969908379107308733613 /
        14703798706075253105255947079583361818635779183871420006400 : ℝ) ≤
        2 * Real.log 2 - 1 ∧
      2 * Real.log 2 - 1 ≤
        5679994527198814242296868526689686166201310747731254593013 /
          14703798706075253105255947079583361818635779183871420006400 := by
  have hcertificate := replica_certificate 80
  rw [replicaLowerSum_add_replicaTail_eighty, replicaLowerSum_eighty] at hcertificate
  exact hcertificate

/-- **The certified width at `K = 80` is below `10^-24`.**  The two endpoints differ by exactly
`τ_80 = 1/(2^80 · 81)`, which is about `1.02 · 10^-26`. -/
theorem certificate_width_eighty_lt :
    (5679994527198814242296868526689686166201310747731254593013 /
        14703798706075253105255947079583361818635779183871420006400 : ℝ) -
      5679994527198814242296868376532930356969908379107308733613 /
        14703798706075253105255947079583361818635779183871420006400 =
        replicaTail 80 ∧
      replicaTail 80 < 1 / 10 ^ 24 := by
  rw [replicaTail_eighty]
  constructor <;> norm_num

end Descent.Portability.ContinuousExampleCertificate

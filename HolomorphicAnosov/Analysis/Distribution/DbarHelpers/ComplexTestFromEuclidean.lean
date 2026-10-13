import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complexTestFromEuclidean

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_complex_test_from_euclidean_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A Euclidean test on the inverse-coordinate image of a complex open set gives a complex-coordinate
test on the original open set by continuous linear pullback and inclusion.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: Compose the continuous coordinate test pullback with the native continuous
test-space inclusion. The inverse-coordinate roundtrip ensures the open-domain inclusion.
-/
noncomputable def complexTestFromEuclidean {n : ℕ} (U : Opens (Fin n → ℂ)) :
    TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤ →L[ℂ]
      TestFunction U ℂ ⊤ :=
  (TestFunction.monoCLM ℂ).comp
    (coordPullbackCLM (complexToOrderedEuclidean n)
      (coordDomain (complexToOrderedEuclidean n).symm U))


end HolomorphicAnosov.Analysis.Distribution

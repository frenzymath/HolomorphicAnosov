import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomainRoundtripLe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLMApply
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complexTestFromEuclidean_apply

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_complex_test_from_euclidean_apply_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The transported complex-coordinate test evaluated at z is the original Euclidean test evaluated at
the ordered coordinate image of z.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: Unfold the continuous-linear-map composition. Native test inclusion preserves
the underlying function because the coordinate roundtrip domain lies in the original domain. The
pullback then evaluates by composition.
-/
theorem complexTestFromEuclidean_apply {n : ℕ} (U : Opens (Fin n → ℂ))
    (φ : TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤)
    (z : Fin n → ℂ) :
    complexTestFromEuclidean U φ z = φ (complexToOrderedEuclidean n z) := by
  change (TestFunction.monoCLM ℂ
    (coordPullbackCLM (complexToOrderedEuclidean n)
      (coordDomain (complexToOrderedEuclidean n).symm U) φ) : TestFunction U ℂ ⊤) z = _
  simp [TestFunction.monoCLM_apply, coordDomain_roundtrip_le, coordPullbackCLM_apply]


end HolomorphicAnosov.Analysis.Distribution

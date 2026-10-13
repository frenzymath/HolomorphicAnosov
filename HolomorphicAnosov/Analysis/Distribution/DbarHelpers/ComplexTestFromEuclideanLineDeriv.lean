import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomainRoundtripLe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLMLineDeriv
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MonoTestLineDeriv
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complexTestFromEuclidean_lineDeriv

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_test_from_euclidean_line_deriv_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Transporting a Euclidean directional derivative in the image of v gives the directional derivative
in v of the transported complex-coordinate test.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Apply the linear-coordinate derivative identity to the pullback. Commute the
native test-space inclusion with the directional derivative using the inverse-coordinate domain
inclusion.
-/
theorem complexTestFromEuclidean_lineDeriv {n : ℕ} (U : Opens (Fin n → ℂ))
    (v : Fin n → ℂ)
    (φ : TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤) :
    complexTestFromEuclidean U (TestFunction.lineDerivCLM ℂ
      (complexToOrderedEuclidean n v) φ) =
    TestFunction.lineDerivCLM ℂ v (complexTestFromEuclidean U φ) := by
  change TestFunction.monoCLM ℂ (coordPullbackCLM _ _ (TestFunction.lineDerivCLM ℂ _ φ)) = _
  rw [← coordPullbackCLM_lineDeriv]
  exact monoTest_lineDeriv _ U (coordDomain_roundtrip_le _ U) v _


end HolomorphicAnosov.Analysis.Distribution

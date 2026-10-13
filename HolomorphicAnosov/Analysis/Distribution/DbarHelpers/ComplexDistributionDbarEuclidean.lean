import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclideanLineDeriv
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleRe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Constructions.SumProd

/-!
# complex_distribution_dbar_euclidean

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_distribution_dbar_euclidean_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The native scalar current dbar equation in complex coordinates becomes the same half-sum of real
and imaginary coordinate test derivatives in ordered Euclidean coordinates.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Test the original distribution equation on the transported Euclidean test. Map
addition and complex scalar multiplication through the transport map. Replace transported test
derivatives by their corresponding complex directions and use the two unit-vector coordinate
formulas.
-/
theorem complex_distribution_dbar_euclidean {n : ℕ} (U : Opens (Fin n → ℂ))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ (j : Fin n) (φ : TestFunction U ℂ ⊤),
      -T ((2 : ℂ)⁻¹ • ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ :
        TestFunction U ℂ ⊤) + Complex.I •
          (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
            TestFunction U ℂ ⊤))) = 0)
    (j : Fin n)
    (φ : TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤) :
    -(T.comp (complexTestFromEuclidean U))
      ((2 : ℂ)⁻¹ • ((TestFunction.lineDerivCLM ℂ
        (EuclideanSpace.single (finSumFinEquiv (Sum.inl j)) 1) φ :
          TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤) +
        Complex.I • (TestFunction.lineDerivCLM ℂ
          (EuclideanSpace.single (finSumFinEquiv (Sum.inr j)) 1) φ :
            TestFunction (coordDomain (complexToOrderedEuclidean n).symm U) ℂ ⊤))) = 0 := by
  rw [← complexToOrderedEuclidean_single_re, ← complexToOrderedEuclidean_single_im]
  simpa only [ContinuousLinearMap.comp_apply, map_smul, map_add,
    complexTestFromEuclidean_lineDeriv] using hT j (complexTestFromEuclidean U φ)


end HolomorphicAnosov.Analysis.Distribution

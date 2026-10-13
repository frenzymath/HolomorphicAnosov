import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToRealArrays
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Constructions.SumProd

/-!
# complexToOrderedEuclidean_im

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_im_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The second coordinate block of the ordered Euclidean image equals the imaginary parts of the
complex tuple.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Expand the composite coordinate definition. The native finite reindexing
evaluated at the image of an index cancels, leaving the defining imaginary-part projection.
-/
theorem complexToOrderedEuclidean_im (n : ℕ) (z : Fin n → ℂ) (j : Fin n) :
    complexToOrderedEuclidean n z (finSumFinEquiv (Sum.inr j)) = (z j).im := by
  simp only [complexToOrderedEuclidean, ContinuousLinearEquiv.trans_apply]
  change (Equiv.piCongrLeft (fun _ : Fin (n+n) ↦ ℝ) finSumFinEquiv)
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin n)
      (fun _ ↦ ℝ)).symm (complexToRealArrays n z)) (finSumFinEquiv (Sum.inr j)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl


end HolomorphicAnosov.Analysis.Distribution

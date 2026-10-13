import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToRealArrays
import Mathlib.Analysis.Distribution.TestFunction

/-!
# complexToOrderedEuclidean_re

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_re_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The first coordinate block of the ordered Euclidean image equals the real parts of the complex
tuple.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Expand the composite coordinate definition. The native finite reindexing
evaluated at the image of an index cancels, leaving the defining real-part projection.
-/
theorem complexToOrderedEuclidean_re (n : ℕ) (z : Fin n → ℂ) (j : Fin n) :
    complexToOrderedEuclidean n z (finSumFinEquiv (Sum.inl j)) = (z j).re := by
  simp only [complexToOrderedEuclidean, ContinuousLinearEquiv.trans_apply]
  change (Equiv.piCongrLeft (fun _ : Fin (n+n) ↦ ℝ) finSumFinEquiv)
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin n)
      (fun _ ↦ ℝ)).symm (complexToRealArrays n z)) (finSumFinEquiv (Sum.inl j)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl


end HolomorphicAnosov.Analysis.Distribution

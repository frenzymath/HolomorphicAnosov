import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToRealArrays
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.RealArraysToFin
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# complexToOrderedEuclidean

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Identify a complex n-tuple with a real Euclidean 2n-tuple by listing all real parts first and then
all imaginary parts.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A (3.1), p.20,
and §3.C (3.14), pp.23–24, real/imaginary coordinates and first derivatives.

Proof/construction: Compose the existing real/imaginary splitting, native concatenation and finite
reindexing, and the continuous linear equivalence from real tuples to Euclidean space.
-/
noncomputable def complexToOrderedEuclidean (n : ℕ) :
    (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n+n)) :=
  ((complexToRealArrays n).trans (realArraysToFin n)).trans
    (EuclideanSpace.equiv (Fin (n+n)) ℝ).symm


end HolomorphicAnosov.Analysis.Distribution

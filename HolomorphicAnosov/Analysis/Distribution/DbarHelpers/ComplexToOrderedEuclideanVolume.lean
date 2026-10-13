import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# complexToOrderedEuclidean_volume

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.
DAG node: `analysis.dbar_helper_complex_to_ordered_euclidean_volume_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The ordered real-coordinate equivalence of complex n-space preserves standard Lebesgue volume,
including n equal to zero.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.

Proof/construction: Each planar real/imaginary equivalence preserves volume. Take its finite
product, regroup the product pairs into two arrays, concatenate and reindex them, and apply the
native tuple-to-Euclidean volume equivalence. Compose the native measure-preserving results.
Coordinate permutations introduce no sign for positive measures.
-/
theorem complexToOrderedEuclidean_volume (n : ℕ) :
    MeasurePreserving (complexToOrderedEuclidean n) := by
  exact (PiLp.volume_preserving_toLp (Fin (n+n))).comp
    (((volume_measurePreserving_piCongrLeft (fun _ : Fin (n+n) ↦ ℝ)
      finSumFinEquiv).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin n ↦ ℝ))).comp
      ((volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).comp
        (volume_preserving_pi (fun _ : Fin n ↦ Complex.volume_preserving_equiv_real_prod))))


end HolomorphicAnosov.Analysis.Distribution

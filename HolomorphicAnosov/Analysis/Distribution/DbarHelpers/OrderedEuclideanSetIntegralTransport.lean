import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanVolume
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# ordered_euclidean_setIntegral_transport

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.
DAG node: `analysis.dbar_helper_ordered_euclidean_set_integral_transport_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Integrating a complex-valued function on a Euclidean set equals integrating its pullback on the
ordered-coordinate preimage with complex-space volume.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.

Proof/construction: Apply the native set-integral change-of-variables theorem to the proved
measure-preserving coordinate equivalence and its measurable embedding. The totalized integral
theorem needs no extra integrability premise.
-/
theorem ordered_euclidean_setIntegral_transport {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n+n)) → ℂ)
    (s : Set (EuclideanSpace ℝ (Fin (n+n)))) :
    (∫ x in s, f x) =
      ∫ z in (complexToOrderedEuclidean n) ⁻¹' s,
        f (complexToOrderedEuclidean n z) := by
  symm
  exact MeasurePreserving.setIntegral_preimage_emb
    (complexToOrderedEuclidean_volume n)
    (complexToOrderedEuclidean n).toHomeomorph.measurableEmbedding f s


end HolomorphicAnosov.Analysis.Distribution

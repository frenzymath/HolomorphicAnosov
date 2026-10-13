import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanSetIntegralTransport
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# ordered_euclidean_open_integral_transport

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.
DAG node: `analysis.dbar_helper_ordered_euclidean_open_integral_transport_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The same coordinate change sends the integral over the inverse-coordinate open domain to the
integral over the original complex open domain.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.

Proof/construction: The preimage under the forward coordinate map of the inverse-coordinate open
domain is the original open set, by the inverse identity. Substitute this equality in the
set-integral transport theorem.
-/
theorem ordered_euclidean_open_integral_transport {n : ℕ}
    (U : Opens (Fin n → ℂ))
    (f : EuclideanSpace ℝ (Fin (n+n)) → ℂ) :
    (∫ x in (coordDomain (complexToOrderedEuclidean n).symm U : Set _), f x) =
      ∫ z in (U : Set _), f (complexToOrderedEuclidean n z) := by
  have hset : (complexToOrderedEuclidean n) ⁻¹'
      (coordDomain (complexToOrderedEuclidean n).symm U : Set _) = (U : Set _) := by
    ext z
    change ((complexToOrderedEuclidean n).symm (complexToOrderedEuclidean n z) ∈ U) ↔ _
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [ordered_euclidean_setIntegral_transport, hset]


end HolomorphicAnosov.Analysis.Distribution

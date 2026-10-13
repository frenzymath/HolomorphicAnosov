import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanVolume
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# ordered_euclidean_integrableOn_transport

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.
DAG node: `analysis.dbar_helper_ordered_euclidean_integrable_on_transport_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Integrability over the inverse-coordinate Euclidean open domain is equivalent to integrability of
the pulled-back function over the original complex open domain.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A p.20 and proof
of (3.24), p.26, product real Lebesgue volume in complex coordinates; §1.C p.8 change of
variables.

Proof/construction: Apply native integrableOn_comp_preimage for the volume-preserving measurable
embedding, then cancel the two coordinate inverses in the domain. This proves integrability
directly rather than inferring it from equality of totalized integrals.
-/
theorem ordered_euclidean_integrableOn_transport {n : ℕ}
    (U : Opens (Fin n → ℂ)) (f : EuclideanSpace ℝ (Fin (n+n)) → ℂ) :
    IntegrableOn f (coordDomain (complexToOrderedEuclidean n).symm U : Set _) volume ↔
      IntegrableOn (fun z ↦ f (complexToOrderedEuclidean n z)) (U : Set _) volume := by
  have hset : (complexToOrderedEuclidean n) ⁻¹'
      (coordDomain (complexToOrderedEuclidean n).symm U : Set _) = (U : Set _) := by
    ext z
    change ((complexToOrderedEuclidean n).symm (complexToOrderedEuclidean n z) ∈ U) ↔ _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have h := (complexToOrderedEuclidean_volume n).integrableOn_comp_preimage
    (complexToOrderedEuclidean n).toHomeomorph.measurableEmbedding
    (f := f) (s := (coordDomain (complexToOrderedEuclidean n).symm U : Set _))
  rw [hset] at h
  exact h.symm


end HolomorphicAnosov.Analysis.Distribution

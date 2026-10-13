import HolomorphicAnosov.Geometry.ComplexSubmoduleTransfer

open scoped Manifold ContDiff Topology _root_.Topology
open Filter MeasureTheory TopologicalSpace Set
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov
namespace ConnectionFlatEstimates
open scoped BigOperators

/-- Two complex tangent submodules with equal realifications are equal. (Zhang, Lemma 2.3) -/
theorem submodule_eq_of_realification_eq {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X)
    (P U : Submodule ℂ (TangentSpace (complexModel d) x))
    (h : (P.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
      (U.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap) : P = U := by
  exact eq_of_realifications (complexTangentToReal d x).toLinearEquiv P U h

end ConnectionFlatEstimates
end HolomorphicAnosov

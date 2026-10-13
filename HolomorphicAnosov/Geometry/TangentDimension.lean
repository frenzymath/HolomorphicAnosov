import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
namespace HolomorphicAnosov

/-- The complex tangent bundle has the dimension prescribed by the fixed model (Zhang, p. 1). -/
theorem tangent_finrank {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    Module.finrank ℂ (TangentSpace (complexModel d) x) = d := by
  rw [(tangentSpaceCastModel (complexModel d) x).toLinearEquiv.finrank_eq]
  simp [ComplexModel]


end HolomorphicAnosov

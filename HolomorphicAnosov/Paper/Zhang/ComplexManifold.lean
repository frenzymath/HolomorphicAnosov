import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Topology.Connected.Basic

/-! The compact connected complex-manifold assumptions used in Zhang’s theorems. (Zhang, pp. 1–2) -/

open scoped ContDiff

universe u

namespace HolomorphicAnosov

/-- A compact connected Hausdorff second-countable complex manifold with smooth complex chart
transitions. (Zhang, pp. 1–2) -/
class IsCompactComplexManifold (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] : Prop
    extends T2Space X, SecondCountableTopology X, CompactSpace X, ConnectedSpace X,
      IsManifold (complexModel d) ∞ X

end HolomorphicAnosov

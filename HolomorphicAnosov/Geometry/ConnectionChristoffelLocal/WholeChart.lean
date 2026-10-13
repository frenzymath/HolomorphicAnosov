import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
/-!
Charts on the whole open subtype correspond to charts on the original manifold. (Andrews, Prop.
8.3.1 and Ex. 8.3.2, p.74)
-/


open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- The chart on `M` corresponding to a chart on the whole open subtype. -/
def wholeChart (c : OpenPartialHomeomorph ((⊤ : Opens M)) E) :
    OpenPartialHomeomorph M E :=
  (Homeomorph.Set.univ M).symm.toOpenPartialHomeomorph.trans c

end ConnectionChristoffelLocal
end
end HolomorphicAnosov

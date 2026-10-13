import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- The coefficient of a tangent vector field in the chart centered at `p`, evaluated at a chart
coordinate. (Bochner–Montgomery, eq. (27), p. 692) -/
noncomputable def generatorChartCoefficient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    (p : M) (X : (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x) (y : E) : E :=
  (trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) p
    ⟨(extChartAt (modelWithCornersSelf ℝ E) p).symm y,
      X ((extChartAt (modelWithCornersSelf ℝ E) p).symm y)⟩).2


end HolomorphicAnosov.Paper.Zhang

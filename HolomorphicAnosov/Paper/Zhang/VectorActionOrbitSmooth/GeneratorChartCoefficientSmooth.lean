import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.GeneratorChartCoefficient

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- The chart coefficient of a smooth tangent vector field is smooth on the chart target.
(Bochner–Montgomery, p. 692) -/
theorem generatorChartCoefficient_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    (p : M) (X : (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x)
    (hX : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E).tangent ∞
      (fun x ↦ (⟨x,X x⟩ : TangentBundle (modelWithCornersSelf ℝ E) M))) :
    ContDiffOn ℝ ∞ (generatorChartCoefficient p X)
      (extChartAt (modelWithCornersSelf ℝ E) p).target := by
  let e := trivializationAt E (TangentSpace (modelWithCornersSelf ℝ E)) p
  have hh := e.contMDiffOn_section_baseSet_iff.mp hX.contMDiffOn
  apply contMDiffOn_iff_contDiffOn.mp
  apply hh.comp (contMDiffOn_extChartAt_symm p)
  intro y hy
  simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source, mem_preimage] using
    (extChartAt (modelWithCornersSelf ℝ E) p).map_target hy


end HolomorphicAnosov.Paper.Zhang

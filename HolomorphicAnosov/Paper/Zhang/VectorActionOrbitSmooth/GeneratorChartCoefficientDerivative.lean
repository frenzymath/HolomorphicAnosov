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

set_option backward.isDefEq.respectTransparency false in
/-- A curve with velocity `X` has chart derivative equal to the chart coefficient of `X`.
(Bochner–Montgomery, eq. (27), p. 692) -/
theorem generatorChartCoefficient_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    (p : M) (X : (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x)
    (c : ℝ → M) (t : ℝ) (hp : c t ∈ (extChartAt (modelWithCornersSelf ℝ E) p).source)
    (hc : HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E) c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t)))) :
    HasDerivAt (fun s ↦ extChartAt (modelWithCornersSelf ℝ E) p (c s))
      (generatorChartCoefficient p X (extChartAt (modelWithCornersSelf ℝ E) p (c t))) t := by
  have hp' : c t ∈ (chartAt E p).source := by simpa only [extChartAt_source] using hp
  have hcoeff : generatorChartCoefficient p X
      (extChartAt (modelWithCornersSelf ℝ E) p (c t)) =
      tangentCoordChange (modelWithCornersSelf ℝ E) (c t) p (c t) (X (c t)) := by
    unfold generatorChartCoefficient
    rw [(extChartAt (modelWithCornersSelf ℝ E) p).left_inv hp]
    rfl
  rw [hcoeff, hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply ((hasMFDerivAt_extChartAt (I := modelWithCornersSelf ℝ E)
    (x := p) hp').comp t hc).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro r
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace (modelWithCornersSelf ℝ ℝ) t →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℝ) t) r,
    ← ContinuousLinearMap.smulRight_apply, mfderiv_chartAt_eq_tangentCoordChange hp']
  rfl


end HolomorphicAnosov.Paper.Zhang

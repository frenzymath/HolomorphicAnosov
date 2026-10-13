import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Paper.Zhang.StableFoliationsDerivativeScalarRestriction

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real inverse-chart fibre map is the scalar restriction of the complex inverse-chart
derivative. -/
theorem real_inverse_chart_frame {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (a x : M) (hx : x ∈ (chartAt (ComplexModel d) a).source) (v : ComplexModel d) :
    (trivializationAt (ComplexModel d) (TangentSpace (realModel d)) a).symmL ℝ x v =
      complexTangentToReal d x
        (mfderiv (complexModel d) (complexModel d) (chartAt (ComplexModel d) a).symm
          (chartAt (ComplexModel d) a x) ((NormedSpace.fromTangentSpace _).symm v)) := by
  rw [TangentBundle.symmL_trivializationAt hx]
  have hrange : Set.range (realModel d) = Set.univ := by simp [realModel]
  rw [hrange, mfderivWithin_univ]
  change mfderiv (realModel d) (realModel d) (chartAt (ComplexModel d) a).symm
    (chartAt (ComplexModel d) a x) v = _
  have hc := mdifferentiableAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := complexModel d) (n := 1) a)
    ((chartAt (ComplexModel d) a).map_source hx)
  have hr := mdifferentiableAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := realModel d) (n := 1) a)
    ((chartAt (ComplexModel d) a).map_source hx)
  have hd := derivative_scalar_restriction _ _ hc hr
  exact congrArg (fun L ↦ L ((NormedSpace.fromTangentSpace
    (𝕜 := ℝ) (chartAt (ComplexModel d) a x)).symm v)) hd

end StableFoliationsSupport
end HolomorphicAnosov

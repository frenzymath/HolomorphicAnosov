import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealVectorBundle
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealTangentSmooth

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- A compact complex manifold admits a Hermitian inner product on each tangent fibre inducing its
given topology. -/
theorem original_tangent_metric_exists {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M] :
    ∃ g : ∀ x : M, InnerProductSpace.Core ℂ (TangentSpace (complexModel d) x),
      ∀ x, (inferInstance : TopologicalSpace (TangentSpace (complexModel d) x)) =
        (g x).toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
  let : VectorBundle ℝ (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x) :=
    real_vector_bundle
  let : ContMDiffVectorBundle ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (complexModel d) x) (realModel d) :=
    real_tangent_smooth
  obtain ⟨g, hp, hc, ht⟩ := smooth_complex_bundle_hermitian_metric
    (B := ComplexModel d) (M := M)
    (E := fun x : M ↦ TangentSpace (complexModel d) x) d
  exact ⟨g, ht⟩


end HolomorphicAnosov.OneFormBundle

import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyEdistFinite
import Mathlib.Geometry.Manifold.Riemannian.Basic

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- Construct the actual Mathlib Riemannian metric from the given original smooth tensor, without asserting equality with Petersen's alternative path convention. -/
theorem covering_conjugacy_original_metric_g15
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x)) :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ m : MetricSpace X,
      ∃ hm : ‹TopologicalSpace X› = m.toUniformSpace.toTopologicalSpace,
      letI : MetricSpace X := m.replaceTopology hm
      IsRiemannianManifold (realModel d) X := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (realModel d) ∞ (ComplexModel d)
    (fun x : X ↦ TangentSpace (realModel d) x) := inferInstance
  let : IsContinuousRiemannianBundle (ComplexModel d)
    (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let em : EMetricSpace X := EMetricSpace.ofRiemannianMetric (realModel d) X
  let : EMetricSpace X := em
  let m : MetricSpace X := EMetricSpace.toMetricSpace covering_conjugacy_edist_finite_g15
  refine ⟨m, rfl, ?_⟩
  exact ⟨fun _ _ ↦ rfl⟩


end HolomorphicAnosov

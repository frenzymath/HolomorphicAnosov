import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.OriginalMetric
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeFromLamination

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- Bind original tensor estimates to the actual Riemannian norm instance, produce the compatible original-tensor distance, and obtain both native intrinsic asymptotic leaf structures from HPS's source-selected output. -/
theorem covering_conjugacy_native_metric_g15
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (b : TensorAnosovBounds f.toReal a.splitting a.metric) :
    ∃ m : MetricSpace X,
      ∃ hm : ‹TopologicalSpace X› = m.toUniformSpace.toTopologicalSpace,
      letI : MetricSpace X := m.replaceTopology hm
      Nonempty (∀ (σ : Bool) (x : X),
        NativeAsymptoticLeafDatum (realModel d)
          (if σ then f.toHomeomorph.symm else f.toHomeomorph)
          (if σ then a.splitting.unstable.toDistribution
            else a.splitting.stable.toDistribution) x) := by
  classical
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (realModel d) ∞ (ComplexModel d)
    (fun x : X ↦ TangentSpace (realModel d) x) := inferInstance
  obtain ⟨m, hm, hriem⟩ := covering_conjugacy_original_metric_g15 a.metric
  let : MetricSpace X := m.replaceTopology hm
  let : IsRiemannianManifold (realModel d) X := hriem
  have hi (x : X) (v w : TangentSpace (realModel d) x) :
      inner ℝ v w = a.metric.inner x v w := rfl
  have hb : BundleAnosovBounds f.toReal a.splitting := by
    refine ⟨b.C, b.lambda, b.C_pos, b.lambda_pos, b.lambda_lt_one, ?_, ?_⟩
    · intro n x v hv
      simpa only [norm_eq_sqrt_real_inner, hi] using b.stable n x v hv
    · intro n x v hv
      simpa only [norm_eq_sqrt_real_inner, hi] using b.unstable n x v hv
  obtain ⟨hs, hu⟩ := HPS.anosov_global_lamination_distance X f.toReal a.splitting hb
  refine ⟨m, hm, ⟨fun σ x ↦ ?_⟩⟩
  cases σ with
  | false => exact (covering_conjugacy_native_from_lamination_g15
      a.splitting.stable.toDistribution f.toReal f.toReal hs x).some
  | true => exact (covering_conjugacy_native_from_lamination_g15
      a.splitting.unstable.toDistribution f.toReal f.toReal.symm hu x).some


end HolomorphicAnosov

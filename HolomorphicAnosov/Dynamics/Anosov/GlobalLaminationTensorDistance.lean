import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open Manifold

namespace HolomorphicAnosov.HPS

universe u

/-- The tensor form of HPS global lamination existence, retaining the source
plaques and exact asymptotic identification for the supplied metric's path
distance.

Source: Hirsch--Pugh--Shub (1977), §§5--7, pp.61--63,111--116,127--129,
in the existing `anosov_global_lamination_distance` and its tensor conversion.
Install the given smooth metric as the Riemannian bundle structure. Smoothness
gives continuity, so its path extended distance induces the original topology.
Convert the tensor bounds to bundle norms by their defining square-root
identity and apply the distance theorem. Retain its entire output, including
the source-selected plaques, finite-order coherence and asymptotic ranges.
No connectedness, positive rank or finite cross-component distance is needed.
-/
theorem anosov_global_lamination_tensor_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (h : Nonempty (TensorAnosovBounds f S g)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    HasNativeLamination S.stable.toDistribution f
      (fun F families coherent ↦
        SourceBoundDistanceOutput F families coherent f (riemannianEDist 𝓘(ℝ, E))) ∧
    HasNativeLamination S.unstable.toDistribution f
      (fun F families coherent ↦
        SourceBoundDistanceOutput F families coherent f.symm (riemannianEDist 𝓘(ℝ, E))) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := inferInstance
  have hcont : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
    change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
      IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
    infer_instance
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact anosov_global_lamination_distance M f S (tensorAnosovBounds_to_bundle f S g h)


end HolomorphicAnosov.HPS

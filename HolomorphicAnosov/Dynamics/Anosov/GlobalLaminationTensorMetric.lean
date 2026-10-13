import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorDistance
import Mathlib.Topology.UniformSpace.Compact

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open Manifold Filter

namespace HolomorphicAnosov.HPS

universe u

/-- HPS source-selected laminations for a supplied tensor, measured by any
compatible ambient metric on the compact manifold.

Source: HPS (1977) §§5--7, pp.61--63,111--116,127--129, as expressed by the
existing distance theorem, and Mathlib `unique_uniformity_of_compact`.
The tensor-distance theorem supplies both laminations with their source plaques.
The tensor path extended metric and the given metric have the same compact
topology, hence the same uniformity. For either distance, convergence of paired
points to the diagonal uniformity is precisely convergence of their extended
distance to zero, by the extended-distance and ENNReal zero neighborhood bases.
Replace only the asymptotic-range equality by this equivalence, keeping every
leaf, chart, source stage, and finite-order coherence witness unchanged.
Disconnected manifolds and infinite path distances are allowed: only the
uniformity is compared, with no equality of the distance functions asserted.
-/
theorem anosov_global_lamination_tensor_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [m : MetricSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [SecondCountableTopology M] [CompactSpace M]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (h : Nonempty (TensorAnosovBounds f S g)) :
    HasNativeLamination S.stable.toDistribution f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent f edist) ∧
    HasNativeLamination S.unstable.toDistribution f
      (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent f.symm edist) := by
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
  let em := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hunif : em.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact rfl rfl
  have hzero (a b : ℕ → M) :
      Tendsto (fun n ↦ riemannianEDist 𝓘(ℝ, E) (a n) (b n)) atTop (nhds 0) ↔
      Tendsto (fun n ↦ @edist M m.toEDist (a n) (b n)) atTop (nhds 0) := by
    have h₁ := (@uniformity_basis_edist M em.toPseudoEMetricSpace).tendsto_right_iff
      (f := fun n ↦ (a n, b n)) (la := atTop)
    have h₂ := (@uniformity_basis_edist M m.toPseudoEMetricSpace).tendsto_right_iff
      (f := fun n ↦ (a n, b n)) (la := atTop)
    rw [ENNReal.nhds_zero_basis.tendsto_right_iff,
      ENNReal.nhds_zero_basis.tendsto_right_iff]
    change (∀ ε, 0 < ε → ∀ᶠ n in atTop, @edist M em.toEDist (a n) (b n) < ε) ↔ _
    simp only [Set.mem_ofPred_eq, Set.mem_Iio] at h₁ h₂ ⊢
    rw [← h₁, ← h₂]
    rw [hunif]
  have transport {D} (k : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
      (hL : HasNativeLamination D f
        (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent k
          (riemannianEDist 𝓘(ℝ, E)))) :
      HasNativeLamination D f
        (fun F families coherent ↦ SourceBoundDistanceOutput F families coherent k
          (@edist M m.toEDist)) := by
    obtain ⟨ι, L, r, top, charts, smooth, F, boxes, invariant, families, coherent,
      label, sourceDisc, sourceMap, stages, ⟨identification, hlabel⟩, hfamily, hcoherent⟩ := hL
    let := top
    let := charts
    let := smooth
    refine ⟨ι, L, r, top, charts, smooth, F, boxes, invariant, families, coherent,
      label, sourceDisc, sourceMap, stages, ?_, hfamily, hcoherent⟩
    refine ⟨{ label := identification.label, equality := ?_ }, hlabel⟩
    intro x
    rw [identification.equality]
    ext y
    exact hzero (fun n ↦ realIterate 𝓘(ℝ, E) k n y)
      (fun n ↦ realIterate 𝓘(ℝ, E) k n x)
  obtain ⟨hs, hu⟩ := anosov_global_lamination_tensor_distance f S g h
  exact ⟨transport f hs, transport f.symm hu⟩


end HolomorphicAnosov.HPS

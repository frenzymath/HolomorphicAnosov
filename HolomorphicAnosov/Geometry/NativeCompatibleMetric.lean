import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import Mathlib.Topology.UniformSpace.Compact

/-! This file transfers intrinsic asymptotic-leaf data between compatible metrics on a compact
space. (Hirsch–Pugh–Shub, §6B–7, pp. 114–116) -/

open scoped Topology _root_.Topology ContDiff Manifold
open Filter
namespace HolomorphicAnosov

/-- Intrinsic asymptotic-leaf data transfer between metrics inducing the same topology on a compact
space. (Hirsch–Pugh–Shub, §6B–7, pp. 114–116) -/
theorem nativeAsymptoticLeafDatum_compatibleMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [m₁ : MetricSpace M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (m₂ : {m : MetricSpace M // m₁.toUniformSpace.toTopologicalSpace =
      m.toUniformSpace.toTopologicalSpace})
    (f : M ≃ₜ M) (D : RealTangentDistribution 𝓘(ℝ, E) M) (x : M)
    (N : letI := m₂.val.replaceTopology m₂.property; NativeAsymptoticLeafDatum 𝓘(ℝ, E) f D x) :
    Nonempty (NativeAsymptoticLeafDatum 𝓘(ℝ, E) f D x) := by
  let m := m₂.val.replaceTopology m₂.property
  rcases N with ⟨r, top, charts, hausdorff, countable, connected, smooth, incl, immersion, tangent⟩
  let : MetricSpace M := m₁
  have hu : m.toUniformSpace = m₁.toUniformSpace :=
    unique_uniformity_of_compact rfl rfl
  have heq (y : M) : @ForwardAsymptotic M m f x y ↔ ForwardAsymptotic f x y := by
    have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
      (fun n ↦ ((f^[n]) y, (f^[n]) x)) atTop
    have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m₁.toPseudoMetricSpace
      (fun n ↦ ((f^[n]) y, (f^[n]) x)) atTop
    unfold ForwardAsymptotic
    rw [← h₁, ← h₂]
    change Tendsto _ _ m.toUniformSpace.uniformity ↔
      Tendsto _ _ m₁.toUniformSpace.uniformity
    rw [hu]
  have hset : (fun y ↦ @ForwardAsymptotic M m f x y) =
      (fun y ↦ ForwardAsymptotic f x y) := funext (fun y ↦ propext (heq y))
  simp only [StableAsymptoticLeaf] at top charts hausdorff countable connected smooth incl immersion tangent
  generalize hOld : (fun y ↦ @ForwardAsymptotic M m f x y) = P at top charts hausdorff countable connected smooth incl immersion tangent
  have hp : P = (fun y ↦ ForwardAsymptotic f x y) := hOld.symm.trans hset
  clear hOld
  subst P
  exact ⟨{ rank := r
           topology := top
           charts := charts
           hausdorff := hausdorff
           secondCountable := countable
           connected := connected
           smoothAtlas := smooth
           inclusion_smooth := incl
           inclusion_immersion := immersion
           tangent_image := tangent }⟩

end HolomorphicAnosov

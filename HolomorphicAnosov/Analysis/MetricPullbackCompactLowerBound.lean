import HolomorphicAnosov.Analysis.CompactPositiveLowerBound
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

universe u v w

/-- A continuous injective finite-dimensional tangent map over a compact base has a
uniform positive lower bound in the given Riemannian metric. This is the native
pullback-metric lower-bound step in Ghys Lemma 3.2 and HPS (6.7); the theorem
assumes only the actual tangent-total-space continuity and retains the given metric. -/
theorem exists_uniform_metric_pullback_lower_bound
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {X : Type w} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (b : X → M)
    (D : ∀ x : X, V →L[ℝ] TangentSpace 𝓘(ℝ, E) (b x))
    (hD : Continuous (fun z : X × V ↦
      (⟨b z.1, D z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hDinj : ∀ x, Function.Injective (D x)) :
    ∃ m : ℝ, 0 < m ∧ ∀ x v,
      m * ‖v‖ ≤ Real.sqrt (g.inner (b x) (D x v) (D x v)) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm : Continuous (fun z : X × V ↦ ‖D z.1 z.2‖) := by
    exact HolomorphicAnosov.FixedBlockEstimates.Native.continuous_original_norm g (fun z : X × V ↦ b z.1)
      (fun z : X × V ↦ D z.1 z.2) hD
  have hpos : ∀ x v, ‖v‖ = 1 → 0 < ‖D x v‖ := by
    intro x v hv
    apply norm_pos_iff.mpr
    intro hz
    have hv0 : v = 0 := hDinj x (by simp [hz])
    have : (1 : ℝ) = 0 := by simp [hv0] at hv
    exact one_ne_zero this
  obtain ⟨m, hm, hbound⟩ := exists_uniform_linear_lower_bound_of_compact_homogeneous
    (fun x v ↦ ‖D x v‖) hnorm hpos (fun x c v ↦ by simp [map_smul, norm_smul])
  refine ⟨m, hm, ?_⟩
  intro x v
  change m * ‖v‖ ≤ ‖D x v‖
  exact hbound x v

end HolomorphicAnosov.Analysis


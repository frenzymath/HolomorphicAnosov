import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base
open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set
universe u
namespace HolomorphicAnosov.HPS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem continuous_tangent_norm_uniform_comparison
    [FiniteDimensional ℝ E] (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]
    [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)]
    (ν : ExponentialCutoff.ContinuousRestrictedTangentNorm (E := E) (Set.univ : Set X)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ p : (Set.univ : Set X), ∀ v, m * ‖v‖ ≤ ν.value p v) ∧
      (∀ p : (Set.univ : Set X), ∀ v, ν.value p v ≤ M * ‖v‖) := by
  obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := 𝓘(ℝ, E)) (n := ∞) (F := E)
      (E := fun x : X ↦ TangentSpace 𝓘(ℝ, E) x)
  let gm : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : X ↦ TangentSpace 𝓘(ℝ, E) x) := {
    inner := g
    symm := fun x v w => by
      rw [← heq x v w, ← heq x w v]
      exact real_inner_comm _ _
    pos := fun x v hv => by
      rw [← heq x v v]
      exact real_inner_self_pos.mpr hv
    isVonNBounded := fun x => by
      have hset : {v : TangentSpace 𝓘(ℝ, E) x | ((g x) v) v < 1} =
          Metric.ball (0 : TangentSpace 𝓘(ℝ, E) x) 1 := by
        ext v
        change ((g x) v) v < 1 ↔ dist v 0 < 1
        rw [← heq x v v]
        simp only [dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
          RCLike.re_to_real]
        simp
      rw [hset]
      exact NormedSpace.isVonNBounded_ball ℝ _ 1
    contMDiff := hg }
  have hnorm : ∀ x v, ExponentialLift.metricNorm gm x v = ‖v‖ := by
    intro x v
    change Real.sqrt (((g x) v) v) = ‖v‖
    rw [← heq x v v]
    exact (norm_eq_sqrt_real_inner v).symm
  obtain ⟨m, M, hm, hM, hlo, hup⟩ :=
    ExponentialCutoff.finite_core_two_sided_norm_comparison_from_canonical
      gm Set.univ isCompact_univ ν
  refine ⟨m, M, hm, hM, ?_, ?_⟩
  · intro p v
    simpa only [hnorm] using hlo p v
  · intro p v
    simpa only [hnorm] using hup p v
end HolomorphicAnosov.HPS



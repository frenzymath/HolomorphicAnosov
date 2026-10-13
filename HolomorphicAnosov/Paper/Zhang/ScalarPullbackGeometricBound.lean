import HolomorphicAnosov.Paper.Zhang.UniformRealProjectionBound
import HolomorphicAnosov.Paper.Zhang.UniformOriginalScalarBound
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates

open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- The iterated pullbacks of a continuous scalar tangent form annihilating the
unstable bundle satisfy a uniform geometric decay bound in the Anosov metric.
(Zhang, Lemma 2.2, calculation before equation (6), p.5) -/
theorem scalar_pullback_geometric_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hc : Continuous (fun z : TangentBundle (realModel d) X ↦ α z.proj z.snd))
    (hu : ∀ x v, v ∈ a.splitting.unstable.toDistribution x → α x v = 0) :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ C τ : ℝ, 0 < C ∧ 0 < τ ∧ τ < 1 ∧
      ∀ n x (v : TangentSpace (realModel d) x),
        ‖α (((f : X → X)^[n]) x)
          (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v)‖ ≤
            C * τ ^ n * ‖v‖ := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨B, hB, hb⟩ := uniform_original_scalar_bound a.metric α hc
  obtain ⟨K, hK, hk⟩ := uniform_real_projection_bound a.splitting.stable
    a.splitting.unstable a.splitting.isCompl a.metric
  obtain ⟨C, τ, hC, hτ, hτ1, hs, -⟩ := fixed_block_uniform_anosov_estimates f a
  refine ⟨B * C * K, τ, mul_pos (mul_pos (by linarith) hC) (by linarith), hτ, hτ1, ?_⟩
  intro n x v
  let s := (a.splitting.stable.toDistribution x).projection
    (a.splitting.unstable.toDistribution x) (a.splitting.isCompl x) v
  let u := (a.splitting.unstable.toDistribution x).projection
    (a.splitting.stable.toDistribution x) (a.splitting.isCompl x).symm v
  have hv : s + u = v := Submodule.projection_add_projection_eq_self (a.splitting.isCompl x) v
  have hu' : mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x u ∈
      a.splitting.unstable.toDistribution (((f : X → X)^[n]) x) := by
    change mfderiv (realModel d) (realModel d) ((f.toReal : X → X)^[n]) x u ∈
      a.splitting.unstable.toDistribution (((f.toReal : X → X)^[n]) x)
    rw [← real_distribution_iterate_invariant f.toReal a.splitting.unstable.toDistribution
      a.splitting.unstable_map n x]
    exact ⟨u, Submodule.projection_apply_mem _ v, rfl⟩
  rw [← hv, map_add, map_add, hu _ _ hu', add_zero]
  calc
    _ ≤ B * ‖mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x s‖ := hb _ _
    _ ≤ B * (C * τ ^ n * ‖s‖) :=
      mul_le_mul_of_nonneg_left (hs n x s (Submodule.projection_apply_mem _ v)) (by linarith)
    _ ≤ B * (C * τ ^ n * (K * ‖v‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hk x v) (mul_nonneg hC.le (pow_nonneg hτ.le _)))
        (by linarith)
    _ = B * C * K * τ ^ n * ‖s + u‖ := by rw [hv]; ring

end HolomorphicAnosov

import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.UniformOriginalScalarBound
import HolomorphicAnosov.Paper.Zhang.ScalarInvarianceIterate

open Set Filter
open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- A continuous invariant scalar one-form annihilating the unstable bundle of an Anosov
diffeomorphism is zero. (Zhang, Lemma 2.2, p.5, after (6)) -/
theorem invariant_scalar_form_zero
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hc : Continuous (fun z : TangentBundle (realModel d) X ↦ α z.proj z.snd))
    (hi : ∀ x, α x = (α (f x)).comp (mfderiv (realModel d) (realModel d) f x))
    (hu : ∀ x v, v ∈ a.splitting.unstable.toDistribution x → α x v = 0) :
    ∀ x, α x = 0 := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨B, hB, hb⟩ := uniform_original_scalar_bound a.metric α hc
  obtain ⟨C, τ, hC, hτ, hτ1, hs, -⟩ := fixed_block_uniform_anosov_estimates f a
  have hstable (x : X) (v : TangentSpace (realModel d) x)
      (hv : v ∈ a.splitting.stable.toDistribution x) : α x v = 0 := by
    have hbound (n : ℕ) : ‖α x v‖ ≤ B * (C * τ ^ n * ‖v‖) := by
      rw [scalar_invariance_iterate f α hi n x v]
      exact (hb _ _).trans (mul_le_mul_of_nonneg_left (hs n x v hv) (by linarith))
    have hlim : Tendsto (fun n : ℕ ↦ B * (C * τ ^ n * ‖v‖)) atTop (𝓝 0) := by
      simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hτ.le hτ1).const_mul C).mul_const
        ‖v‖).const_mul B
    exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound))
      (norm_nonneg _))
  intro x
  ext v
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp
    (show v ∈ a.splitting.stable.toDistribution x ⊔ a.splitting.unstable.toDistribution x by
      rw [(a.splitting.isCompl x).sup_eq_top]
      trivial)
  rw [← hst, map_add, hstable x s hs, hu x t ht]
  simp

end HolomorphicAnosov

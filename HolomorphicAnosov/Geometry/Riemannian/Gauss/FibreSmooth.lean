import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition

/-! The Riemannian exponential is smooth on each fixed tangent fibre within its natural domain.
(Gallier–Quaintance, Prop. 16.8, pp.452–454; Andrews, Lecture 8, §8.11, pp.84–85) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The restriction of the Riemannian exponential to a fixed tangent fibre is smooth at every point
of its natural domain. (Gallier–Quaintance, Prop. 16.8) -/
theorem gauss_fibre_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) ∞
      (fun u ↦ riemannianExponential g ⟨p, u⟩) v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hi : ContMDiffAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) (𝓘(ℝ, E)).tangent ∞
      (fun u : TangentSpace 𝓘(ℝ, E) p ↦ (⟨p, u⟩ : TangentBundle 𝓘(ℝ, E) M)) v := by
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_const, ?_⟩
    let τ := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) p
    have hτ := ((τ.continuousLinearMapAt ℝ p).contDiff (n := ∞)).contMDiff.contMDiffAt (x := v)
    convert hτ using 1
    funext u
    exact (τ.continuousLinearMapAt_apply_of_mem ℝ
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) p) u).symm
  obtain ⟨hD, _, he, _⟩ := riemannian_exponential_local_addition g
  exact (he.contMDiffAt (hD.mem_nhds hv)).comp v hi

end HolomorphicAnosov


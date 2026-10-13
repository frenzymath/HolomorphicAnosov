import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition

/-! The differential of the Riemannian exponential at zero is the identity on the tangent fibre.
(Gallier–Quaintance, Prop. 16.4, p.448; Andrews, Lecture 8, §8.11, pp.85–86) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- The Riemannian exponential sends the zero vector at `p` to `p`, and its differential there is
the identity after transport along this equality. (Gallier–Quaintance, Prop. 16.4, p.448;
Andrews, Lecture 8, §8.11, pp.85–86) -/
theorem gauss_exponential_derivative_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ p : M, ∃ hp : riemannianExponential g ⟨p, 0⟩ = p,
      ∀ w : TangentSpace 𝓘(ℝ, E) p,
        (hp ▸ mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
          (fun v : TangentSpace 𝓘(ℝ, E) p ↦
            riemannianExponential g (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M)) 0
          ((NormedSpace.fromTangentSpace (0 : TangentSpace 𝓘(ℝ, E) p)).symm w)) = w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨_, _, _, hbase, hvert, _⟩ := riemannian_exponential_local_addition g
  intro p
  refine ⟨hbase p, ?_⟩
  intro w
  let c : TangentSpace 𝓘(ℝ, E) p ≃L[ℝ] E := tangentSpaceCastModel 𝓘(ℝ, E) p
  let ep : E → M := fun z ↦ riemannianExponential g
    (⟨p, (tangentSpaceCastModel 𝓘(ℝ, E) p).symm z⟩ : TangentBundle 𝓘(ℝ, E) M)
  have hep : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 :=
    (riemannianExponential_fibre_contMDiffAt_zero g p).mdifferentiableAt (by simp)
  have hcomp : (fun z : TangentSpace 𝓘(ℝ, E) p ↦
      riemannianExponential g (⟨p, z⟩ : TangentBundle 𝓘(ℝ, E) M)) = ep ∘ c := by
    funext z
    simp [ep, c]
  have hc := mfderiv_comp_apply (I := 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p))
    (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) (f := c) (g := ep)
    (0 : TangentSpace 𝓘(ℝ, E) p) hep c.mdifferentiableAt
    ((NormedSpace.fromTangentSpace (0 : TangentSpace 𝓘(ℝ, E) p)).symm w)
  rw [← hcomp, ContinuousLinearEquiv.mfderiv_eq] at hc
  change mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
      (fun z : TangentSpace 𝓘(ℝ, E) p ↦ riemannianExponential g ⟨p, z⟩) 0
      ((NormedSpace.fromTangentSpace (0 : TangentSpace 𝓘(ℝ, E) p)).symm w) =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0
      ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm (c w)) at hc
  have hv' : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0
      ((tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm (c w)) = c w := hvert p (c w)
  rw [hv'] at hc
  apply c.injective
  rw [show ∀ (q : M) (hp : q = p) (v : TangentSpace 𝓘(ℝ, E) q),
      tangentSpaceCastModel 𝓘(ℝ, E) p (hp ▸ v) = tangentSpaceCastModel 𝓘(ℝ, E) q v by
    intro q hp v
    subst q
    rfl]
  exact hc

end HolomorphicAnosov

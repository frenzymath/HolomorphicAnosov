import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialConstantSpeed
import HolomorphicAnosov.Geometry.Riemannian.Gauss.VariationEndpointVelocities
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialOrthogonality

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- On the natural time-one domain, the differential of the Riemannian exponential preserves the
metric pairing of a radial vector with any tangent vector. (Gallier–Quaintance, Props.
16.8–16.9, pp.452–454; Andrews, Lecture 11, Prop. 11.1.1, pp.101–102) -/
theorem gauss_pairing_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v w : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    g.inner (riemannianExponential g ⟨p, v⟩)
      (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
        (fun u ↦ riemannianExponential g ⟨p, u⟩) v
          ((NormedSpace.fromTangentSpace v).symm v))
      (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
        (fun u ↦ riemannianExponential g ⟨p, u⟩) v
          ((NormedSpace.fromTangentSpace v).symm w)) = g.inner p v w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let de := fun u ↦ mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
    (fun u ↦ riemannianExponential g ⟨p, u⟩) v ((NormedSpace.fromTangentSpace v).symm u)
  change g.inner (riemannianExponential g ⟨p, v⟩) (de v) (de w) = g.inner p v w
  by_cases hv0 : v = 0
  · subst v
    simp only [de, map_zero, zero_apply]
  have hnonneg (q : M) (u : TangentSpace 𝓘(ℝ, E) q) : 0 ≤ g.inner q u u := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (g.pos q u hu).le
  have hspeed := gauss_radial_constant_speed g p v hv 1 (by simp)
  have hvel := (gauss_variation_endpoint_velocities g p v w hv).1
  change curveVelocity (fun s ↦ riemannianExponential g ⟨p, s • v⟩) 1 = de v at hvel
  erw [one_smul] at hspeed
  rw [hvel] at hspeed
  have hrad : g.inner (riemannianExponential g ⟨p, v⟩) (de v) (de v) = g.inner p v v :=
    (Real.sqrt_inj (hnonneg _ _) (hnonneg _ _)).mp hspeed
  have hden : g.inner p v v ≠ 0 := (g.pos p v hv0).ne'
  have hscalar : g.inner p v w / g.inner p v v * g.inner p v v = g.inner p v w :=
    div_mul_cancel₀ _ hden
  have hperp : g.inner p v (w - (g.inner p v w / g.inner p v v) • v) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hscalar, sub_self]
  have h := gauss_radial_orthogonality g p v (w - (g.inner p v w / g.inner p v v) • v) hv hv0 hperp
  change g.inner (riemannianExponential g ⟨p, v⟩) (de v)
    (de (w - (g.inner p v w / g.inner p v v) • v)) = 0 at h
  have hde : de (w - (g.inner p v w / g.inner p v v) • v) =
      de w - (g.inner p v w / g.inner p v v) • de v := by simp only [de, map_sub, map_smul]
  rw [hde, map_sub, map_smul] at h
  simpa only [smul_eq_mul, hrad, hscalar, sub_eq_zero] using h


end HolomorphicAnosov

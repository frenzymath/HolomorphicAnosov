import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.Riemannian.GaussAffineCurveVelocity
import HolomorphicAnosov.Geometry.Riemannian.Gauss.FibreSmooth

/-! The endpoint velocities of radial and affine exponential variations are given by the exponential
differential. -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- The radial velocity at time one and the affine transverse velocity at parameter zero equal the
exponential differential at `v` applied to `v` and `w`, respectively. (Gallier–Quaintance, Props.
16.7–16.8, pp.451–454; Andrews, Prop. 8.3.1 and §8.4, pp.74–75; §10.1 and Prop. 10.3.1, pp.95–98) -/
theorem gauss_variation_endpoint_velocities
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v w : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let e := fun u : TangentSpace 𝓘(ℝ, E) p ↦ riemannianExponential g ⟨p, u⟩
    let de := fun u ↦ mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v
      ((NormedSpace.fromTangentSpace v).symm u)
    curveVelocity (fun t ↦ e (t • v)) 1 = de v ∧
      curveVelocity (fun s ↦ e (v + s • w)) 0 = de w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := fun u : TangentSpace 𝓘(ℝ, E) p ↦ riemannianExponential g ⟨p, u⟩
  have he : MDifferentiableAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v :=
    (gauss_fibre_smooth g p v hv).mdifferentiableAt (by simp)
  constructor
  · have hr := gauss_affine_curve_velocity_public (v := 0) (w := v) (t := 1)
      he (by simp)
    have hfun : (fun s : ℝ ↦ e ((0 : TangentSpace 𝓘(ℝ, E) p) + s • v)) =
        (fun s ↦ e (s • v)) := by
      funext s
      rw [zero_add]
    rw [hfun] at hr
    exact hr
  · exact gauss_affine_curve_velocity_public (v := v) (w := w) (t := 0)
      he (by simp)


end HolomorphicAnosov

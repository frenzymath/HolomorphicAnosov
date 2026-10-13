import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialConstantSpeed
import HolomorphicAnosov.Geometry.Riemannian.Gauss.GaussPairingIdentity
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ExponentialDerivativeZero
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialGeodesic

/-! The Gauss lemma holds on the natural time-one exponential domain, together with radial constant
speed and the identity differential at zero. (Gallier–Quaintance, Props. 16.8–16.9, pp.452–454) -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The natural Riemannian exponential is smooth on its open time-one domain, which contains the
zero section, and satisfies the Gauss pairing identity. Its radial curves are geodesics of
constant speed, radial and spherical directions are orthogonal, and its differential at zero is
the identity. (Gallier–Quaintance, Props. 16.7–16.9, pp.451–454; Andrews, Lecture 11, Prop.
11.1.1, pp.101–102; Teschl, Thm 6.1, pp.189–190) -/
theorem gallier_quaintance_gauss_lemma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _)) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let D := riemannianExponentialDomain g
    let e := fun (p : M) (v : TangentSpace 𝓘(ℝ, E) p) ↦
      riemannianExponential g (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M)
    let de := fun (p : M) (v w : TangentSpace 𝓘(ℝ, E) p) ↦
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) (e p) v
        ((NormedSpace.fromTangentSpace v).symm w)
    IsOpen D ∧
    (∀ p : M, (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D) ∧
    ContMDiffOn (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞ (riemannianExponential g) D ∧
    (∀ (p : M) (v w : TangentSpace 𝓘(ℝ, E) p),
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D →
      g.inner (e p v) (de p v v) (de p v w) = g.inner p v w) ∧
    (∀ (p : M) (v : TangentSpace 𝓘(ℝ, E) p),
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D →
      ∃ J : Set ℝ, IsOpen J ∧ OrdConnected J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
        IsConnectionGeodesicOn (riemannianConnection g) (fun t ↦ e p (t • v)) J ∧
        (∀ t ∈ J, (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D) ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          Real.sqrt (g.inner (e p (t • v))
            (curveVelocity (fun s ↦ e p (s • v)) t)
            (curveVelocity (fun s ↦ e p (s • v)) t)) = Real.sqrt (g.inner p v v)) ∧
    (∀ (p : M) (v w : TangentSpace 𝓘(ℝ, E) p),
      (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D → v ≠ 0 → g.inner p v w = 0 →
      g.inner (e p v) (de p v v) (de p v w) = 0) ∧
    ∀ p : M, ∃ hp : e p 0 = p,
      ∀ w : TangentSpace 𝓘(ℝ, E) p, (hp ▸ de p 0 w) = w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  dsimp only
  obtain ⟨hD, hzero, he, _⟩ := riemannian_exponential_local_addition g
  refine ⟨hD, hzero, he, ?_⟩
  refine ⟨gauss_pairing_identity g, ?_,
    fun p v w hv _ hw ↦ (gauss_pairing_identity g p v w hv).trans hw,
    gauss_exponential_derivative_zero g⟩
  intro p v hv
  obtain ⟨J, hJ, hconn, hseg, hgeod, hdom, _⟩ := gauss_radial_geodesic g p v hv
  exact ⟨J, hJ, hconn, hseg, hgeod, hdom, gauss_radial_constant_speed g p v hv⟩

end HolomorphicAnosov


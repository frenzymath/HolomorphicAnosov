import HolomorphicAnosov.Geometry.Riemannian.Gauss.GeodesicEnergyDerivative
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialGeodesic
import Mathlib.Analysis.Calculus.MeanValue

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The speed of the radial geodesic `t ↦ exp_p(t v)` on `[0, 1]` equals the norm of its initial
vector `v`. (Gallier–Quaintance, Prop. 16.8, pp.452–454; Andrews, Prop. 11.1.1, pp.101–102) -/
theorem gauss_radial_constant_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      Real.sqrt (g.inner (riemannianExponential g ⟨p, t • v⟩)
        (curveVelocity (fun s ↦ riemannianExponential g ⟨p, s • v⟩) t)
        (curveVelocity (fun s ↦ riemannianExponential g ⟨p, s • v⟩) t)) =
          Real.sqrt (g.inner p v v) := by
  obtain ⟨J, hJ, hconn, hseg, hγ, hdom, hinit⟩ := gauss_radial_geodesic g p v hv
  let γ : ℝ → M := fun t ↦ riemannianExponential g ⟨p, t • v⟩
  let f : ℝ → ℝ := fun t ↦ g.inner (γ t) (curveVelocity γ t) (curveVelocity γ t)
  have hd (t : ℝ) (ht : t ∈ J) : HasDerivAt f 0 t := by
    let q : ConnectionWhole M := ⟨γ t, mem_univ (γ t)⟩
    exact gauss_geodesic_energy_derivative g (Module.finBasis ℝ E) (chartAt E q)
      (chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) q) γ J hJ hγ t ht
      (mem_chart_source E q)
  have h0 : f 0 = g.inner p v v := by
    have hh := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ g.inner z.proj z.snd z.snd) hinit
    exact hh
  intro t ht
  have he : f t = f 0 := hJ.is_const_of_deriv_eq_zero hconn.isPreconnected
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv) (hseg ht) (hseg (by simp))
  exact congrArg Real.sqrt (he.trans h0)

end HolomorphicAnosov


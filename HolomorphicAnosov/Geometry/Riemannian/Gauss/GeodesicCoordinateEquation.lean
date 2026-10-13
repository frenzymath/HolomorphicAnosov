import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateCurveVelocity
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.CurveTangentLiftSmooth

/-! Geodesics of smooth affine connections satisfy the second-order coordinate equation. -/

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- A geodesic of a smooth affine connection satisfies the second-order coordinate equation in every
smooth chart. (Andrews, Prop. 8.11.2, p.84) -/
theorem gauss_geodesic_coordinate_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (nabla : SmoothAffineConnection E M) {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (γ : ℝ → M) (J : Set ℝ) (hJ : IsOpen J)
    (hγ : IsConnectionGeodesicOn nabla γ J) (t : ℝ) (ht : t ∈ J)
    (hp : (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M) ∈ c.source) :
    deriv (deriv (connectionChartMap c ∘ γ)) t +
      connectionChristoffelBilinear nabla b c hc (γ t)
        (deriv (connectionChartMap c ∘ γ) t)
        (deriv (connectionChartMap c ∘ γ) t) = 0 := by
  have hcont : ContinuousAt (fun r ↦ (⟨γ r, mem_univ (γ r)⟩ : ConnectionWhole M)) t :=
    ((continuous_id.subtype_mk fun p : M ↦ mem_univ p).continuousAt).comp
      (hγ.1.contMDiffAt (hJ.mem_nhds ht)).continuousAt
  have he : alongCurveCoordinate c γ (curveVelocity γ) =ᶠ[𝓝 t]
      deriv (connectionChartMap c ∘ γ) := by
    filter_upwards [hJ.mem_nhds ht, hcont.eventually (c.open_source.mem_nhds hp)] with r hr hrc
    exact gauss_coordinate_curveVelocity c hc γ r
      ((hγ.1.contMDiffAt (hJ.mem_nhds hr)).mdifferentiableAt (by simp)) hrc
  have h := covariantDerivativeAlongCurve_coordinates nabla b c hc γ (curveVelocity γ)
    J hJ hγ.1 (curveTangentLift_contMDiffOn hJ hγ.1) t ht hp
  rw [show alongCurveCoordinate c γ (covariantDerivativeAlongCurve nabla γ
      (curveVelocity γ)) t = 0 by simp [alongCurveCoordinate, hγ.2 t ht]] at h
  simpa only [covariantDerivativeCoordinate, he.deriv_eq, he.self_of_nhds] using h.symm

end HolomorphicAnosov


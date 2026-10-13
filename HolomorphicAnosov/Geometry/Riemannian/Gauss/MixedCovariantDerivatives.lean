import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChristoffelBilinearSymmetric
import HolomorphicAnosov.Geometry.Riemannian.GaussMixedCoordinatePartials
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChartMapSmooth
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateCurveVelocity

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The covariant mixed derivatives of a smooth two-parameter map commute for the Levi-Civita
connection. (Gallier–Quaintance, Prop. 16.7, p.451) -/
theorem gauss_mixed_covariant_derivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (F : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F U)
    (t s : ℝ) (hz : (t, s) ∈ U) :
    covariantDerivativeAlongCurve (riemannianConnection g) (fun r ↦ F (r, s))
        (fun r ↦ curveVelocity (fun q ↦ F (r, q)) s) t =
      covariantDerivativeAlongCurve (riemannianConnection g) (fun q ↦ F (t, q))
        (fun q ↦ curveVelocity (fun r ↦ F (r, q)) t) s := by
  let p : ConnectionWhole M := ⟨F (t, s), mem_univ _⟩
  let c := chartAt E p
  have hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M) :=
    chart_mem_maximalAtlas p
  have hp : p ∈ c.source := mem_chart_source E p
  have hsub : ContinuousAt (fun q : M ↦ (⟨q, mem_univ q⟩ : ConnectionWhole M))
      (F (t, s)) := (continuous_id.subtype_mk _).continuousAt
  have hsource : ∀ᶠ z in 𝓝 (t, s),
      (⟨F z, mem_univ (F z)⟩ : ConnectionWhole M) ∈ c.source :=
    ((hsub.comp (hF.contMDiffAt (hU.mem_nhds hz)).continuousAt).eventually
      (c.open_source.mem_nhds hp))
  have hn : ∀ᶠ z in 𝓝 (t, s), z ∈ U ∧
      (⟨F z, mem_univ (F z)⟩ : ConnectionWhole M) ∈ c.source :=
    Filter.Eventually.and (hU.mem_nhds hz) hsource
  have ht : alongCurveCoordinate c (fun r ↦ F (r, s))
      (fun r ↦ curveVelocity (fun q ↦ F (r, q)) s) =ᶠ[𝓝 t]
      (fun r ↦ deriv (fun q ↦ connectionChartMap c (F (r, q))) s) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hn] with r hr
    have hcurve := ((hF.contMDiffAt (hU.mem_nhds hr.1)).comp s
      (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt).mdifferentiableAt (by simp)
    exact gauss_coordinate_curveVelocity c hc (fun q ↦ F (r, q)) s hcurve hr.2
  have hs : alongCurveCoordinate c (fun q ↦ F (t, q))
      (fun q ↦ curveVelocity (fun r ↦ F (r, q)) t) =ᶠ[𝓝 s]
      (fun q ↦ deriv (fun r ↦ connectionChartMap c (F (r, q))) t) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with q hq
    have hcurve := ((hF.contMDiffAt (hU.mem_nhds hq.1)).comp t
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt).mdifferentiableAt (by simp)
    exact gauss_coordinate_curveVelocity c hc (fun r ↦ F (r, q)) t hcurve hq.2
  have hx : ContDiffAt ℝ 2 (fun z ↦ connectionChartMap c (F z)) (t, s) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact ((gauss_connectionChartMap_smooth c hc (F (t, s)) hp).comp (t, s)
      (hF.contMDiffAt (hU.mem_nhds hz))).of_le (by simp)
  have hm := gauss_mixed_coordinate_partials_public hx
  have ha : covariantDerivativeCoordinate (riemannianConnection g) (Module.finBasis ℝ E)
      c hc (fun r ↦ F (r, s)) (fun r ↦ curveVelocity (fun q ↦ F (r, q)) s) t =
      covariantDerivativeCoordinate (riemannianConnection g) (Module.finBasis ℝ E)
      c hc (fun q ↦ F (t, q)) (fun q ↦ curveVelocity (fun r ↦ F (r, q)) t) s := by
    unfold covariantDerivativeCoordinate
    rw [ht.deriv_eq, hs.deriv_eq, ht.self_of_nhds, hs.self_of_nhds, hm]
    exact congrArg (fun x ↦ deriv (fun q ↦ deriv
      (fun r ↦ connectionChartMap c (F (r, q))) t) s + x)
      (gauss_connectionChristoffelBilinear_symmetric g (Module.finBasis ℝ E)
        c hc (F (t, s)) hp _ _)
  unfold covariantDerivativeAlongCurve
  change (tangentSpaceCastModel 𝓘(ℝ, E) (F (t, s))).symm
      (tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartInverse c
        (connectionChartMap c (F (t, s))))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c)
          (connectionChartMap c (F (t, s)))
          ((tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartMap c (F (t, s)))).symm
            (covariantDerivativeCoordinate (riemannianConnection g) (Module.finBasis ℝ E)
              c hc (fun r ↦ F (r, s))
              (fun r ↦ curveVelocity (fun q ↦ F (r, q)) s) t)))) = _
  rw [ha]

end HolomorphicAnosov


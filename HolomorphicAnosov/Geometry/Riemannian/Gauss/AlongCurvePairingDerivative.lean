import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.SmoothLeviCivitaConnection
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateMetricCompatibility
import HolomorphicAnosov.Geometry.Riemannian.Gauss.NativeCoordinatePairing
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChartMapSmooth
import HolomorphicAnosov.Geometry.Riemannian.Gauss.SmoothMetricPullbackEntry
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix
namespace HolomorphicAnosov

/-- The derivative of the metric pairing of two differentiable fields along a smooth curve is the
sum of the pairings with their covariant derivatives. (Gallier–Quaintance, Prop. 15.12,
pp.436–438) -/
theorem gauss_along_curve_pairing_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (γ : ℝ → M) (Y Z : (r : ℝ) → TangentSpace 𝓘(ℝ, E) (γ r)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ t)
    (hY : DifferentiableAt ℝ (alongCurveCoordinate
      (chartAt E (⟨γ t, mem_univ _⟩ : ConnectionWhole M)) γ Y) t)
    (hZ : DifferentiableAt ℝ (alongCurveCoordinate
      (chartAt E (⟨γ t, mem_univ _⟩ : ConnectionWhole M)) γ Z) t) :
    HasDerivAt (fun r ↦ g.inner (γ r) (Y r) (Z r))
      (g.inner (γ t) (covariantDerivativeAlongCurve (riemannianConnection g) γ Y t) (Z t) +
       g.inner (γ t) (Y t) (covariantDerivativeAlongCurve (riemannianConnection g) γ Z t)) t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let p : ConnectionWhole M := ⟨γ t, mem_univ _⟩
  let c := chartAt E p
  have hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M) := chart_mem_maximalAtlas p
  have hp : p ∈ c.source := mem_chart_source E p
  let ψ : E → M := connectionChartInverse c
  let x : ℝ → E := connectionChartMap c ∘ γ
  let y := alongCurveCoordinate c γ Y
  let z := alongCurveCoordinate c γ Z
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun a ↦
    (g.inner (ψ a)).bilinearComp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ a)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ a)
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ c.target :=
    contMDiff_subtype_val.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)
  have hB : ContDiffOn ℝ ∞ B c.target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact gauss_smooth_metric_pullback_entry g c.open_target ψ hψ v w
  have hx : ContDiffAt ℝ ∞ x t := contMDiffAt_iff_contDiffAt.mp
    ((gauss_connectionChartMap_smooth c hc (γ t) hp).comp t hγ)
  have hxd := (hx.differentiableAt (by simp)).hasDerivAt
  have hBt : ContDiffAt ℝ ∞ B (x t) := hB.contDiffAt (c.open_target.mem_nhds (c.map_source hp))
  have hBd : HasFDerivAt B (fderiv ℝ B (x t)) (x t) :=
    (hBt.differentiableAt (by simp)).hasFDerivAt
  let Bd := fderiv ℝ B (x t) (deriv x t)
  have hdB : HasDerivAt (B ∘ x) Bd t := hBd.comp_hasDerivAt t hxd
  have hd := (hdB.clm_apply hY.hasDerivAt).clm_apply hZ.hasDerivAt
  let A := connectionChristoffelBilinear (E := E) (riemannianConnection g)
    (Module.finBasis ℝ E) c hc (γ t) (deriv x t)
  have hcompat : Bd (y t) (z t) = B (x t) (A (y t)) (z t) +
      B (x t) (y t) (A (z t)) := by
    have hentry := (hBd.clm_apply (hasFDerivAt_const (y t) (x t))).clm_apply
      (hasFDerivAt_const (z t) (x t))
    have he := congrArg (fun f : E →L[ℝ] ℝ ↦ f (deriv x t)) hentry.fderiv
    have hc' := gauss_coordinate_metric_compatibility g (Module.finBasis ℝ E) c hc
      p hp (deriv x t) (y t) (z t)
    change fderiv ℝ (fun a ↦ B a (y t) (z t)) (x t) (deriv x t) =
      B (x t) (A (y t)) (z t) + B (x t) (y t) (A (z t)) at hc'
    rw [he] at hc'
    simpa [Bd] using hc'
  have hderiv : HasDerivAt (fun r ↦ B (x r) (y r) (z r))
      (B (x t) (deriv y t + A (y t)) (z t) +
       B (x t) (y t) (deriv z t + A (z t))) t := by
    change HasDerivAt (fun r ↦ B (x r) (y r) (z r))
      ((Bd (y t) + B (x t) (deriv y t)) (z t) +
        B (x t) (y t) (deriv z t)) t at hd
    convert hd using 1
    simp only [add_apply, hcompat, map_add]
    ring
  have hinv : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t) :=
    (hψ.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))).mdifferentiableAt (by simp)
  have hchart := (gauss_connectionChartMap_smooth c hc (γ t) hp).mdifferentiableAt (by simp)
  have hid : ψ ∘ connectionChartMap c =ᶠ[𝓝 (γ t)] id := by
    have hcont : ContinuousAt (fun q : M ↦ (⟨q, mem_univ q⟩ : ConnectionWhole M)) (γ t) :=
      (continuous_id.subtype_mk fun q : M ↦ mem_univ q).continuousAt
    filter_upwards [hcont.eventually (c.open_source.mem_nhds hp)] with q hq
    exact congrArg Subtype.val (c.left_inv hq)
  have hcancel (v : TangentSpace 𝓘(ℝ, E) (γ t)) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) (γ t) v) = v := by
    dsimp only [x, Function.comp_apply]
    rw [← mfderiv_comp_apply (x := γ t) (f := connectionChartMap c) (g := ψ)
      hinv hchart, hid.mfderiv_eq, mfderiv_id]
    rfl
  have hbase : ψ (x t) = γ t := hid.self_of_nhds
  have hrhs : B (x t) (deriv y t + A (y t)) (z t) +
      B (x t) (y t) (deriv z t + A (z t)) =
      g.inner (γ t) (covariantDerivativeAlongCurve (riemannianConnection g) γ Y t) (Z t) +
      g.inner (γ t) (Y t) (covariantDerivativeAlongCurve (riemannianConnection g) γ Z t) := by
    change g.inner (ψ (x t))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t) (deriv y t + A (y t)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) (γ t) (Z t))) +
      g.inner (ψ (x t))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartMap c) (γ t) (Y t)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t) (deriv z t + A (z t))) = _
    rw [hcancel (Y t), hcancel (Z t)]
    unfold covariantDerivativeAlongCurve
    change g.inner (ψ (x t)) _ _ + g.inner (ψ (x t)) _ _ =
      g.inner (γ t)
        ((tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) (ψ (x t))
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t) (deriv y t + A (y t))))) (Z t) +
      g.inner (γ t) (Y t)
        ((tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) (ψ (x t))
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (x t) (deriv z t + A (z t)))))
    erw [hbase]
    rfl
  rw [hrhs] at hderiv
  apply hderiv.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun r ↦ (⟨γ r, mem_univ (γ r)⟩ : ConnectionWhole M)) t :=
    ((continuous_id.subtype_mk fun p : M ↦ mem_univ p).continuousAt).comp hγ.continuousAt
  filter_upwards [hcont.eventually (c.open_source.mem_nhds hp)] with r hr
  exact (gauss_native_coordinate_pairing g c hc (γ r) hr (Y r) (Z r)).symm

end HolomorphicAnosov


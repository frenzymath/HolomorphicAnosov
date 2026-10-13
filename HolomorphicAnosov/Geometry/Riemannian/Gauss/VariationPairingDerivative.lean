import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.Riemannian.Gauss.AlongCurvePairingDerivative
import HolomorphicAnosov.Geometry.Riemannian.Gauss.MixedCovariantDerivatives
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChartMapSmooth
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateCurveVelocity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix
namespace HolomorphicAnosov

/-- At a point where the time curve has zero covariant acceleration, the time derivative of the
pairing of the two variation velocities equals half the transverse derivative of the squared time
speed. (Gallier–Quaintance, Prop. 16.8, pp.452–453) -/
theorem gauss_variation_pairing_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (F : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F U)
    (t s : ℝ) (hz : (t, s) ∈ U)
    (hgeod : covariantDerivativeAlongCurve (riemannianConnection g)
      (fun r ↦ F (r, s)) (curveVelocity (fun r ↦ F (r, s))) t = 0) :
    HasDerivAt (fun r ↦ g.inner (F (r, s))
      (curveVelocity (fun a ↦ F (a, s)) r)
      (curveVelocity (fun b ↦ F (r, b)) s))
      ((1 / 2 : ℝ) * deriv (fun q ↦ g.inner (F (t, q))
        (curveVelocity (fun a ↦ F (a, q)) t)
        (curveVelocity (fun a ↦ F (a, q)) t)) s) t := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let p : ConnectionWhole M := ⟨F (t, s), mem_univ _⟩
  let c := chartAt E p
  have hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M) := chart_mem_maximalAtlas p
  have hp : p ∈ c.source := mem_chart_source E p
  let x : ℝ × ℝ → E := fun z ↦ connectionChartMap c (F z)
  have hFat := hF.contMDiffAt (hU.mem_nhds hz)
  have hx : ContDiffAt ℝ ∞ x (t, s) := contMDiffAt_iff_contDiffAt.mp
    ((gauss_connectionChartMap_smooth c hc (F (t, s)) hp).comp (t, s) hFat)
  have hsource : ∀ᶠ z in 𝓝 (t, s),
      (⟨F z, mem_univ (F z)⟩ : ConnectionWhole M) ∈ c.source :=
    (((continuous_id.subtype_mk _).continuousAt).comp hFat.continuousAt).eventually
      (c.open_source.mem_nhds hp)
  have hnear : ∀ᶠ z in 𝓝 (t, s), z ∈ U ∧
      (⟨F z, mem_univ (F z)⟩ : ConnectionWhole M) ∈ c.source ∧
      DifferentiableAt ℝ x z :=
    Filter.Eventually.and (hU.mem_nhds hz) (hsource.and
      (((hx.of_le (m := 1) (by simp)).eventually (by norm_num)).mono fun z hz ↦ hz.differentiableAt (by simp)))
  let T : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, E) (F z) :=
    fun z ↦ curveVelocity (fun r ↦ F (r, z.2)) z.1
  let S : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, E) (F z) :=
    fun z ↦ curveVelocity (fun q ↦ F (z.1, q)) z.2
  let y : ℝ × ℝ → E := fun z ↦
    alongCurveCoordinate c (fun r ↦ F (r, z.2)) (fun r ↦ T (r, z.2)) z.1
  let zc : ℝ × ℝ → E := fun z ↦
    alongCurveCoordinate c (fun q ↦ F (z.1, q)) (fun q ↦ S (z.1, q)) z.2
  have hy : y =ᶠ[𝓝 (t, s)] (fun z ↦ fderiv ℝ x z (1, 0)) := by
    filter_upwards [hnear] with z hz
    have hcurve := ((hF.contMDiffAt (hU.mem_nhds hz.1)).comp z.1
      (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt).mdifferentiableAt (by simp)
    change alongCurveCoordinate c (fun r ↦ F (r, z.2))
      (curveVelocity (fun r ↦ F (r, z.2))) z.1 = _
    rw [gauss_coordinate_curveVelocity c hc (fun r ↦ F (r, z.2)) z.1 hcurve hz.2.1]
    exact (hz.2.2.hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hzc : zc =ᶠ[𝓝 (t, s)] (fun z ↦ fderiv ℝ x z (0, 1)) := by
    filter_upwards [hnear] with z hz
    have hcurve := ((hF.contMDiffAt (hU.mem_nhds hz.1)).comp z.2
      (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt).mdifferentiableAt (by simp)
    change alongCurveCoordinate c (fun q ↦ F (z.1, q))
      (curveVelocity (fun q ↦ F (z.1, q))) z.2 = _
    rw [gauss_coordinate_curveVelocity c hc (fun q ↦ F (z.1, q)) z.2 hcurve hz.2.1]
    exact (hz.2.2.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  have hyd : DifferentiableAt ℝ y (t, s) :=
    (((hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).congr_of_eventuallyEq
      hy).differentiableAt (by norm_num)
  have hzd : DifferentiableAt ℝ zc (t, s) :=
    (((hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).congr_of_eventuallyEq
      hzc).differentiableAt (by norm_num)
  have hdt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r ↦ F (r, s)) t :=
    hFat.comp t (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hds : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun q ↦ F (t, q)) s :=
    hFat.comp s (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hytt : DifferentiableAt ℝ (fun r ↦ y (r, s)) t := by
    change DifferentiableAt ℝ (y ∘ fun r : ℝ ↦ (r, s)) t
    exact hyd.comp t ((hasDerivAt_id t).prodMk (hasDerivAt_const t s)).differentiableAt
  have hzts : DifferentiableAt ℝ (fun r ↦ zc (r, s)) t := by
    change DifferentiableAt ℝ (zc ∘ fun r : ℝ ↦ (r, s)) t
    exact hzd.comp t ((hasDerivAt_id t).prodMk (hasDerivAt_const t s)).differentiableAt
  have hytq : DifferentiableAt ℝ (fun q ↦ y (t, q)) s := by
    change DifferentiableAt ℝ (y ∘ fun q : ℝ ↦ (t, q)) s
    exact hyd.comp s ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)).differentiableAt
  have hpair := gauss_along_curve_pairing_derivative g (fun r ↦ F (r, s))
    (fun r ↦ T (r, s)) (fun r ↦ S (r, s)) t hdt hytt hzts
  have henergy := gauss_along_curve_pairing_derivative g (fun q ↦ F (t, q))
    (fun q ↦ T (t, q)) (fun q ↦ T (t, q)) s hds hytq hytq
  have hm := gauss_mixed_covariant_derivatives g F U hU hF t s hz
  dsimp only [T, S] at hpair henergy
  rw [hgeod, hm] at hpair
  simp only [map_zero, zero_apply, zero_add] at hpair
  rw [henergy.deriv]
  convert hpair using 1
  rw [g.symm]
  ring

end HolomorphicAnosov


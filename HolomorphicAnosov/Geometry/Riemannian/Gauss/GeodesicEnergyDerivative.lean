import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateMetricCompatibility
import HolomorphicAnosov.Geometry.Riemannian.Gauss.NativeCoordinatePairing
import HolomorphicAnosov.Geometry.Riemannian.Gauss.GeodesicCoordinateEquation
import HolomorphicAnosov.Geometry.Riemannian.Gauss.CoordinateCurveVelocity
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The squared speed of a Levi-Civita geodesic has derivative zero. (Gallier–Quaintance, Prop.
15.12, pp.437–438; Def. 16.4, p.444) -/
theorem gauss_geodesic_energy_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (γ : ℝ → M) (J : Set ℝ) (hJ : IsOpen J)
    (hγ : IsConnectionGeodesicOn (riemannianConnection g) γ J) (t : ℝ) (ht : t ∈ J)
    (hp : (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M) ∈ c.source) :
    HasDerivAt (fun r ↦ g.inner (γ r) (curveVelocity γ r) (curveVelocity γ r)) 0 t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let ψ : E → M := fun z ↦ (c.symm z : M)
  let x : ℝ → E := connectionChartMap c ∘ γ
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦
    (g.inner (ψ z)).bilinearComp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ z)
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ψ c.target :=
    contMDiff_subtype_val.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hc)
  have hB : ContDiffOn ℝ ∞ B c.target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    exact gauss_smooth_metric_pullback_entry g c.open_target ψ hψ v w
  have hx : ContDiffAt ℝ ∞ x t := by
    exact contMDiffAt_iff_contDiffAt.mp
      ((gauss_connectionChartMap_smooth c hc (γ t) hp).comp t
        (hγ.1.contMDiffAt (hJ.mem_nhds ht)))
  have hxd : HasDerivAt x (deriv x t) t := (hx.differentiableAt (by simp)).hasDerivAt
  have hTd : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    ((hx.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hBt : ContDiffAt ℝ ∞ B (x t) :=
    hB.contDiffAt (c.open_target.mem_nhds (c.map_source hp))
  let Bd := fderiv ℝ B (x t) (deriv x t)
  have hBd : HasFDerivAt B (fderiv ℝ B (x t)) (x t) :=
    (hBt.differentiableAt (by simp)).hasFDerivAt
  have hdB : HasDerivAt (B ∘ x) Bd t := hBd.comp_hasDerivAt t hxd
  have hd := (hdB.clm_apply hTd).clm_apply hTd
  let A := connectionChristoffelBilinear (E := E) (riemannianConnection g)
    b c hc (γ t) (deriv x t) (deriv x t)
  have hcompat : Bd (deriv x t) (deriv x t) =
      B (x t) A (deriv x t) + B (x t) (deriv x t) A := by
    have hentry := (hBd.clm_apply
      (hasFDerivAt_const (deriv x t) (x t))).clm_apply
      (hasFDerivAt_const (deriv x t) (x t))
    have he := congrArg (fun f : E →L[ℝ] ℝ ↦ f (deriv x t)) hentry.fderiv
    have hc' := gauss_coordinate_metric_compatibility g b c hc
      ⟨γ t, mem_univ (γ t)⟩ hp (deriv x t) (deriv x t) (deriv x t)
    dsimp only at hc'
    change fderiv ℝ (fun z ↦ B z (deriv x t) (deriv x t)) (x t) (deriv x t) = _ at hc'
    change _ = B (x t) A (deriv x t) + B (x t) (deriv x t) A at hc'
    rw [he] at hc'
    simpa [Bd] using hc'
  have hgeod : deriv (deriv x) t + A = 0 :=
    gauss_geodesic_coordinate_equation (riemannianConnection g) b c hc γ J hJ hγ t ht hp
  have hzero : Bd (deriv x t) (deriv x t) +
      B (x t) (deriv (deriv x) t) (deriv x t) +
      B (x t) (deriv x t) (deriv (deriv x) t) = 0 := by
    calc
      _ = B (x t) (deriv (deriv x) t + A) (deriv x t) +
          B (x t) (deriv x t) (deriv (deriv x) t + A) := by
        simp only [hcompat, map_add, add_apply]
        ring
      _ = 0 := by rw [hgeod]; simp
  have hz : HasDerivAt (fun r ↦ B (x r) (deriv x r) (deriv x r)) 0 t := by
    simpa only [Function.comp_apply, add_apply, hzero] using hd
  apply hz.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun r ↦ (⟨γ r, mem_univ (γ r)⟩ : ConnectionWhole M)) t :=
    ((continuous_id.subtype_mk fun p : M ↦ mem_univ p).continuousAt).comp
      (hγ.1.contMDiffAt (hJ.mem_nhds ht)).continuousAt
  filter_upwards [hJ.mem_nhds ht, hcont.eventually (c.open_source.mem_nhds hp)] with r hr hrc
  have hvel := gauss_coordinate_curveVelocity c hc γ r
    ((hγ.1.contMDiffAt (hJ.mem_nhds hr)).mdifferentiableAt (by simp)) hrc
  have hpair := gauss_native_coordinate_pairing g c hc (γ r) hrc
    (curveVelocity γ r) (curveVelocity γ r)
  change B (x r) (alongCurveCoordinate c γ (curveVelocity γ) r)
    (alongCurveCoordinate c γ (curveVelocity γ) r) = _ at hpair
  rw [hvel] at hpair
  exact hpair.symm

end HolomorphicAnosov

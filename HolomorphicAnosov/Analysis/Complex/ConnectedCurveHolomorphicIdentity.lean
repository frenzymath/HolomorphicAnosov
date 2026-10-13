import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter ChartedSpace IsManifold
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- Holomorphic maps from a connected complex curve to a
Hausdorff complex curve agree globally if they agree on a nonempty intrinsic open set.
This is the identity-principle step of the global holonomy comparison in Ghys,
Theorem B, pp.597–598 (literature/ghys.txt:620–625,655–663), expanded here in
charts. Let A be the points of local agreement. It is open and nonempty. At a
closure point, continuity and Hausdorffness give equal values. Choose one common
target chart and a small source coordinate disk mapping into it under both maps.
The two coordinate maps are analytic on this disk. It meets A, so the analytic
identity principle gives equality on the disk. Thus A is closed, and connectedness
implies that it is the whole original curve. No global affine coordinate is assumed. -/
theorem connected_curve_holomorphic_eq_of_open_germ
    {L : Type*} [TopologicalSpace L] [ConnectedSpace L]
    [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace (ComplexModel 1) N] [IsManifold (complexModel 1) ∞ N]
    (F G : L → N)
    (hF : ContMDiff (complexModel 1) (complexModel 1) ∞ F)
    (hG : ContMDiff (complexModel 1) (complexModel 1) ∞ G)
    (U : Set L) (hU : IsOpen U) (hne : U.Nonempty) (hFG : EqOn F G U) : F = G := by
  let A : Set L := {x | F =ᶠ[𝓝 x] G}
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAn : A.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hFG⟩
  have hAc : IsClosed A := by
    apply isClosed_of_closure_subset
    intro x hx
    have heq : F x = G x :=
      closure_minimal (fun y hy ↦ Filter.Eventually.self_of_nhds (show F =ᶠ[𝓝 y] G from hy))
        (isClosed_eq hF.continuous hG.continuous) hx
    let c := chartAt (ComplexModel 1) x
    let d := chartAt (ComplexModel 1) (F x)
    let e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
    let V : Set L := F ⁻¹' d.source ∩ G ⁻¹' d.source
    have hVo : IsOpen V :=
      (d.open_source.preimage hF.continuous).inter (d.open_source.preimage hG.continuous)
    have hxV : x ∈ V := by
      refine ⟨mem_chart_source _ _, ?_⟩
      change G x ∈ d.source
      rw [← heq]
      exact mem_chart_source _ _
    let W : Set ℂ := e.symm ⁻¹' (c.target ∩ c.symm ⁻¹' V)
    have hWo : IsOpen W :=
      (c.isOpen_inter_preimage_symm hVo).preimage e.symm.continuous
    have hxW : e (c x) ∈ W := by
      simp only [W, mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
      exact ⟨c.map_source (mem_chart_source _ _), by simpa only [mem_preimage, c.left_inv (mem_chart_source _ _)] using hxV⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo (e (c x)) hxW
    let B := Metric.ball (e (c x)) r
    let f : ℂ → ℂ := fun z ↦ e (d (F (c.symm (e.symm z))))
    let g : ℂ → ℂ := fun z ↦ e (d (G (c.symm (e.symm z))))
    have hrep (H : L → N)
        (hH : ContMDiff (complexModel 1) (complexModel 1) ∞ H)
        (hHV : ∀ y ∈ V, H y ∈ d.source) : AnalyticOnNhd ℂ
          (fun z ↦ e (d (H (c.symm (e.symm z))))) B := by
      apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
      have hpre : ContMDiffOn 𝓘(ℂ, ℂ) (complexModel 1) ∞
          (fun z ↦ c.symm (e.symm z)) B :=
        contMDiffOn_chart_symm.comp e.symm.contDiff.contMDiff.contMDiffOn
          (fun z hz ↦ (hball hz).1)
      have hh : ContMDiffOn 𝓘(ℂ, ℂ) (complexModel 1) ∞
          (fun z ↦ d (H (c.symm (e.symm z)))) B :=
        contMDiffOn_chart.comp (hH.comp_contMDiffOn hpre)
          (fun z hz ↦ hHV _ (hball hz).2)
      have hscalar : ContDiffOn ℂ 1
          (fun z ↦ e (d (H (c.symm (e.symm z))))) B :=
        (e.contDiff.contMDiff.comp_contMDiffOn hh).contDiffOn.of_le (by simp)
      exact hscalar.differentiableOn_one
    have hf := hrep F hF (fun y hy ↦ hy.1)
    have hg := hrep G hG (fun y hy ↦ hy.2)
    let N : Set L := c.source ∩ (fun y ↦ e (c y)) ⁻¹' B
    have hNo : IsOpen N :=
      c.isOpen_inter_preimage (Metric.isOpen_ball.preimage e.continuous)
    have hxN : x ∈ N := ⟨mem_chart_source _ _, Metric.mem_ball_self hr⟩
    obtain ⟨y, hyN, hyA⟩ := mem_closure_iff.mp hx N hNo hxN
    have hyB : e (c y) ∈ B := hyN.2
    have hnear : f =ᶠ[𝓝 (e (c y))] g := by
      have hcont : ContinuousAt (fun z ↦ c.symm (e.symm z)) (e (c y)) :=
        (show ContinuousAt c.symm (e.symm (e (c y))) by
          simpa using c.symm.continuousAt (c.map_source hyN.1)).comp e.symm.continuousAt
      have hlim : Tendsto (fun z ↦ c.symm (e.symm z)) (𝓝 (e (c y))) (𝓝 y) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply, c.left_inv hyN.1] using hcont.tendsto
      exact (hlim.eventually hyA).mono (fun z hz ↦ congrArg (fun q ↦ e (d q)) hz)
    have hlocal : EqOn f g B :=
      hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball _ _).isPreconnected hyB hnear
    apply Filter.eventuallyEq_of_mem (hNo.mem_nhds hxN)
    intro y hy
    have hc : c.symm (e.symm (e (c y))) = y := by simp [c.left_inv hy.1]
    have hyV : y ∈ V := by
      have hh := (hball hy.2).2
      change c.symm (e.symm (e (c y))) ∈ V at hh
      rwa [hc] at hh
    apply d.injOn hyV.1 hyV.2
    apply e.injective
    simpa only [f, g, hc] using hlocal hy.2
  have hAall : A = univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ hAn
  funext x
  have hxA : x ∈ A := hAall.symm ▸ mem_univ x
  exact Filter.Eventually.self_of_nhds (p := fun y ↦ F y = G y) hxA

end HolomorphicAnosov.Ghys

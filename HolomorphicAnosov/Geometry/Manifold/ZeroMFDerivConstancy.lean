import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

/-! This file proves constancy of differentiable manifold-valued maps with zero differential on open
preconnected vector-space domains. (Lee, Prop. 6.10, p. 134; Prop. 19.12, pp. 504–505) -/

open Set Filter IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- A differentiable manifold-valued map on an open preconnected vector-space domain is constant if
its manifold differential vanishes there. (Lee, Prop. 6.10, p. 134; Prop. 19.12, pp. 504–505) -/
theorem eq_of_mfderiv_eq_zero_on
    {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (g : E → M) (hg : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) g U)
    (hzero : ∀ x ∈ U, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x = 0)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) : g x = g y := by
  have hloc : IsLocallyConstant (fun z : U ↦ g z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    let c := chartAt F (g z.val)
    let V := U ∩ g ⁻¹' c.source
    have hV : IsOpen V := hg.continuousOn.isOpen_inter_preimage hU c.open_source
    have hz : z.val ∈ V := ⟨z.property, mem_chart_source F (g z.val)⟩
    have hc (w : E) (hw : w ∈ V) :
        MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) c (g w) :=
      (contMDiffAt_of_mem_maximalAtlas
        (chart_mem_maximalAtlas (I := 𝓘(ℝ, F)) (n := ∞) (g z.val))
        hw.2).mdifferentiableAt (by simp)
    have hd (w : E) (hw : w ∈ V) :
        MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) g w :=
      hg.mdifferentiableAt (hU.mem_nhds hw.1)
    have hdiff : DifferentiableOn ℝ (c ∘ g) V := fun w hw ↦
      ((hc w hw).comp w (hd w hw)).differentiableAt.differentiableWithinAt
    have hderiv : V.EqOn (fderiv ℝ (c ∘ g)) 0 := by
      intro w hw
      change fderiv ℝ (c ∘ g) w = 0
      rw [← mfderiv_eq_fderiv, mfderiv_comp w (hc w hw) (hd w hw), hzero w hw.1]
      exact ContinuousLinearMap.comp_zero _
    have hopen := hV.isOpen_inter_preimage_of_fderiv_eq_zero hdiff hderiv {c (g z.val)}
    have hn : V ∩ (c ∘ g) ⁻¹' {c (g z.val)} ∈ 𝓝 z.val :=
      hopen.mem_nhds ⟨hz, rfl⟩
    filter_upwards [continuous_subtype_val.continuousAt.eventually hn] with w hw
    exact c.injOn hw.1.2 hz.2 hw.2
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩


end HolomorphicAnosov

import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Compatible immersion charts send the range of the immersion differential to the horizontal
linear plane (Lee, Prop. 8.27, pp.192–193). -/

noncomputable section
open Set Filter Function
open scoped Topology _root_.Topology ContDiff Manifold Bundle
namespace HolomorphicAnosov.Theorem12NativePlaque
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace E L] [ChartedSpace H M]

/-- The codomain chart differential sends the immersion differential range to the horizontal linear
plane at every point of the domain chart source (Lee, Prop. 8.27, pp.192–193). -/
theorem immersion_chart_tangent_range {f : L → M} {x z : L}
    (h : Manifold.IsImmersionAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) ∞ f x) (hz : z ∈ h.domChart.source) :
    (LinearMap.range (mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) f z).toLinearMap).map
      (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
        h.codChart (f z)).toLinearMap =
    LinearMap.range
      (h.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ E h.complement)).toLinearMap := by
  let A : E →L[ℝ] H := h.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E h.complement)
  have hd : h.domChart.MDifferentiable (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
     (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hc : h.codChart.MDifferentiable (modelWithCornersSelf ℝ H)
      (modelWithCornersSelf ℝ H) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
     (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hf := (h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds hz)).mdifferentiableAt
    (by simp)
  have hcz := h.source_subset_preimage_source hz
  have heq : (h.codChart ∘ f) =ᶠ[𝓝 z] (A ∘ h.domChart) := by
    filter_upwards [h.domChart.open_source.mem_nhds hz] with t ht
    have hh := h.writtenInCharts
      ((h.domChart.extend (modelWithCornersSelf ℝ E)).map_source' (by simpa using ht))
    simpa [A, Function.comp_apply, h.domChart.left_inv ht] using hh
  have hder : (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
      h.codChart (f z)).comp
      (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ H) f z) =
      A.comp (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        h.domChart z) := by
    rw [← mfderiv_comp z (hc.mdifferentiableAt hcz) hf, heq.mfderiv_eq,
      mfderiv_comp z A.mdifferentiableAt (hd.mdifferentiableAt hz)]
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  rw [← LinearMap.range_comp]
  change LinearMap.range ((mfderiv (modelWithCornersSelf ℝ H)
    (modelWithCornersSelf ℝ H) h.codChart (f z)).comp
    (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ H) f z)).toLinearMap = _
  rw [hder]
  exact LinearMap.range_comp_of_range_eq_top _ (hd.range_mfderiv_eq_top hz)

end HolomorphicAnosov.Theorem12NativePlaque


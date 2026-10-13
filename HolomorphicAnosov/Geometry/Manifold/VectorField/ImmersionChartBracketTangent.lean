import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionChartTangentRange
import HolomorphicAnosov.Geometry.Manifold.VectorField.LieBracketMemLinearRange

/-! In an immersion chart, the Lie bracket of differentiable vector fields tangent to the immersion
derivative image is tangent to that image (Lee, Prop. 8.27, pp.192–193, Cor. 8.28, p.193). -/

noncomputable section
open Set Filter Function
open scoped Topology _root_.Topology ContDiff Manifold Bundle
namespace HolomorphicAnosov.Theorem12NativePlaque
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace E L] [ChartedSpace H M]

/-- Differentiable vector fields tangent to the immersion derivative image near the centre of a
compatible chart have a Lie bracket tangent to that image at the centre (Lee, Prop. 8.27,
pp.192–193, Cor. 8.28, p.193). -/
theorem immersion_chart_bracket_tangent {f : L → M} {x : L}
    (h : Manifold.IsImmersionAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) ∞ f x)
    (P : M → Submodule ℝ H)
    (hP : ∀ z, LinearMap.range (mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) f z).toLinearMap = P (f z))
    {V W : H → H}
    (hV : DifferentiableAt ℝ V (h.codChart (f x)))
    (hW : DifferentiableAt ℝ W (h.codChart (f x)))
    (hVtan : ∀ᶠ z in 𝓝 x, V (h.codChart (f z)) ∈
      (P (f z)).map (mfderiv (modelWithCornersSelf ℝ H)
        (modelWithCornersSelf ℝ H) h.codChart (f z)).toLinearMap)
    (hWtan : ∀ᶠ z in 𝓝 x, W (h.codChart (f z)) ∈
      (P (f z)).map (mfderiv (modelWithCornersSelf ℝ H)
        (modelWithCornersSelf ℝ H) h.codChart (f z)).toLinearMap) :
    VectorField.lieBracket ℝ V W (h.codChart (f x)) ∈
      (P (f x)).map (mfderiv (modelWithCornersSelf ℝ H)
        (modelWithCornersSelf ℝ H) h.codChart (f x)).toLinearMap := by
  let A : E →L[ℝ] H := h.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E h.complement)
  let B : H →L[ℝ] E := (ContinuousLinearMap.fst ℝ E h.complement).comp
    h.equiv.symm.toContinuousLinearMap
  have hBA : ∀ u, B (A u) = u := by
    intro u
    simp [A, B]
  have hpos : ∀ u ∈ h.domChart.target,
      h.codChart (f (h.domChart.symm u)) = A u := by
    intro u hu
    simpa [A, Function.comp_apply] using h.writtenInCharts (by simpa using hu)
  have hx := h.mem_domChart_source
  have hcenter : h.codChart (f x) = A (h.domChart x) := by
    simpa only [h.domChart.left_inv hx] using hpos (h.domChart x) (h.domChart.map_source hx)
  have hdT : Tendsto h.domChart.symm (𝓝 (h.domChart x)) (𝓝 x) := by
    simpa only [ContinuousAt, h.domChart.left_inv hx] using
      (h.domChart.continuousAt_symm (h.domChart.map_source hx))
  have hVplane : ∀ᶠ u in 𝓝 (h.domChart x), V (A u) ∈ A.range := by
    filter_upwards [hdT.eventually hVtan,
      h.domChart.open_target.mem_nhds (h.domChart.map_source hx)] with u ht hu
    have hz := h.domChart.map_target hu
    rw [← hP (h.domChart.symm u), immersion_chart_tangent_range h hz] at ht
    rcases ht with ⟨a, ha⟩
    exact ⟨a, by simpa only [hpos u hu] using ha⟩
  have hWplane : ∀ᶠ u in 𝓝 (h.domChart x), W (A u) ∈ A.range := by
    filter_upwards [hdT.eventually hWtan,
      h.domChart.open_target.mem_nhds (h.domChart.map_source hx)] with u ht hu
    have hz := h.domChart.map_target hu
    rw [← hP (h.domChart.symm u), immersion_chart_tangent_range h hz] at ht
    rcases ht with ⟨a, ha⟩
    exact ⟨a, by simpa only [hpos u hu] using ha⟩
  rw [← hP x, immersion_chart_tangent_range h hx, hcenter]
  apply lieBracket_mem_linear_range A B hBA
  · simpa only [hcenter] using hV
  · simpa only [hcenter] using hW
  · exact hVplane
  · exact hWplane

end HolomorphicAnosov.Theorem12NativePlaque


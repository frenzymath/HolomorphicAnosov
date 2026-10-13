import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

/-!
Vanishing of covariant differentiation along a curve is equivalent to vanishing of its canonical
coordinate expression. (Andrews, Prop. 8.4.1, pp.74–75)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The covariant derivative of a field along a curve vanishes if and only if its canonical
coordinate covariant derivative vanishes. (Andrews, Prop. 8.4.1, pp.74–75) -/
theorem covariantDerivativeAlongCurve_eq_zero_iff
    (nabla : SmoothAffineConnection E M) (γ : ℝ → M)
    (Z : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (γ t)) (t : ℝ) :
    covariantDerivativeAlongCurve nabla γ Z t = 0 ↔
      let c := chartAt E (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
      let hc := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
        (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
      covariantDerivativeCoordinate nabla (Module.finBasis ℝ E) c hc γ Z t = 0 := by
  let c := chartAt E (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M)
  have heq := (⊤ : Opens M).chartAt_subtype_val_symm_eventuallyEq
    (H := E) (x := (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M))
  change (chartAt E (γ t)).symm =ᶠ[𝓝 (connectionChartMap c (γ t))]
    connectionChartInverse c at heq
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E (γ t)).symm
      (connectionChartMap c (γ t)) = ContinuousLinearMap.id ℝ E := by
    simpa [c, connectionChartMap] using! (mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, E)) (x := γ t))
  unfold covariantDerivativeAlongCurve
  change ((tangentSpaceCastModel 𝓘(ℝ, E) (γ t)).symm
    ((tangentSpaceCastModel 𝓘(ℝ, E) _)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c)
        (connectionChartMap c (γ t)) _)) = 0) ↔ _
  have hdModel := congrArg (fun D ↦ (tangentSpaceCastModel 𝓘(ℝ, E)
    ((chartAt E (γ t)).symm (connectionChartMap c (γ t)))).toContinuousLinearMap.comp D) hd
  simp only [hid] at hdModel
  change ContinuousLinearMap.id ℝ E = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c)
    (connectionChartMap c (γ t)) at hdModel
  rw [← hdModel]
  rfl

end
end HolomorphicAnosov


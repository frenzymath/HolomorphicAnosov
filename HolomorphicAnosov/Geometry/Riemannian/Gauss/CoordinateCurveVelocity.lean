import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChartMapSmooth

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The coordinate representative of a curve's velocity equals the derivative of its chart
expression. (Gallier–Quaintance, Prop. 16.7) -/
theorem gauss_coordinate_curveVelocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (γ : ℝ → M) (t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t)
    (hp : (⟨γ t, mem_univ (γ t)⟩ : ConnectionWhole M) ∈ c.source) :
    alongCurveCoordinate c γ (curveVelocity γ) t = deriv (connectionChartMap c ∘ γ) t := by
  have h := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) (x := t)
    ((gauss_connectionChartMap_smooth c hc (γ t) hp).mdifferentiableAt (by simp)) hγ
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (connectionChartMap c ∘ γ) t
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1) =
    alongCurveCoordinate c γ (curveVelocity γ) t at h
  rw [mfderiv_eq_fderiv] at h
  change deriv (connectionChartMap c ∘ γ) t = _ at h
  exact h.symm

end HolomorphicAnosov


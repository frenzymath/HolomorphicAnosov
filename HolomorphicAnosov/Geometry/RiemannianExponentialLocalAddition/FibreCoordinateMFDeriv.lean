import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FibreMFDeriv

/-!
Reusable FibreCoordinateMFDeriv declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FibreInsertionDerivative

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- In the original preferred tangent-bundle model, the fixed-fibre derivative is `inr`. Source: the native tangent/model casts cancel in the preceding exact derivative formula. -/
theorem coordinate_mfderiv_fibreInsertion (p : M) :
    let ι : E → TangentBundle I M := fun v ↦ ⟨p, (tangentSpaceCastModel I p).symm v⟩
    (tangentSpaceCastModel (I.prod 𝓘(ℝ, E)) (ι 0)).toContinuousLinearMap.comp
      ((mfderiv 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ι 0).comp
        (tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.inr ℝ E E := by
  dsimp only
  rw [mfderiv_fibreInsertion]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

end
end HolomorphicAnosov.W07FibreInsertionDerivative

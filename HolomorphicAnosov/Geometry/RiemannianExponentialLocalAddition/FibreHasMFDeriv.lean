import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.FibreChart
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
Reusable FibreHasMFDeriv declarations from the Riemannian exponential construction.
-/ 

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.W07FibreInsertionDerivative

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The derivative of insertion into a fixed tangent fibre is the vertical inclusion in the native tangent-bundle model. The source and target tangent/model casts are explicit. Source: Mathlib's native tangent-bundle charts and derivative of the product insertion. -/
theorem hasMFDerivAt_fibreInsertion (p : M) :
    let ι : E → TangentBundle I M := fun v ↦ ⟨p, (tangentSpaceCastModel I p).symm v⟩
    HasMFDerivAt 𝓘(ℝ, E) (I.prod 𝓘(ℝ, E)) ι 0
      ((tangentSpaceCastModel (I.prod 𝓘(ℝ, E)) (ι 0)).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr ℝ E E).comp
          (tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).toContinuousLinearMap)) := by
  dsimp only
  constructor
  · exact ((FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p).comp
      (tangentSpaceCastModel I p).symm.continuous).continuousAt
  · have hlin :
        (tangentSpaceCastModel (I.prod 𝓘(ℝ, E))
          (⟨p, (tangentSpaceCastModel I p).symm 0⟩ : TangentBundle I M)).toContinuousLinearMap.comp
          (((tangentSpaceCastModel (I.prod 𝓘(ℝ, E))
            (⟨p, (tangentSpaceCastModel I p).symm 0⟩ : TangentBundle I M)).symm.toContinuousLinearMap.comp
              ((ContinuousLinearMap.inr ℝ E E).comp
                (tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).toContinuousLinearMap)).comp
                  (tangentSpaceCastModel 𝓘(ℝ, E) (0 : E)).symm.toContinuousLinearMap) =
        ContinuousLinearMap.inr ℝ E E := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearMap.comp_assoc] at hlin ⊢
    rw [hlin]
    rw [𝓘(ℝ, E).range_eq_univ]
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id, id_eq]
    change HasFDerivWithinAt
      (fun v : E ↦ extChartAt (I.prod 𝓘(ℝ, E))
        (⟨p, (tangentSpaceCastModel I p).symm 0⟩ : TangentBundle I M)
        (⟨p, (tangentSpaceCastModel I p).symm v⟩ : TangentBundle I M))
      (ContinuousLinearMap.inr ℝ E E) Set.univ 0
    have heq : (fun v : E ↦ extChartAt (I.prod 𝓘(ℝ, E))
        (⟨p, (tangentSpaceCastModel I p).symm 0⟩ : TangentBundle I M)
        (⟨p, (tangentSpaceCastModel I p).symm v⟩ : TangentBundle I M)) =
        fun v ↦ (extChartAt I p p, v) := by
      funext v
      simpa only [map_zero] using fibre_chart (I := I) p v
    rw [heq]
    exact (hasFDerivAt_prodMk_right (extChartAt I p p) (0 : E)).hasFDerivWithinAt

end
end HolomorphicAnosov.W07FibreInsertionDerivative

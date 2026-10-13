import Mathlib.Analysis.Normed.Operator.NormedSpace
import HolomorphicAnosov.Paper.Zhang.Anosov

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
variable {V W V' W' : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- The stable forward and unstable inverse operator norms are preserved under the supplied tensor isometries. -/
theorem conjugate_operator_norms
    (T : V ≃L[ℝ] W) (T' : V' ≃L[ℝ] W')
    (D : V ≃L[ℝ] V') (D' : W ≃L[ℝ] W')
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hT' : ∀ v, ‖T' v‖ = ‖v‖)
    (hD : D'.toContinuousLinearMap.comp T.toContinuousLinearMap =
      T'.toContinuousLinearMap.comp D.toContinuousLinearMap) :
    ‖D'.toContinuousLinearMap‖ = ‖D.toContinuousLinearMap‖ ∧
      ‖D'.symm.toContinuousLinearMap‖ = ‖D.symm.toContinuousLinearMap‖ := by
  let J : V ≃ₗᵢ[ℝ] W := { T.toLinearEquiv with norm_map' := hT }
  let J' : V' ≃ₗᵢ[ℝ] W' := { T'.toLinearEquiv with norm_map' := hT' }
  have hfwd : ‖D'.toContinuousLinearMap‖ = ‖D.toContinuousLinearMap‖ := by
    have heq := congrArg norm hD
    change ‖D'.toContinuousLinearMap.comp J.toContinuousLinearEquiv.toContinuousLinearMap‖ =
      ‖J'.toContinuousLinearEquiv.toContinuousLinearMap.comp D.toContinuousLinearMap‖ at heq
    simpa only [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
      ContinuousLinearMap.opNorm_linearIsometryEquiv_comp] using heq
  refine ⟨hfwd, ?_⟩
  have hinv : D'.symm.toContinuousLinearMap.comp T'.toContinuousLinearMap =
      T.toContinuousLinearMap.comp D.symm.toContinuousLinearMap := by
    ext v
    apply D'.injective
    change D' (D'.symm (T' v)) = D' (T (D.symm v))
    rw [D'.apply_symm_apply]
    have heq := congrArg (fun L ↦ L (D.symm v)) hD
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      D.apply_symm_apply] using heq.symm
  have heq := congrArg norm hinv
  change ‖D'.symm.toContinuousLinearMap.comp J'.toContinuousLinearEquiv.toContinuousLinearMap‖ =
    ‖J.toContinuousLinearEquiv.toContinuousLinearMap.comp D.symm.toContinuousLinearMap‖ at heq
  simpa only [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp] using heq


end
end HolomorphicAnosov.GhysAnosovConjugacy

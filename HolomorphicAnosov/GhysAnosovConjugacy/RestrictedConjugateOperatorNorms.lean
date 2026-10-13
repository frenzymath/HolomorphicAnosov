import Mathlib.Analysis.Normed.Operator.NormedSpace
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateOperatorNorms

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
variable {V W V' W' : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup W'] [NormedSpace ℝ W']

/-- Restricting the tensor isometries to the mapped stable and unstable fibres preserves both block operator-norm identities. -/
theorem restricted_conjugate_operator_norms
    (T : V ≃L[ℝ] W) (T' : V' ≃L[ℝ] W')
    (D : V ≃L[ℝ] V') (D' : W ≃L[ℝ] W')
    (P : Submodule ℝ V) (Q : Submodule ℝ W)
    (P' : Submodule ℝ V') (Q' : Submodule ℝ W')
    (hPQ : P.map T.toLinearEquiv.toLinearMap = Q)
    (hPQ' : P'.map T'.toLinearEquiv.toLinearMap = Q')
    (hPP' : P.map D.toLinearEquiv.toLinearMap = P')
    (hQQ' : Q.map D'.toLinearEquiv.toLinearMap = Q')
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hT' : ∀ v, ‖T' v‖ = ‖v‖)
    (hD : D'.toContinuousLinearMap.comp T.toContinuousLinearMap =
      T'.toContinuousLinearMap.comp D.toContinuousLinearMap) :
    ‖(D'.ofSubmodules Q Q' hQQ').toContinuousLinearMap‖ =
      ‖(D.ofSubmodules P P' hPP').toContinuousLinearMap‖ ∧
    ‖(D'.ofSubmodules Q Q' hQQ').symm.toContinuousLinearMap‖ =
      ‖(D.ofSubmodules P P' hPP').symm.toContinuousLinearMap‖ := by
  apply conjugate_operator_norms (T.ofSubmodules P Q hPQ)
    (T'.ofSubmodules P' Q' hPQ')
  · intro v
    exact hT v.val
  · intro v
    exact hT' v.val
  · ext v
    exact congrArg (fun L ↦ L v.val) hD


end
end HolomorphicAnosov.GhysAnosovConjugacy

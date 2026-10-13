import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Neumann-series invertibility for operators close to the identity. (Bochner–Montgomery, Lemma 2.) -/

noncomputable section

namespace HolomorphicAnosov

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- A continuous linear map at operator-norm distance less than one from the identity is the forward map of a continuous linear equivalence. -/
theorem average_jacobian_invertible_g1
    (T : E →L[ℝ] E)
    (hT : ‖ContinuousLinearMap.id ℝ E - T‖ < 1) :
    ∃ A : E ≃L[ℝ] E, A.toContinuousLinearMap = T := by
  obtain ⟨a, ha⟩ := isUnit_one_sub_of_norm_lt_one hT
  let A := ContinuousLinearEquiv.ofUnit a
  refine ⟨A, ?_⟩
  change (a : E →L[ℝ] E) = T
  rw [ha]
  rw [show (1 : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E by rfl]
  abel

end HolomorphicAnosov


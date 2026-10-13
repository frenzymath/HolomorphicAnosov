import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Pullback of a vector field through an inverse chart agrees with pushforward by the chart
differential. -/

noncomputable section
open Set Filter Function
open scoped Topology _root_.Topology ContDiff Manifold Bundle
namespace HolomorphicAnosov.Theorem12NativePlaque
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace E L] [ChartedSpace H M]

/-- Pulling a vector field back through an inverse chart at `c p` equals applying the forward chart
differential at `p` to the field value. -/
theorem chart_inverse_mpullback_eq
    (c : OpenPartialHomeomorph M H)
    (hc : c.MDifferentiable (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H))
    {p : M} (hp : p ∈ c.source)
    (V : ∀ p : M, TangentSpace (modelWithCornersSelf ℝ H) p) :
    VectorField.mpullback (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
      c.symm V (c p) =
    mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c p (V p) := by
  rw [VectorField.mpullback_apply]
  have hi : (mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
      c.symm (c p)).inverse =
      mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) c p := by
    apply ContinuousLinearMap.inverse_eq
    · exact hc.symm_comp_deriv hp
    · have hh := hc.comp_symm_deriv (c.map_source hp)
      rw [c.left_inv hp] at hh
      exact hh
  rw [hi, c.left_inv hp]

end HolomorphicAnosov.Theorem12NativePlaque


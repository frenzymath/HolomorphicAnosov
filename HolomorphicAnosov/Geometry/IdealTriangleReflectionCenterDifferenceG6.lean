import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- After reflection, subtracting the selected orthogonal-circle center cancels the variable conjugate term. -/
theorem idealDiskSideReflection_sub_orthogonalCenter_g6
    {p q z : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hs : p + q ≠ 0) (hz : ‖z‖ < 1) :
    idealDiskSideReflection p q z - orthogonalCenter p q =
      ((p + q) ^ 2 - 4 * p * q) /
        ((p + q) * (2 - (p + q) * conj z)) := by
  have hd : 2 - (p + q) * conj z ≠ 0 :=
    idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz
  unfold idealDiskSideReflection orthogonalCenter
  field_simp [hs, hd]
  ring

end HolomorphicAnosov.IdealDiskTriangle

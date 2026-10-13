import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceIdentityG6

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- In the non-antipodal case, reflection transports the signed side half-space. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_halfspace_sign_nonantipodal_g6
    {p q z r : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : p ≠ q) (hz : ‖z‖ < 1) (hs : p + q ≠ 0) :
    (0 ≤ sideEquation p q (idealDiskSideReflection p q z) *
      sideEquation p q r) ↔
      (sideEquation p q z * sideEquation p q r ≤ 0) := by
  have hi := idealDiskSideReflection_sideEquation_identity_nonantipodal_g6 hp hq hs hz
  have hv : 0 < Complex.normSq (2 - (p + q) * conj z) :=
    Complex.normSq_pos.mpr (idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz)
  have hg := ideal_reflection_gap_pos_g6 hp hq hpq
  have he : (sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q r) *
      Complex.normSq (2 - (p + q) * conj z) =
      -(4 - Complex.normSq (p + q)) *
        (sideEquation p q z * sideEquation p q r) := by
    linear_combination sideEquation p q r * hi
  constructor
  · intro h
    by_contra h'
    have hy : 0 < sideEquation p q z * sideEquation p q r := lt_of_not_ge h'
    have hx := mul_nonneg h hv.le
    have hy' := mul_pos hg hy
    nlinarith [he]
  · intro h
    have hy := mul_nonpos_of_nonneg_of_nonpos hg.le h
    have hx : 0 ≤
        (sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q r) *
          Complex.normSq (2 - (p + q) * conj z) := by
      nlinarith [he]
    exact (mul_nonneg_iff_of_pos_right hv).mp hx

end HolomorphicAnosov.IdealDiskTriangle

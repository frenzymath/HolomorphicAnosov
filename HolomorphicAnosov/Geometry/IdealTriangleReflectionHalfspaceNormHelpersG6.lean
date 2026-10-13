import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterDifferenceG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterConjugateG6

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The norm square of the non-antipodal orthogonal-circle center. -/
theorem idealTriangle_orthogonalCenter_normSq_g6
    {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (_hs : p + q ≠ 0) :
    Complex.normSq (orthogonalCenter p q) =
      4 / Complex.normSq (p + q) := by
  unfold orthogonalCenter
  rw [Complex.normSq_div, Complex.normSq_mul]
  have hp' : Complex.normSq p = 1 := by
    rw [Complex.normSq_eq_norm_sq, hp]
    norm_num
  have hq' : Complex.normSq q = 1 := by
    rw [Complex.normSq_eq_norm_sq, hq]
    norm_num
  rw [Complex.normSq_mul, hp', hq']
  norm_num

/-- The norm square of the reflected-center numerator. -/
theorem idealTriangle_reflection_centerNumerator_normSq_g6
    {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    Complex.normSq ((p + q) ^ 2 - 4 * p * q) =
      (4 - Complex.normSq (p + q)) ^ 2 := by
  have hp' : Complex.normSq p = 1 := by
    rw [Complex.normSq_eq_norm_sq, hp]
    norm_num
  have hq' : Complex.normSq q = 1 := by
    rw [Complex.normSq_eq_norm_sq, hq]
    norm_num
  have he : (p + q) ^ 2 - 4 * p * q = (p - q) ^ 2 := by ring
  rw [he]
  rw [show (p - q) ^ 2 = (p - q) * (p - q) by ring, Complex.normSq_mul]
  rw [Complex.normSq_sub, Complex.normSq_add, hp', hq']
  ring

/-- The original side equation expressed through the reflection denominator. -/
theorem idealTriangle_sideEquation_denominator_normSq_g6
    {p q z : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hs : p + q ≠ 0) :
    Complex.normSq (p + q) * sideEquation p q z =
      Complex.normSq (2 - (p + q) * conj z) -
        (4 - Complex.normSq (p + q)) := by
  obtain ⟨ht, hst⟩ := ideal_reflection_coefficients_g6 hp hq
  have hc : (p + q) * orthogonalCenter p q = 2 * (p * q) := by
    unfold orthogonalCenter
    field_simp
  have he : (p + q) * (z - orthogonalCenter p q) =
      -(p * q) * conj (2 - (p + q) * conj z) := by
    simp only [map_sub, map_mul, map_ofNat, Complex.conj_conj]
    linear_combination -z * hst - hc
  have hn := congrArg Complex.normSq he
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_conj, ht,
    one_mul] at hn
  have hcn := idealTriangle_orthogonalCenter_normSq_g6 hp hq hs
  have hu : Complex.normSq (p + q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hs)
  have hcn' : Complex.normSq (p + q) *
      Complex.normSq (orthogonalCenter p q) = 4 := by
    rw [hcn]
    field_simp
  simp only [sideEquation, ite_eq_right hs, Complex.sq_norm]
  nlinarith [hn, hcn']

end HolomorphicAnosov.IdealDiskTriangle

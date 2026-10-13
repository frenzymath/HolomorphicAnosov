import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- For antipodal endpoints, reflection transports the signed side coordinate with reversed sign. -/
theorem idealDiskSideReflection_halfspace_sign_antipodal_g6 {p q z r : ℂ}
    (hp : ‖p‖ = 1) (_hq : ‖q‖ = 1) (_hpq : p ≠ q) (_hz : ‖z‖ < 1)
    (hs : p + q = 0) :
    (0 ≤ sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q r) ↔
      (sideEquation p q z * sideEquation p q r ≤ 0) := by
  have hq' : q = -p := by linear_combination hs
  have hane : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hau : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
    norm_num
  have he : idealDiskSideReflection p q z / p = conj (z / p) := by
    unfold idealDiskSideReflection
    rw [hq']
    simp only [map_div₀]
    have hcan : conj p ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hane
    field_simp
    ring_nf
    calc
      p * conj z * conj p * 2 = (p * conj p) * conj z * 2 := by ring
      _ = conj z * 2 := by rw [hau]; ring
  simp only [sideEquation, ite_eq_left hs]
  rw [he, Complex.conj_im, neg_mul]
  exact neg_nonneg

end HolomorphicAnosov.IdealDiskTriangle

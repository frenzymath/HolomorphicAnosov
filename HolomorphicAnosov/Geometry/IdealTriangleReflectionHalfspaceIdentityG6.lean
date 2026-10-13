import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterDifferenceG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceNormHelpersG6

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- In the non-antipodal case, the reflection satisfies an exact side-equation identity. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_sideEquation_identity_nonantipodal_g6
    {p q z : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hs : p + q ≠ 0) (hz : ‖z‖ < 1) :
    sideEquation p q (idealDiskSideReflection p q z) *
        Complex.normSq (2 - (p + q) * conj z) =
      -(4 - Complex.normSq (p + q)) * sideEquation p q z := by
  let s : ℂ := p + q
  let t : ℂ := p * q
  let D : ℂ := 2 - s * conj z
  let N : ℂ := s ^ 2 - 4 * t
  have hsd : s ≠ 0 := by simpa [s] using hs
  have hnum := idealTriangle_reflection_centerNumerator_normSq_g6 hp hq
  have hcn := idealTriangle_orthogonalCenter_normSq_g6 hp hq hs
  have hdiff := idealDiskSideReflection_sub_orthogonalCenter_g6 hp hq hs hz
  have hden := idealTriangle_sideEquation_denominator_normSq_g6 (z := z) hp hq hs
  have hu : Complex.normSq s ≠ 0 := Complex.normSq_pos.mpr hsd |>.ne'
  have hD : D ≠ 0 := by
    dsimp [D]
    exact idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz
  have hv : Complex.normSq D ≠ 0 := Complex.normSq_pos.mpr hD |>.ne'
  have hR : idealDiskSideReflection p q z - orthogonalCenter p q = N / (s * D) := by
    simpa [s, t, D, N, mul_assoc] using hdiff
  have hnorm : Complex.normSq (idealDiskSideReflection p q z - orthogonalCenter p q) =
      (4 - Complex.normSq s)^2 / (Complex.normSq s * Complex.normSq D) := by
    rw [hR, Complex.normSq_div, Complex.normSq_mul]
    congr 1
    simpa [N, s, t, mul_assoc] using hnum
  have hsideR : sideEquation p q (idealDiskSideReflection p q z) =
      (4 - Complex.normSq s)^2 / (Complex.normSq s * Complex.normSq D) -
        (4 / Complex.normSq s - 1) := by
    simp only [sideEquation, ite_eq_right hs, Complex.sq_norm]
    rw [hnorm, hcn]
  have hsidez : Complex.normSq s * sideEquation p q z =
      Complex.normSq D - (4 - Complex.normSq s) := by
    simpa [s, D] using hden
  rw [hsideR]
  change ((4 - Complex.normSq s)^2 / (Complex.normSq s * Complex.normSq D) -
    (4 / Complex.normSq s - 1)) * Complex.normSq D =
      -(4 - Complex.normSq s) * sideEquation p q z
  field_simp
  linear_combination (4 - Complex.normSq s) * hsidez

end HolomorphicAnosov.IdealDiskTriangle

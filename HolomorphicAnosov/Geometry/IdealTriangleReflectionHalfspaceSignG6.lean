import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceAntipodalG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceNonantipodalG6

noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- Equation-level half-space sign transport for the selected reflected side. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_halfspace_sign_g6 {p q z r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1) :
    (0 ≤ sideEquation p q (idealDiskSideReflection p q z) * sideEquation p q r) ↔
      (sideEquation p q z * sideEquation p q r ≤ 0) := by
  by_cases hs : p + q = 0
  · exact idealDiskSideReflection_halfspace_sign_antipodal_g6 hp hq hpq hz hs
  · exact idealDiskSideReflection_halfspace_sign_nonantipodal_g6 hp hq hpq hz hs

end HolomorphicAnosov.IdealDiskTriangle

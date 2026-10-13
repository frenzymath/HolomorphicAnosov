import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The non-antipodal orthogonal center satisfies (p+q) * conj c = 2 for unit endpoints. -/
theorem idealTriangle_center_conjugate_g6 {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hs : p + q ≠ 0) :
    (p + q) * conj (orthogonalCenter p q) = 2 := by
  unfold orthogonalCenter
  simp only [map_div₀, map_mul, map_add]
  have hsu : conj p + conj q ≠ 0 := by
    rw [← map_add]
    exact (map_ne_zero (starRingEnd ℂ)).mpr hs
  rw [← mul_div_assoc]
  apply (div_eq_iff hsu).mpr
  have hst := (ideal_reflection_coefficients_g6 hp hq).2
  have hstc := congrArg (starRingEnd ℂ) hst
  simp only [map_mul, map_add, Complex.conj_conj] at hstc
  have htwo : (starRingEnd ℂ) 2 = 2 := map_ofNat (starRingEnd ℂ) 2
  rw [htwo]
  calc
    (p + q) * (2 * (starRingEnd ℂ) p * (starRingEnd ℂ) q) =
        2 * ((starRingEnd ℂ) p * (starRingEnd ℂ) q * (p + q)) := by ring
    _ = 2 * ((starRingEnd ℂ) p + (starRingEnd ℂ) q) := by rw [hstc]

end HolomorphicAnosov.IdealDiskTriangle

import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The explicit anti-Möbius side reflection fixes the open geodesic side pointwise. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_fixed_openSide {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (_hpq : p ≠ q)
    {z : ℂ} (hz : z ∈ openSide p q) :
    idealDiskSideReflection p q z = z := by
  obtain ⟨hzd, hside⟩ := hz
  have hd := idealDiskSideReflection_denominator_ne_zero_g6 hp hq hzd
  obtain ⟨ht, hst⟩ := ideal_reflection_coefficients_g6 hp hq
  unfold sideEquation at hside
  split_ifs at hside with hs
  · have hq' : q = -p := by linear_combination hs
    have hpne : p ≠ 0 := by
      intro h
      simp [h] at hp
    have hpu : p * conj p = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
      norm_num
    have hzreal := Complex.conj_eq_iff_im.mpr hside
    simp only [map_div₀] at hzreal
    have hpc : conj p ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hpne
    have hcross := (div_eq_div_iff hpc hpne).mp hzreal
    unfold idealDiskSideReflection
    apply (div_eq_iff hd).mpr
    rw [hq']
    linear_combination 2*p*hcross + 2*z*hpu
  · let c := orthogonalCenter p q
    have hc : c * (p + q) = 2 * (p * q) := by
      dsimp [c, orthogonalCenter]
      field_simp
    have hsc : (p + q) * conj c = 2 := by
      dsimp [c, orthogonalCenter]
      simp only [map_div₀, map_mul, map_add, map_ofNat]
      have hs' : conj p + conj q ≠ 0 := by
        simpa only [map_add] using (map_ne_zero (starRingEnd ℂ)).mpr hs
      rw [← mul_div_assoc]
      apply (div_eq_iff hs').mpr
      have hstc := congrArg (starRingEnd ℂ) hst
      simp only [map_mul, map_add, Complex.conj_conj] at hstc
      linear_combination 2*hstc
    have hcircle : (z-c)*conj (z-c) - (c*conj c-1) = 0 := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq]
      exact_mod_cast hside
    unfold idealDiskSideReflection
    apply (div_eq_iff hd).mpr
    simp only [map_sub] at hcircle
    linear_combination (p+q)*hcircle + z*hsc + conj z*hc

end HolomorphicAnosov.IdealDiskTriangle

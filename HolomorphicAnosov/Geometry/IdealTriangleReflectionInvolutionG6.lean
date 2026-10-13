import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import Mathlib.Tactic
import Mathlib.Tactic
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle
open scoped ComplexConjugate

/-- The anti-Möbius denominator is nonzero at every interior disk point. (Lyubich, §2.4.4) -/
theorem idealDiskSideReflection_denominator_ne_zero_g6 {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖z‖ < 1) :
    2 - (p + q) * conj z ≠ 0 := by
  intro h
  have hEq : (2 : ℂ) = (p + q) * conj z := sub_eq_zero.mp h
  have heq : (2 : ℝ) = ‖(p + q) * conj z‖ := by
    have hnorm := congrArg norm hEq
    simpa using hnorm
  have hle : ‖(p + q) * conj z‖ ≤ 2 * ‖z‖ := by
    calc
      ‖(p + q) * conj z‖ ≤ ‖p + q‖ * ‖conj z‖ := norm_mul_le _ _
      _ ≤ (‖p‖ + ‖q‖) * ‖z‖ := by
        rw [Complex.norm_conj]
        gcongr
        exact norm_add_le _ _
      _ = 2 * ‖z‖ := by rw [hp, hq]; norm_num
  have hlt : (2 : ℝ) < 2 * ‖z‖ := by nlinarith [hz]
  linarith

/-- Conjugating a nonzero reflection denominator preserves nonzeroness. -/
theorem idealDiskSideReflection_conjugate_denominator_ne_zero_g6 {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hz : ‖z‖ < 1) :
    2 - (conj p + conj q) * z ≠ 0 := by
  intro h
  apply idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz
  have hc := congrArg conj h
  simpa [map_sub, map_add, map_mul, map_ofNat] using hc

theorem idealDiskSideReflection_involutive_disk_g6 {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    ∀ z ∈ disk,
      idealDiskSideReflection p q (idealDiskSideReflection p q z) = z := by
  intro z hz
  have hd : 2 - (p + q) * conj z ≠ 0 := idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz
  have hd' := idealDiskSideReflection_denominator_ne_zero_g6 hp hq
    (idealDiskSideReflection_mem_disk_g6 hp hq hpq hz)
  have hau : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  have hbu : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; norm_num
  unfold idealDiskSideReflection at hd' ⊢
  apply (div_eq_iff hd').mpr
  simp only [map_div₀, map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj]
  have hdc : 2 - (conj p + conj q) * z ≠ 0 := by
    simpa only [map_sub, map_mul, map_add, map_ofNat, Complex.conj_conj] using
      (map_ne_zero (starRingEnd ℂ)).mpr hd
  field_simp
  have hst := (ideal_reflection_coefficients_g6 hp hq).2
  have hstc := congrArg (starRingEnd ℂ) hst
  simp only [map_mul, map_add, Complex.conj_conj] at hstc hst
  linear_combination -2 * hst - 2 * z^2 * hstc +
    4 * z * (q * conj q) * hau + 4 * z * hbu


end HolomorphicAnosov.IdealDiskTriangle

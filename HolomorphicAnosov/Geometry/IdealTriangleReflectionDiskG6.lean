import HolomorphicAnosov.Geometry.IdealTriangleReflectionData
import Mathlib.Tactic

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

lemma ideal_reflection_coefficients_g6 {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    Complex.normSq (a * b) = 1 ∧ (a * b) * conj (a + b) = a + b := by
  have hau : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; norm_num
  have hbu : b * conj b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]; norm_num
  constructor
  · rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ha, hb]
    norm_num
  · rw [map_add]
    linear_combination b * hau + a * hbu

lemma ideal_reflection_norm_difference_g6 {s t : ℂ} (ht : Complex.normSq t = 1)
    (hst : t * conj s = s) (z : ℂ) :
    Complex.normSq (2 - s * conj z) - Complex.normSq (s - 2 * t * conj z) =
      (4 - Complex.normSq s) * (1 - Complex.normSq z) := by
  have hr := congrArg Complex.re hst
  have hi := congrArg Complex.im hst
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im] at *
  norm_num at *
  linear_combination 4 * z.re * hr + 4 * z.im * hi -
    4 * (z.re * z.re + z.im * z.im) * ht

lemma ideal_reflection_gap_pos_g6 {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ b) : 0 < 4 - Complex.normSq (a + b) := by
  have hp : 0 < Complex.normSq (a - b) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)
  have ha' : Complex.normSq a = 1 := by rw [Complex.normSq_eq_norm_sq, ha]; norm_num
  have hb' : Complex.normSq b = 1 := by rw [Complex.normSq_eq_norm_sq, hb]; norm_num
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at *
  nlinarith

/-- The explicit side reflection preserves the open disk. -/
theorem idealDiskSideReflection_mem_disk_g6 {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1) :
    ‖idealDiskSideReflection p q z‖ < 1 := by
  obtain ⟨ht, hst⟩ := ideal_reflection_coefficients_g6 hp hq
  have hg := ideal_reflection_gap_pos_g6 hp hq hpq
  have hz' : 0 < 1 - Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hd := ideal_reflection_norm_difference_g6 ht hst z
  have hlt : Complex.normSq ((p + q) - 2 * (p * q) * conj z) <
      Complex.normSq (2 - (p + q) * conj z) := by
    nlinarith [mul_pos hg hz']
  have hpos : 0 < Complex.normSq (2 - (p + q) * conj z) :=
    lt_of_le_of_lt (Complex.normSq_nonneg _) hlt
  have hr : Complex.normSq (idealDiskSideReflection p q z) < 1 := by
    unfold idealDiskSideReflection
    rw [Complex.normSq_div]
    apply (div_lt_one hpos).mpr
    simpa [mul_assoc] using hlt
  rw [Complex.normSq_eq_norm_sq] at hr
  nlinarith [norm_nonneg (idealDiskSideReflection p q z)]

end HolomorphicAnosov.IdealDiskTriangle

namespace HolomorphicAnosov.IdealDiskTriangle
/-- The disk reflection map is surjective. -/
theorem idealDiskSideReflection_disk_image_g6 {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    idealDiskSideReflection p q '' disk = disk := by
  have hden : ∀ {w : ℂ}, w ∈ disk → 2 - (p + q) * conj w ≠ 0 := by
    intro w hw he
    change ‖w‖ < 1 at hw
    have hEq : (2 : ℂ) = (p + q) * conj w := sub_eq_zero.mp he
    have heq : (2 : ℝ) = ‖(p + q) * conj w‖ := by
      have hnorm := congrArg norm hEq
      simpa using hnorm
    have hle : ‖(p + q) * conj w‖ ≤ 2 * ‖w‖ := by
      calc
        ‖(p + q) * conj w‖ ≤ ‖p + q‖ * ‖conj w‖ := norm_mul_le _ _
        _ ≤ (‖p‖ + ‖q‖) * ‖w‖ := by
          rw [Complex.norm_conj]
          gcongr
          exact norm_add_le _ _
        _ = 2 * ‖w‖ := by rw [hp, hq]; norm_num
    have hlt : (2 : ℝ) < 2 * ‖w‖ := by nlinarith [hw]
    linarith
  have hinv : ∀ z ∈ disk,
      idealDiskSideReflection p q (idealDiskSideReflection p q z) = z := by
    intro z hz
    have hd := hden hz
    have hd' := hden (idealDiskSideReflection_mem_disk_g6 hp hq hpq hz)
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
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact idealDiskSideReflection_mem_disk_g6 hp hq hpq hw
  · intro hz
    exact ⟨idealDiskSideReflection p q z,
      idealDiskSideReflection_mem_disk_g6 hp hq hpq hz,
      hinv z hz⟩

end HolomorphicAnosov.IdealDiskTriangle

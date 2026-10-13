import HolomorphicAnosov.Geometry.IdealTriangleReflectionData
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic

/-! Klein coordinates identify the open geodesic side of the disk. (Lyubich, §2.4.4) -/

namespace HolomorphicAnosov
open IdealDiskTriangle
open scoped ComplexConjugate

/-- The Klein image of an interior disk point lies in the open chord with distinct unit endpoints precisely when the signed geodesic equation vanishes. -/
theorem idealDiskKlein_mem_openSegment_iff_sideEquation {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1) :
    idealDiskKlein z ∈ openSegment ℝ p q ↔ sideEquation p q z = 0 := by
  have antipodal : ∀ {p q z : ℂ} (hp : ‖p‖ = 1) (hanti : p + q = 0)
      (hz : ‖z‖ < 1),
      idealDiskKlein z ∈ openSegment ℝ p q ↔ sideEquation p q z = 0 := by
    intro p q z hp hanti hz
    have hnorm : ‖idealDiskKlein z‖ < 1 := by
      have hs : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
      rw [idealDiskKlein, norm_div, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_lt_one hs]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hz)]
    have him :
        (idealDiskKlein z / p).im = 0 ↔ (z / p).im = 0 := by
      have he : idealDiskKlein z / p =
          ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * (z / p) := by
        unfold idealDiskKlein
        push_cast
        ring
      have hscale : (2 / (1 + ‖z‖ ^ 2) : ℝ) ≠ 0 := by positivity
      rw [he, Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        mul_eq_zero, hscale, false_or]
  
    have hchord : ∀ w : ℂ, ‖w‖ < 1 →
        (w ∈ openSegment ℝ p (-p) ↔ (w / p).im = 0) := by
      intro w hw
      have hp0 : p ≠ 0 := by intro h; simp [h] at hp
      constructor
      · rintro ⟨a, b, ha, hb, hab, rfl⟩
        have he : (a • p + b • -p) / p = ((a - b : ℝ) : ℂ) := by
          simp only [Complex.real_smul, Complex.ofReal_sub]
          field_simp
          ring
        rw [he]
        exact Complex.ofReal_im _
      · intro hi
        let t : ℝ := (w / p).re
        have hreal : w / p = (t : ℂ) := by
          apply Complex.ext <;> simp [t, hi]
        have ht : |t| < 1 := by
          have hn : ‖w / p‖ < 1 := by simpa [norm_div, hp] using hw
          simpa [hreal] using hn
        have htlo : -1 < t := (abs_lt.mp ht).1
        have hthi : t < 1 := (abs_lt.mp ht).2
        refine ⟨(1 + t) / 2, (1 - t) / 2, by linarith, by linarith, by ring, ?_⟩
        have hwp : w = (t : ℂ) * p := (div_eq_iff hp0).mp hreal
        rw [hwp]
        simp only [Complex.real_smul]
        push_cast
        ring
    have hq : q = -p := eq_neg_of_add_eq_zero_right hanti
    rw [hq, hchord (idealDiskKlein z) hnorm, him]
    simp only [sideEquation, add_neg_cancel, ite_true]
  have circle_to_chord_line : ∀ (c z : ℂ),
      ‖z - c‖ ^ 2 - (‖c‖ ^ 2 - 1) = 0 ↔ (conj c * idealDiskKlein z).re = 1 := by
    intro c z
    have hs : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have he : conj c * idealDiskKlein z =
        ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * (conj c * z) := by
      unfold idealDiskKlein
      push_cast
      ring
    rw [he, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← Complex.normSq_eq_norm_sq (z - c), Complex.normSq_sub,
      Complex.normSq_eq_norm_sq z, Complex.normSq_eq_norm_sq c]
    rw [mul_comm z (conj c), div_mul_eq_mul_div, div_eq_one_iff_eq hs.ne']
    constructor <;> intro h <;> linarith
  have endpoint_line : ∀ {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hanti : p + q ≠ 0),
      (conj (orthogonalCenter p q) * p).re = 1 := by
    intro p q hp hq hanti
    have hp0 : p ≠ 0 := by intro h; simp [h] at hp
    have hq0 : q ≠ 0 := by intro h; simp [h] at hq
    have hc : conj (orthogonalCenter p q) = 2 / (p + q) := by
      simp only [orthogonalCenter, map_div₀, map_mul, map_ofNat, map_add,
        ← Complex.inv_eq_conj hp, ← Complex.inv_eq_conj hq]
      field_simp
      rw [add_comm q p, div_self hanti]
    have hs : conj (orthogonalCenter p q) * p + conj (conj (orthogonalCenter p q) * p) = 2 := by
      rw [map_mul, Complex.conj_conj, hc, ← Complex.inv_eq_conj hp]
      unfold orthogonalCenter
      field_simp
    rw [Complex.add_conj] at hs
    have hr := congrArg Complex.re hs
    norm_num at hr
    simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add] using hr
  have chord_line : ∀ {p q c w : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
      (hpq : p ≠ q) (hw : ‖w‖ < 1)
      (hcp : (conj c * p).re = 1) (hcq : (conj c * q).re = 1),
      w ∈ openSegment ℝ p q ↔ (conj c * w).re = 1 := by
    intro p q c w hp hq hpq hw hcp hcq
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      simp only [Complex.real_smul, mul_add, ← mul_assoc]
      have hcp' : c.re * p.re + c.im * p.im = 1 := by simpa using hcp
      have hcq' : c.re * q.re + c.im * q.im = 1 := by simpa using hcq
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith
    · intro hcw
      have hcp' : c.re * p.re + c.im * p.im = 1 := by simpa using hcp
      have hd : c.re * (q - p).re + c.im * (q - p).im = 0 := by
        simp only [Complex.sub_re, Complex.sub_im]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
          sub_neg_eq_add] at hcq hcp
        linarith
      have hu : c.re * (w - p).re + c.im * (w - p).im = 0 := by
        simp only [Complex.sub_re, Complex.sub_im]
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
          sub_neg_eq_add] at hcw hcp
        linarith
      have hcross : (w - p).im * (q - p).re - (w - p).re * (q - p).im = 0 := by
        by_cases hc : c.re = 0
        · have hci : c.im ≠ 0 := by intro h; simp [hc, h] at hcp'
          apply (mul_eq_zero.mp (show c.im *
            ((w - p).im * (q - p).re - (w - p).re * (q - p).im) = 0 by
              linear_combination (q - p).re * hu - (w - p).re * hd)).resolve_left hci
        · apply (mul_eq_zero.mp (show c.re *
            ((w - p).im * (q - p).re - (w - p).re * (q - p).im) = 0 by
              linear_combination (w - p).im * hd - (q - p).im * hu)).resolve_left hc
      have him : ((w - p) / (q - p)).im = 0 := by
        rw [Complex.div_im, ← sub_div, hcross, zero_div]
      let t : ℝ := ((w - p) / (q - p)).re
      have he : w - p = (t : ℂ) * (q - p) := by
        apply (div_eq_iff (sub_ne_zero.mpr hpq.symm)).mp
        apply Complex.ext <;> simp [t, him]
      have hwline : w = t • (q - p) +ᵥ p := by
        simpa only [Complex.real_smul, vadd_eq_add] using (sub_eq_iff_eq_add.mp he)
      have hcol : Collinear ℝ ({p, w, q} : Set ℂ) := by
        rw [collinear_iff_of_mem (by simp : p ∈ ({p, w, q} : Set ℂ))]
        refine ⟨q - p, ?_⟩
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨t, hwline⟩
        · exact ⟨1, by simp⟩
      have hbetween := hcol.sbtw_of_dist_eq_of_dist_lt
        (p := (0 : ℂ)) (r := 1) (by simpa using hp) (by simpa using hw)
        (by simpa using hq) hpq
      rw [openSegment_eq_image_lineMap]
      exact hbetween.mem_image_Ioo
  by_cases hanti : p + q = 0
  · exact antipodal hp hanti hz
  · have hnorm : ‖idealDiskKlein z‖ < 1 := by
      have hs : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
      rw [idealDiskKlein, norm_div, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_lt_one hs]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hz)]
    have hcp := endpoint_line hp hq hanti
    have hcq : (conj (orthogonalCenter p q) * q).re = 1 := by
      have h := endpoint_line hq hp (by simpa [add_comm] using hanti)
      simpa only [orthogonalCenter, add_comm q p, mul_comm q p, mul_assoc] using h
    rw [chord_line hp hq hpq hnorm hcp hcq, sideEquation, ite_eq_right (by exact hanti)]
    exact (circle_to_chord_line (orthogonalCenter p q) z).symm

end HolomorphicAnosov

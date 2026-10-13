import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterConjugateG6
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexSpace

open scoped ComplexConjugate
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- Every point w of the unit disk has an inverse Klein point z=t w with t>0 and 1+‖z‖²=2t. -/
lemma inverse_klein_point {w : ℂ} (hw : ‖w‖ < 1) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ ∃ t : ℝ, 0 < t ∧ z = (t : ℂ) * w ∧ ‖z‖ ^ 2 + 1 = 2 * t := by
  let a : ℝ := Real.sqrt (1 - ‖w‖ ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by nlinarith [norm_nonneg w])
  have ha2 : a ^ 2 = 1 - ‖w‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg w])
  let t : ℝ := (1 + a)⁻¹
  have ht : 0 < t := inv_pos.mpr (by linarith)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply inv_le_one_of_one_le₀
    linarith
  let z : ℂ := (t : ℂ) * w
  have hz : ‖z‖ = t * ‖w‖ := by simp [z, abs_of_pos ht]
  refine ⟨z, ?_, t, ht, rfl, ?_⟩
  · rw [hz]
    calc t * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) ht1
         _ < 1 := hw
  · rw [hz]
    dsimp [t]
    field_simp
    nlinarith [ha2]

/-- The average of three unit vectors, two of them distinct, is strictly inside the complex unit disk. -/
lemma triple_average_norm_lt {p q r : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hr : ‖r‖ = 1) (hpq : p ≠ q) : ‖(p + q + r) / 3‖ < 1 := by
  have hm := (norm_midpoint_lt_iff (hp.trans hq.symm)).mpr hpq
  rw [norm_smul, Real.norm_eq_abs] at hm
  norm_num at hm
  have hs := norm_add_le (p + q) r
  rw [norm_div]
  norm_num
  rw [hp] at hm
  nlinarith [hs]

/-- The inverse Klein image of a triple average satisfies each original side equation by the same positive scaling. -/
lemma sideEquation_radial_average {p q r w z : ℂ} {t : ℝ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hw : p + q + r = 3 * w) (hz : z = (t : ℂ) * w)
    (ht : ‖z‖ ^ 2 + 1 = 2 * t) :
    sideEquation p q z = t / 3 * sideEquation p q r := by
  by_cases hs : p + q = 0
  · have hw' : w = r / 3 := by
      rw [hs, zero_add] at hw
      linear_combination -hw / 3
    simp only [sideEquation, ite_eq_left hs]
    rw [hz, hw']
    have he : (t : ℂ) * (r / 3) / p = (t / 3 : ℝ) * (r / p) := by
      push_cast
      ring
    rw [he]
    simp
  · let c := orthogonalCenter p q
    have hc := idealTriangle_center_conjugate_g6 hp hq hs
    have hm : (p + q + r) * conj c = 3 * w * conj c := congrArg (· * conj c) hw
    have hmc : 2 + r * conj c = 3 * (w * conj c) := by
      calc 2 + r * conj c = (p + q) * conj c + r * conj c := by rw [hc]
           _ = 3 * (w * conj c) := by linear_combination hm
    have hre := congrArg Complex.re hmc
    have hzre : (z * conj c).re = t * (w * conj c).re := by
      rw [hz, mul_assoc]
      simp
    norm_num [Complex.add_re, Complex.mul_re] at hre hzre
    simp only [sideEquation, ite_eq_right hs, Complex.sq_norm, Complex.normSq_sub]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq r, hr]
    dsimp [c] at hzre hre
    norm_num [Complex.mul_re] at *
    nlinarith



/-- An explicit interior-disk point has each triangle side value proportional to that of the opposite ideal vertex, with a common positive factor. (Epstein–Petronio, Def. 2.1) -/
theorem ideal_triangle_klein_barycenter_g6 (A : VertexTriple) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ ∃ t : ℝ, 0 < t ∧
      ∀ p ∈ A.val, ∀ q ∈ A.val, ∀ r ∈ A.val,
        p ≠ q → q ≠ r → r ≠ p →
        sideEquation p q z = t / 3 * sideEquation p q r := by
  classical
  let w : ℂ := (∑ p ∈ A.val, p) / 3
  have sum_eq (p q r : ℂ) (hp : p ∈ A.val) (hq : q ∈ A.val) (hr : r ∈ A.val)
      (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) : p + q + r = 3 * w := by
    have he : ({p,q,r} : Finset ℂ) = A.val := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [A.property.1]
        simp [hpq, hqr, hrp.symm]
    dsimp [w]
    rw [← he]
    simp [hpq, hqr, hrp.symm]
    ring
  have hw : ‖w‖ < 1 := by
    obtain ⟨p,q,r,hpq,hpr,hqr,hA⟩ := Finset.card_eq_three.mp A.property.1
    have hp : p ∈ A.val := by rw [hA]; simp
    have hq : q ∈ A.val := by rw [hA]; simp
    have hr : r ∈ A.val := by rw [hA]; simp
    have he := sum_eq p q r hp hq hr hpq hqr hpr.symm
    have hw' : w = (p+q+r)/3 := by linear_combination -he / 3
    rw [hw']
    exact triple_average_norm_lt (A.property.2 p hp) (A.property.2 q hq)
      (A.property.2 r hr) hpq
  obtain ⟨z, hz, t, ht, hzw, hzt⟩ := inverse_klein_point hw
  refine ⟨z, hz, t, ht, ?_⟩
  intro p hp q hq r hr hpq hqr hrp
  exact sideEquation_radial_average (A.property.2 p hp) (A.property.2 q hq)
    (A.property.2 r hr) (sum_eq p q r hp hq hr hpq hqr hrp) hzw hzt

end HolomorphicAnosov.IdealDiskTriangle

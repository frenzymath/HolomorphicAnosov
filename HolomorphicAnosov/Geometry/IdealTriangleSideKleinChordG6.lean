import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-! Klein coordinates identify ideal geodesic sides with Euclidean chords. -/

open scoped ComplexConjugate
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- A side point has Klein coordinates satisfying the real chord equation (Epstein–Petronio pp.116–117).-/
lemma side_klein_relation {p q z : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : p ≠ q) (hz : z ∈ openSide p q) :
    ∃ t : ℝ, 0 < t ∧ ∃ w : ℂ, ‖w‖ < 1 ∧ z = (t : ℂ) * w ∧
      ‖z‖ ^ 2 + 1 = 2 * t ∧ w + p*q*conj w = p+q := by
  let t : ℝ := (‖z‖ ^ 2 + 1) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  let w : ℂ := z / (t : ℂ)
  have htn : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hzw : z = (t : ℂ) * w := by dsimp [w]; field_simp
  have hw : ‖w‖ < 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    apply (div_lt_one ht).mpr
    have hzd : ‖z‖ < 1 := hz.1
    dsimp [t]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hzd)]
  have hfix := idealDiskSideReflection_fixed_openSide hp hq hpq hz
  have hd := idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz.1
  unfold idealDiskSideReflection at hfix
  have he := (div_eq_iff hd).mp hfix
  have hnorm : z * conj z = (‖z‖ ^ 2 : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have htval : ((‖z‖ ^ 2 + 1 : ℝ) : ℂ) = 2*(t : ℂ) := by
    dsimp [t]; push_cast; ring
  refine ⟨t, ht, w, hw, hzw, by dsimp [t]; ring, ?_⟩
  have hwrel : z + p*q*conj z = (t : ℂ)*(p+q) := by
    push_cast at htval hnorm
    linear_combination -he/2 + (p+q)*hnorm/2 + (p+q)*htval/2
  rw [hzw, map_mul, Complex.conj_ofReal] at hwrel
  apply mul_left_cancel₀ htn
  linear_combination hwrel

/-- The Klein chord equation and the unit-disk bound give a convex combination of its distinct unit endpoints (elementary coordinate form of the geodesic half-space description in Epstein–Petronio pp.116–117).-/
lemma klein_relation_chord {p q w : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : p ≠ q) (hw : ‖w‖ < 1) (he : w+p*q*conj w=p+q) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ w = (1-s) • p + s • q := by
  have hpunit : p*conj p = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  have hqunit : q*conj q = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; norm_num
  have hqp : q-p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hqpc : conj q-conj p ≠ 0 := by
    simpa only [map_sub] using (map_ne_zero (starRingEnd ℂ)).mpr hqp
  let v := (w-p)/(q-p)
  have hvreal : conj v = v := by
    dsimp [v]
    simp only [map_div₀, map_sub]
    apply (div_eq_div_iff hqpc hqp).mpr
    have hpne : p ≠ 0 := by intro h; simp [h] at hp
    have hqne : q ≠ 0 := by intro h; simp [h] at hq
    apply mul_left_cancel₀ (mul_ne_zero hpne hqne)
    linear_combination (q-p)*he + (w-q)*q*hpunit - (w-p)*p*hqunit
  have hvim : v.im = 0 := Complex.conj_eq_iff_im.mp hvreal
  have hv : (v.re : ℂ) = v := by apply Complex.ext <;> simp [hvim]
  let s : ℝ := v.re
  have hws : w = (1-s) • p + s • q := by
    have hh : (s : ℂ)*(q-p)=w-p := by rw [show (s:ℂ)=v from hv]; exact div_mul_cancel₀ _ hqp
    simp only [Complex.real_smul]
    push_cast
    linear_combination -hh
  have hp2 : p.re^2+p.im^2=1 := by
    have h : Complex.normSq p = 1 := by rw [Complex.normSq_eq_norm_sq, hp]; norm_num
    simp only [Complex.normSq_apply] at h
    nlinarith
  have hq2 : q.re^2+q.im^2=1 := by
    have h : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq, hq]; norm_num
    simp only [Complex.normSq_apply] at h
    nlinarith
  have hw2 : w.re^2+w.im^2 < 1 := by
    have h : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg w]
    simp only [Complex.normSq_apply] at h
    nlinarith
  have hdiff : 0 < (q.re-p.re)^2+(q.im-p.im)^2 := by
    have hn : 0 < Complex.normSq (q-p) := Complex.normSq_pos.mpr hqp
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hn
    nlinarith
  have hpoly : w.re^2+w.im^2 = 1-s*(1-s)*((q.re-p.re)^2+(q.im-p.im)^2) := by
    rw [hws]
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    linear_combination (1-s)*hp2 + s*hq2
  have hsprod : 0 < s*(1-s) := by nlinarith
  refine ⟨s, ?_, ?_, hws⟩ <;> nlinarith

/-- Every point of the original open geodesic is a positive radial multiple of a convex combination of its two ideal endpoints, with the Klein radial identity (Epstein–Petronio pp.116–117).-/
theorem openSide_radial_chord {p q z : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : p ≠ q) (hz : z ∈ openSide p q) :
    ∃ t : ℝ, 0 < t ∧ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      z = (t : ℂ) * ((1-s) • p + s • q) ∧ ‖z‖^2+1=2*t := by
  obtain ⟨t, ht, w, hw, hzw, hrad, hrel⟩ := side_klein_relation hp hq hpq hz
  obtain ⟨s, hs, hs1, hws⟩ := klein_relation_chord hp hq hpq hw hrel
  exact ⟨t, ht, s, hs, hs1, hzw.trans (congrArg ((t : ℂ)*·) hws), hrad⟩

end HolomorphicAnosov.IdealDiskTriangle

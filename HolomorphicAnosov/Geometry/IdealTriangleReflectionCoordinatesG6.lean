import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterConjugateG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6
import HolomorphicAnosov.Geometry.IdealDiskSideReflectionEndpoints
import Mathlib.Tactic

/-! This file develops explicit reflection coordinates on the closed disk and the corresponding polynomial side kernel. -/
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

lemma reflection_denominator_closed {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ ≤ 1) :
    2 - (p+q)*conj z ≠ 0 := by
  have hgap := ideal_reflection_gap_pos_g6 hp hq hpq
  rw [Complex.normSq_eq_norm_sq] at hgap
  have hs : ‖p+q‖ < 2 := by nlinarith [norm_nonneg (p+q)]
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_mul, Complex.norm_conj] at hn
  norm_num at hn
  nlinarith [mul_le_mul_of_nonneg_left hz (norm_nonneg (p+q))]

lemma reflection_unit {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ = 1) :
    ‖idealDiskSideReflection p q z‖ = 1 := by
  obtain ⟨ht,hst⟩ := ideal_reflection_coefficients_g6 hp hq
  have hd := ideal_reflection_norm_difference_g6 ht hst z
  have hzsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq,hz]; norm_num
  rw [hzsq] at hd
  have heq : Complex.normSq ((p+q)-2*(p*q)*conj z) =
      Complex.normSq (2-(p+q)*conj z) := by linarith
  have hrefl : Complex.normSq (idealDiskSideReflection p q z) = 1 := by
    unfold idealDiskSideReflection
    rw [Complex.normSq_div]
    have hdpos := Complex.normSq_pos.mpr (reflection_denominator_closed hp hq hpq hz.le)
    rw [show p+q-2*p*q*conj z = (p+q)-2*(p*q)*conj z by ring,heq,div_self hdpos.ne']
  rw [Complex.normSq_eq_norm_sq] at hrefl
  nlinarith [norm_nonneg (idealDiskSideReflection p q z)]

lemma reflection_inj_closed {p q x y : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxy : idealDiskSideReflection p q x = idealDiskSideReflection p q y) : x = y := by
  have hd₁ := reflection_denominator_closed hp hq hpq hx
  have hd₂ := reflection_denominator_closed hp hq hpq hy
  unfold idealDiskSideReflection at hxy
  have heq := (div_eq_div_iff hd₁ hd₂).mp hxy
  have hprod : (p-q)^2 * (conj x-conj y) = 0 := by linear_combination heq
  have hc : conj x = conj y := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hpq)))
  simpa only [Complex.conj_conj] using congrArg conj hc

def sideKernel (a b z : ℂ) : ℂ := (a+b)*(1+z*conj z)-2*z-2*a*b*conj z

def sideCoefficient (a b : ℂ) : ℂ := if a+b=0 then -4*Complex.I*a else a+b

lemma sideCoefficient_ne_zero {a b : ℂ} (ha : ‖a‖ = 1) : sideCoefficient a b ≠ 0 := by
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  unfold sideCoefficient
  split_ifs with h
  · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) han
  · exact h

lemma sideKernel_eq_coefficient {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : ℂ) :
    sideKernel a b z = sideCoefficient a b * (sideEquation a b z : ℂ) := by
  by_cases hs : a+b=0
  · have hb' : b = -a := by linear_combination hs
    have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
    have hau : a*conj a=1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,ha]; norm_num
    have hac : conj a = 1/a := by apply (eq_div_iff han).mpr; simpa [mul_comm] using hau
    have hgeneric (w : ℂ) : 2*Complex.I*(w.im : ℂ) = w-conj w := by
      apply Complex.ext <;> simp; ring
    have hi := hgeneric (z/a)
    simp only [sideKernel,sideCoefficient,sideEquation,hs,ite_true,zero_mul,zero_sub]
    rw [hb']
    calc
      -(2*z)-2*a*(-a)*conj z = -2*a*(z/a-conj (z/a)) := by
        simp only [map_div₀,hac]
        field_simp
        ring
      _ = -4*Complex.I*a*((z/a).im : ℂ) := by rw [←hi]; ring
  · let c := orthogonalCenter a b
    have hc : c*(a+b) = 2*a*b := by dsimp [c, orthogonalCenter]; field_simp
    have hsc := idealTriangle_center_conjugate_g6 ha hb hs
    have he : (sideEquation a b z : ℂ) =
        (z-c)*conj (z-c)-(c*conj c-1) := by
      simp only [sideEquation, ite_eq_right hs, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have hscaled : (a+b)*(sideEquation a b z : ℂ) =
        (a+b)*(1+z*conj z)-2*z-2*a*b*conj z := by
      rw [he]
      simp only [map_sub]
      linear_combination -z*hsc - conj z*hc
    simpa only [sideKernel,sideCoefficient,ite_eq_right hs] using hscaled.symm

def reflectionKernelFactor (p q a b : ℂ) : ℂ :=
  -((p+q)^2-4*p*q)^2 / (p*q*(2-(p+q)*conj a)*(2-(p+q)*conj b))

lemma reflectionKernelFactor_ne_zero {p q a b : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpq : p ≠ q) : reflectionKernelFactor p q a b ≠ 0 := by
  unfold reflectionKernelFactor
  apply div_ne_zero
  · apply neg_ne_zero.mpr
    apply pow_ne_zero
    rw [show (p+q)^2-4*p*q = (p-q)^2 by ring]
    exact pow_ne_zero 2 (sub_ne_zero.mpr hpq)
  · exact mul_ne_zero (mul_ne_zero
      (mul_ne_zero (norm_ne_zero_iff.mp (by rw [hp]; norm_num))
        (norm_ne_zero_iff.mp (by rw [hq]; norm_num)))
      (reflection_denominator_closed hp hq hpq ha.le))
      (reflection_denominator_closed hp hq hpq hb.le)

set_option maxRecDepth 4096 in
lemma sideKernel_reflection {p q a b z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpq : p ≠ q) (hz : ‖z‖ ≤ 1) :
    sideKernel (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
      (idealDiskSideReflection p q z) * (Complex.normSq (2-(p+q)*conj z) : ℂ) =
      reflectionKernelFactor p q a b * conj (sideKernel a b z) := by
  have hunit {x : ℂ} (hx : ‖x‖=1) : conj x=1/x := by
    apply (eq_div_iff (norm_ne_zero_iff.mp (by rw [hx]; norm_num))).mpr
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hx]
    norm_num
  have hpn : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  have hqn : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hbn : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hdpa := reflection_denominator_closed hp hq hpq ha.le
  have hdpb := reflection_denominator_closed hp hq hpq hb.le
  have hdpz := reflection_denominator_closed hp hq hpq hz
  have hdpc := (map_ne_zero (starRingEnd ℂ)).mpr hdpz
  simp only [map_sub,map_add,map_mul,map_ofNat,Complex.conj_conj,hunit hp,hunit hq,hunit ha,hunit hb]
    at hdpa hdpb hdpc
  field_simp [hpn,hqn,han,hbn] at hdpa hdpb hdpc
  have hdpa' := (div_ne_zero_iff.mp hdpa).1
  have hdpb' := (div_ne_zero_iff.mp hdpb).1
  have hdpc' := (div_ne_zero_iff.mp hdpc).1
  have hdpc'' : p*q*2-(q+p)*z ≠ 0 := by
    intro h
    apply hdpc'
    linear_combination h
  rw [← Complex.mul_conj]
  unfold sideKernel reflectionKernelFactor idealDiskSideReflection
  simp only [map_div₀,map_sub,map_add,map_mul,map_ofNat,map_one,Complex.conj_conj,
    hunit hp,hunit hq,hunit ha,hunit hb]
  field_simp (disch := solve | assumption | norm_num | (intro h; solve
    | (apply hdpa'; linear_combination h)
    | (apply hdpb'; linear_combination h)
    | (apply hdpc'; linear_combination h)))
  ring

lemma sideKernel_product_real {a b z r : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (sideKernel a b z * conj (sideKernel a b r)).re =
      Complex.normSq (sideCoefficient a b) *
        (sideEquation a b z * sideEquation a b r) := by
  rw [sideKernel_eq_coefficient ha hb,sideKernel_eq_coefficient ha hb]
  have he : (sideCoefficient a b * (sideEquation a b z : ℂ)) *
      conj (sideCoefficient a b * (sideEquation a b r : ℂ)) =
      (Complex.normSq (sideCoefficient a b) : ℂ) *
        ((sideEquation a b z * sideEquation a b r : ℝ) : ℂ) := by
    rw [← Complex.mul_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  rw [he]
  simp

/-- Reflection transports the signed product for any pair of distinct unit endpoints, including diameter sides. -/
lemma reflection_side_product_transport {p q a b z r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hpq : p ≠ q) (hz : ‖z‖ ≤ 1) (hr : ‖r‖ = 1) :
    (0 ≤ sideEquation (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
      (idealDiskSideReflection p q z) *
        sideEquation (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
          (idealDiskSideReflection p q r)) ↔
      0 ≤ sideEquation a b z * sideEquation a b r := by
  let Kz := sideKernel (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
      (idealDiskSideReflection p q z)
  let Kr := sideKernel (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)
      (idealDiskSideReflection p q r)
  let L := reflectionKernelFactor p q a b
  let dZ := Complex.normSq (2-(p+q)*conj z)
  let dR := Complex.normSq (2-(p+q)*conj r)
  have hzid := sideKernel_reflection hp hq ha hb hpq hz
  have hrid := sideKernel_reflection hp hq ha hb hpq hr.le
  have hdZ : 0 < dZ := Complex.normSq_pos.mpr (reflection_denominator_closed hp hq hpq hz)
  have hdR : 0 < dR := Complex.normSq_pos.mpr (reflection_denominator_closed hp hq hpq hr.le)
  have hL : 0 < Complex.normSq L := Complex.normSq_pos.mpr
    (reflectionKernelFactor_ne_zero hp hq ha hb hpq)
  have hc : 0 < Complex.normSq (sideCoefficient a b) :=
    Complex.normSq_pos.mpr (sideCoefficient_ne_zero (b := b) ha)
  have hc' : 0 < Complex.normSq (sideCoefficient
      (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)) :=
    Complex.normSq_pos.mpr (sideCoefficient_ne_zero
      (b := idealDiskSideReflection p q b) (reflection_unit hp hq hpq ha))
  have he0 := congrArg Complex.re (congrArg₂ (fun x y : ℂ ↦ x*conj y) hzid hrid)
  have he : (Kz * conj Kr).re * dZ*dR = (Complex.normSq L) *
      (sideKernel a b z * conj (sideKernel a b r)).re := by
    dsimp [Kz,Kr,L,dZ,dR] at *
    have hleft : (Kz * (dZ : ℂ)) * conj (Kr * (dR : ℂ)) =
        (Kz*conj Kr) * ((dZ*dR : ℝ) : ℂ) := by
      simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
      ring
    have hright : (L * conj (sideKernel a b z)) *
        conj (L * conj (sideKernel a b r)) =
        (Complex.normSq L : ℂ) * conj (sideKernel a b z * conj (sideKernel a b r)) := by
      simp only [map_mul,Complex.conj_conj]
      rw [← Complex.mul_conj]
      ring
    change (Kz * (dZ : ℂ) * conj (Kr * (dR : ℂ))).re =
      (L * conj (sideKernel a b z) * conj (L * conj (sideKernel a b r))).re at he0
    rw [hleft,hright] at he0
    simp only [map_mul,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero,Complex.mul_re,Complex.conj_re,Complex.conj_conj] at he0
    have he' : (Kz * conj Kr).re * dZ*dR = (Complex.normSq L) *
        (sideKernel a b z * conj (sideKernel a b r)).re := by
      convert he0 using 1 <;> simp [Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring
    exact he' 
  rw [sideKernel_product_real (reflection_unit hp hq hpq ha)
      (reflection_unit hp hq hpq hb), sideKernel_product_real ha hb] at he
  have hpos : 0 < Complex.normSq (sideCoefficient
      (idealDiskSideReflection p q a) (idealDiskSideReflection p q b)) * dZ*dR := by positivity
  have hpos' : 0 < Complex.normSq L * Complex.normSq (sideCoefficient a b) := by positivity
  constructor
  · intro h
    have hh : 0 ≤ (Kz * conj Kr).re := by
      rw [sideKernel_product_real (reflection_unit hp hq hpq ha)
        (reflection_unit hp hq hpq hb)]
      exact mul_nonneg (Complex.normSq_nonneg _) h
    nlinarith [he]
  · intro h
    have hh : 0 ≤ (sideKernel a b z * conj (sideKernel a b r)).re := by
      rw [sideKernel_product_real ha hb]
      exact mul_nonneg (Complex.normSq_nonneg _) h
    nlinarith [he]

end HolomorphicAnosov.IdealDiskTriangle

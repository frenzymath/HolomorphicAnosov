import HolomorphicAnosov.Geometry.IdealTriangleBoundary
import HolomorphicAnosov.Geometry.IdealTriangleSideKleinChordG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterConjugateG6

/-! This file proves that points on the original ideal-triangle sides belong to its carrier. (Epstein–Petronio, Def. 2.1) -/

open scoped ComplexConjugate
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- A side equation vanishes at both unit-circle endpoints. (Epstein–Petronio, Def. 2.1) -/
lemma sideEquation_endpoints {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    sideEquation p q p = 0 ∧ sideEquation p q q = 0 := by
  by_cases hs : p+q=0
  · have hpne : p ≠ 0 := by intro h; simp [h] at hp
    have hq' : q = -p := by linear_combination hs
    simp [sideEquation, hq', hpne]
  · let c := orthogonalCenter p q
    have hc := idealTriangle_center_conjugate_g6 hp hq hs
    have hpunit : p*conj p=1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
    have hcc : c*(p+q)=2*p*q := by dsimp [c, orthogonalCenter]; field_simp
    have hsum : p*conj c+conj p*c=2 := by
      apply mul_right_cancel₀ hs
      linear_combination p*hc + conj p*hcc + 2*q*hpunit
    have hpRe : (p*conj c).re=1 := by
      have h := congrArg Complex.re hsum
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        ] at h ⊢
      norm_num at h
      nlinarith
    have hqRe : (q*conj c).re=1 := by
      have h := congrArg Complex.re hc
      rw [add_mul, Complex.add_re] at h
      change (p*conj c).re + (q*conj c).re = 2 at h
      linarith
    simp only [sideEquation, ite_eq_right hs, Complex.sq_norm, Complex.normSq_sub]
    rw [Complex.normSq_eq_norm_sq p, Complex.normSq_eq_norm_sq q, hp, hq]
    change (1^2 + Complex.normSq c - 2*(p*conj c).re -
      (Complex.normSq c-1) = 0) ∧
      (1^2 + Complex.normSq c - 2*(q*conj c).re - (Complex.normSq c-1) = 0)
    rw [hpRe, hqRe]
    constructor <;> ring

/-- Radial Klein coordinates turn each side equation into affine interpolation of its endpoint values, up to a common radial factor. (Epstein–Petronio, Def. 2.1) -/
lemma sideEquation_radial_chord (u v : ℂ) {p q z : ℂ} {s t : ℝ}
    (hp : ‖p‖=1) (hq : ‖q‖=1)
    (hz : z = (t:ℂ)*((1-s) • p+s • q)) (ht : ‖z‖^2+1=2*t) :
    sideEquation u v z = t*((1-s)*sideEquation u v p+s*sideEquation u v q) := by
  by_cases huv : u+v=0
  · simp only [sideEquation, ite_eq_left huv]
    rw [hz]
    simp only [Complex.real_smul]
    have he : (t:ℂ)*(((1-s:ℝ):ℂ)*p+(s:ℂ)*q)/u =
      (t:ℂ)*(((1-s:ℝ):ℂ)*(p/u)+(s:ℂ)*(q/u)) := by ring
    rw [he]
    simp
  · simp only [sideEquation, ite_eq_right huv, Complex.sq_norm, Complex.normSq_sub]
    rw [Complex.normSq_eq_norm_sq z, Complex.normSq_eq_norm_sq p,
      Complex.normSq_eq_norm_sq q, hp, hq]
    have hre : (z*conj (orthogonalCenter u v)).re =
        t*((1-s)*(p*conj (orthogonalCenter u v)).re +
          s*(q*conj (orthogonalCenter u v)).re) := by
      rw [hz]
      simp only [Complex.real_smul, add_mul, mul_assoc, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre]
    nlinarith

/-- Every point on a side of an original three-vertex ideal triangle belongs to its closed half-space carrier. (Epstein–Petronio, Def. 2.1) -/
theorem openSide_mem_triangle_of_vertexTriple (A : VertexTriple)
    {p q z : ℂ} (hp : p ∈ A.val) (hq : q ∈ A.val) (hpq : p ≠ q)
    (hz : z ∈ openSide p q) : z ∈ triangle A.val := by
  classical
  obtain ⟨t, ht, s, hs, hs1, hzw, hrad⟩ :=
    openSide_radial_chord (A.property.2 p hp) (A.property.2 q hq) hpq hz
  refine ⟨hz.1, ?_⟩
  intro u hu v hv r hr huv hvr hru
  have he : A.val = {u,v,r} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [A.property.1]
      simp [huv, hvr, hru.symm]
  have hends := sideEquation_endpoints (A.property.2 u hu) (A.property.2 v hv)
  have hnon (x : ℂ) (hx : x ∈ A.val) : 0 ≤ sideEquation u v x * sideEquation u v r := by
    rw [he] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simp [hends.1]
    · simp [hends.2]
    · exact mul_self_nonneg _
  rw [sideEquation_radial_chord u v (A.property.2 p hp) (A.property.2 q hq)
    hzw hrad]
  have ha := mul_nonneg (sub_nonneg.mpr hs1) (hnon p hp)
  have hb := mul_nonneg hs (hnon q hq)
  have hh := mul_nonneg ht.le (add_nonneg ha hb)
  nlinarith

end HolomorphicAnosov.IdealDiskTriangle

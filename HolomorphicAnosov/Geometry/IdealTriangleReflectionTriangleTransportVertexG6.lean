import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionHalfspaceSignG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCoordinatesG6

/-! This file proves transport of the finite carrier of an actual ideal triangle under a side reflection. (Lyubich, §2.4.13) -/

noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

private lemma triangle_third_vertex_local (A : VertexTriple) {p q : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hpq : p ≠ q) :
    ∃ r ∈ A.val, q ≠ r ∧ r ≠ p ∧ A.val = {p,q,r} := by
  classical
  obtain ⟨r,hr,hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {p,q}) (t := A.val) (by rw [Finset.card_pair hpq,A.property.1]; norm_num)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hrpq
  refine ⟨r,hr,Ne.symm hrpq.2,hrpq.1,?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hp ⟨hq,hr⟩
  · rw [A.property.1]
    simp [hpq,Ne.symm hrpq.1,Ne.symm hrpq.2]

private lemma reflection_involutive_unit_local {p q z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ = 1) :
    idealDiskSideReflection p q (idealDiskSideReflection p q z) = z := by
  have hd : 2 - (p + q) * conj z ≠ 0 := reflection_denominator_closed hp hq hpq hz.le
  have hzR := reflection_unit hp hq hpq hz
  have hd' := reflection_denominator_closed hp hq hpq hzR.le
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

/-- The explicit side reflection transports the finite half-space carrier of an actual ideal triangle in both directions. (Lyubich, §2.4.4) (Epstein–Petronio, Def. 2.1) -/
theorem idealDiskSideReflection_triangle_transport_vertex_g6 (V : VertexTriple)
    {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q)
    (hpV : p ∈ V.val) (hqV : q ∈ V.val) :
    ∀ z, (z ∈ triangle V.val → idealDiskSideReflection p q z ∈
      triangle (reflectedVertices V.val p q)) ∧
      (z ∈ triangle (reflectedVertices V.val p q) → idealDiskSideReflection p q z ∈ triangle V.val) := by
  intro z
  have hpu : p ∈ V.val := hpV
  have hqu : q ∈ V.val := hqV
  have sideEquation_swap_product_local : ∀ (p q z r : ℂ),
      sideEquation p q z * sideEquation p q r =
        sideEquation q p z * sideEquation q p r := by
    intro p q z r
    by_cases hs : p+q = 0
    · have hq : q = -p := by linear_combination hs
      simp [sideEquation, hq, div_neg, Complex.neg_im]
    · have hs' : q+p ≠ 0 := by simpa [add_comm] using hs
      simp only [sideEquation, ite_eq_right hs, ite_eq_right hs']
      have hc : orthogonalCenter p q = orthogonalCenter q p := by
        unfold orthogonalCenter
        ring
      rw [hc]
  have mem_triangle_three_iff_local (p q r z : ℂ) (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) :
      z ∈ triangle {p,q,r} ↔ z ∈ disk ∧
        0 ≤ sideEquation p q z * sideEquation p q r ∧
        0 ≤ sideEquation q r z * sideEquation q r p ∧
        0 ≤ sideEquation r p z * sideEquation r p q := by
    classical
    constructor
    · intro hz
      exact ⟨hz.1, hz.2 p (by simp) q (by simp) r (by simp) hpq hqr hrp,
        hz.2 q (by simp) r (by simp) p (by simp) hqr hrp hpq,
        hz.2 r (by simp) p (by simp) q (by simp) hrp hpq hqr⟩
    · rintro ⟨hz,h₁,h₂,h₃⟩
      refine ⟨hz, ?_⟩
      intro a ha b hb c hc hab hbc hca
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
      rcases ha with rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl | rfl <;>
        first | exact (hab rfl).elim | exact (hbc rfl).elim | exact (hca rfl).elim |
          exact h₁ | exact h₂ | exact h₃ |
          (rw [sideEquation_swap_product_local]; assumption)
  obtain ⟨r,hr,hqr,hrp,hV⟩ := triangle_third_vertex_local V hpV hqV hpq
  have hru := V.property.2 r hr
  have hV' : V.val = {p,q,r} := hV
  let R := idealDiskSideReflection p q
  have hRp := reflection_unit hp hq hpq hp
  have hRq := reflection_unit hp hq hpq hq
  have hRr := reflection_unit hp hq hpq hru
  have hRr_inv : R (R r) = r := reflection_involutive_unit_local hp hq hpq hru
  have hR_inj : Set.InjOn R V.val := by
    intro x hx y hy hxy
    exact reflection_inj_closed hp hq hpq (V.property.2 x hx).le (V.property.2 y hy).le hxy
  have hB : reflectedVertices V.val p q = {R p,R q,R r} := by
    rw [reflectedVertices,hV']
    simp [R,idealDiskSideReflection_endpoints hp hq hpq,Finset.image_insert,Finset.image_singleton]
  have hRpq : R p ≠ R q := by intro h; exact hpq (reflection_inj_closed hp hq hpq hp.le hq.le h)
  have hRqr : R q ≠ R r := by intro h; exact hqr (reflection_inj_closed hp hq hpq hq.le hru.le h)
  have hRrp : R r ≠ R p := by intro h; exact hrp (reflection_inj_closed hp hq hpq hru.le hp.le h)
  constructor
  · intro hz
    rw [hB]
    apply (mem_triangle_three_iff_local (R p) (R q) (R r) (R z) hRpq hRqr hRrp).mpr
    obtain ⟨hzD,h₁,h₂,h₃⟩ := (mem_triangle_three_iff_local p q r z hpq hqr hrp).mp (hV ▸ hz)
    have hRz : ‖R z‖ < 1 := idealDiskSideReflection_mem_disk_g6 hp hq hpq hzD
    refine ⟨hRz,?_,?_,?_⟩
    · exact (reflection_side_product_transport hp hq hp hq hpq hzD.le hru).mpr h₁
    · exact (reflection_side_product_transport hp hq hq hru hpq hzD.le hp).mpr h₂
    · exact (reflection_side_product_transport hp hq hru hp hpq hzD.le hq).mpr h₃
  · intro hz
    obtain ⟨hzD,h₁,h₂,h₃⟩ := (mem_triangle_three_iff_local (R p) (R q) (R r) z hRpq hRqr hRrp).mp (hB ▸ hz)
    have hRzD : R z ∈ disk := idealDiskSideReflection_mem_disk_g6 hp hq hpq hzD
    have hRinv : R (R z) = z := idealDiskSideReflection_involutive_disk_g6 hp hq hpq z hzD
    rw [hV']
    apply (mem_triangle_three_iff_local p q r (R z) hpq hqr hrp).mpr
    refine ⟨hRzD,?_,?_,?_⟩
    · have hx := (reflection_side_product_transport (a := R p) (b := R q)
          (z := z) (r := R r) hp hq hRp hRq hpq hzD.le hRr).mpr h₁
      simpa [R, idealDiskSideReflection_endpoints hp hq hpq, hRinv, hRr_inv] using hx
    · have hx := (reflection_side_product_transport (a := R q) (b := R r)
          (z := z) (r := R p) hp hq hRq hRr hpq hzD.le hRp).mpr h₂
      simpa [R, idealDiskSideReflection_endpoints hp hq hpq, hRinv, hRr_inv] using hx
    · have hx := (reflection_side_product_transport (a := R r) (b := R p)
          (z := z) (r := R q) hp hq hRr hRp hpq hzD.le hRq).mpr h₃
      simpa [R, idealDiskSideReflection_endpoints hp hq hpq, hRinv, hRr_inv] using hx

end HolomorphicAnosov.IdealDiskTriangle

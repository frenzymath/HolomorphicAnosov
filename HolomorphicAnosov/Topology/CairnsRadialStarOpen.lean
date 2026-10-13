import HolomorphicAnosov.Topology.CairnsRadialStarNonempty
import Mathlib.Analysis.Complex.Circle

namespace HolomorphicAnosov
open Set

/-- The strict Cairns radial star is open in the complex plane.

Source: Cairns (1951), §4(A), printed pp.863--864.  In direction coordinates,
the inverse front radius is continuous and positive; the strict radial region is
the pullback of `0 < s < r(v)` over the open semicircle interior.  Polar
coordinates away from the excluded center, together with the center-side
interior witness, give an ambient open set.  This named provider isolates that
polar-coordinate argument for the parent radial-star geometry theorem. -/
theorem cairns_radial_star_isOpen
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (_hν : IsCompact ν)
    (_hE : E₁ ≠ E₂)
    (_hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (_hE₁ : E₁ ∈ ν) (_hE₂ : E₂ ∈ ν)
    (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ)) :
    let N := (E₁ + E₂) / 2
    let γ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (z - E₁)).im}
    IsOpen γ := by
  dsimp only
  let N := (E₁ + E₂) / 2
  have hN' : N ∉ ν := hN
  let c := (star (E₂ - E₁) * (Eₚ - E₁)).im
  let d := E₂ - E₁
  let H : Set ℂ := {z | 0 < c * (star d * (z - E₁)).im}
  let A : Set Circle := {v | 0 ≤ c * (star d * (v : ℂ)).im}
  have hcross (z : ℂ) : (star d * (z - E₁)).im = (star d * (z - N)).im := by
    simp [d, N, Complex.mul_im]
    ring
  have hHopen : IsOpen H := by
    apply isOpen_lt continuous_const
    fun_prop
  have hzpos (z : H) : 0 < ‖(z : ℂ) - N‖ := by
    apply norm_pos_iff.mpr
    intro heq
    have h := z.property
    change 0 < c * (star d * ((z : ℂ) - E₁)).im at h
    rw [hcross, heq] at h
    simp at h
  let dir : H → Circle := fun z ↦ ⟨((z : ℂ) - N) / (‖(z : ℂ) - N‖ : ℂ), by
    have hn : ‖((z : ℂ) - N) / (‖(z : ℂ) - N‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hzpos z)]
      exact div_self (hzpos z).ne'
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hn⟩
  have hdirside (z : H) : 0 ≤ c * (star d * (dir z : ℂ)).im := by
    change 0 ≤ c * (star d * (((z : ℂ) - N) / (‖(z : ℂ) - N‖ : ℂ))).im
    rw [← mul_div_assoc, Complex.div_ofReal_im, ← mul_div_assoc]
    have h := z.property
    change 0 < c * (star d * ((z : ℂ) - E₁)).im at h
    rw [hcross] at h
    exact (div_pos h (hzpos z)).le
  let g : H → A := fun z ↦ ⟨dir z, hdirside z⟩
  have hdircont : Continuous dir := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      exact Complex.ofReal_ne_zero.mpr (hzpos z).ne'
  have hgcont : Continuous g := hdircont.subtype_mk hdirside
  let R : H → ℝ := fun z ↦ ‖(ds.symm (g z) : ℂ) - N‖
  have hRcont : Continuous R := by fun_prop
  have hRpos (z : H) : 0 < R z := by
    apply norm_pos_iff.mpr
    intro heq
    exact hN' ((sub_eq_zero.mp heq) ▸ (ds.symm (g z)).property)
  have hUopen : IsOpen {z : H | ‖(z : ℂ) - N‖ < R z} :=
    isOpen_lt (by fun_prop) hRcont
  have heq : {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧ 0 < c * (star d * (z - E₁)).im} =
      Subtype.val '' {z : H | ‖(z : ℂ) - N‖ < R z} := by
    ext z
    constructor
    · rintro ⟨Q, hQ, t, ht, heq, hzside⟩
      let zH : H := ⟨z, hzside⟩
      have hz : z - N = t • (Q - N) := by rw [heq]; module
      have hnorm : ‖z - N‖ = t * ‖Q - N‖ := by
        rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      have hQpos : 0 < ‖Q - N‖ := by
        apply norm_pos_iff.mpr
        intro heq
        exact hN' ((sub_eq_zero.mp heq) ▸ hQ)
      have hg : g zH = ds ⟨Q, hQ⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        change (z - N) / (‖z - N‖ : ℂ) = _
        rw [hds]
        change (z - N) / (‖z - N‖ : ℂ) = (Q - N) / (‖Q - N‖ : ℂ)
        rw [hnorm, hz]
        push_cast
        change (t : ℂ) * (Q - N) / ((t : ℂ) * (‖Q - N‖ : ℂ)) = _
        field_simp [Complex.ofReal_ne_zero.mpr ht.1.ne',
          Complex.ofReal_ne_zero.mpr hQpos.ne']
      refine ⟨zH, ?_, rfl⟩
      change ‖z - N‖ < ‖(ds.symm (g zH) : ℂ) - N‖
      rw [hg, ds.symm_apply_apply, hnorm]
      exact (mul_lt_iff_lt_one_left hQpos).mpr ht.2
    · rintro ⟨zH, hz, rfl⟩
      let Q : ν := ds.symm (g zH)
      let t : ℝ := ‖(zH : ℂ) - N‖ / R zH
      have htpos : 0 < t := div_pos (hzpos zH) (hRpos zH)
      have htlt : t < 1 := (div_lt_one (hRpos zH)).mpr hz
      refine ⟨Q, Q.property, t, ⟨htpos, htlt⟩, ?_, zH.property⟩
      have hdir := hds Q
      have hdQ : ds Q = g zH := ds.apply_symm_apply (g zH)
      rw [hdQ] at hdir
      change ((zH : ℂ) - N) / (‖(zH : ℂ) - N‖ : ℂ) =
        ((Q : ℂ) - N) / (R zH : ℂ) at hdir
      have hn : (‖(zH : ℂ) - N‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hzpos zH).ne'
      have hr : (R zH : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hRpos zH).ne'
      have heq := (div_eq_div_iff hn hr).mp hdir
      dsimp [t]
      change (zH : ℂ) = (1 - ‖(zH : ℂ) - N‖ / R zH : ℝ) • N +
        (‖(zH : ℂ) - N‖ / R zH : ℝ) • (Q : ℂ)
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
      field_simp
      linear_combination heq
  change IsOpen {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
    z = (1 - t) • N + t • Q ∧ 0 < c * (star d * (z - E₁)).im}
  rw [heq]
  exact hHopen.isOpenMap_subtype_val _ hUopen

end HolomorphicAnosov

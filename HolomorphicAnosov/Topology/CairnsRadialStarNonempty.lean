import HolomorphicAnosov.Topology.CairnsNormalizedInteriorDirection

namespace HolomorphicAnosov
open Set Complex

/-- The strict radial-star set is nonempty under the explicit direction homeomorphism.

Source: Cairns (1951), §4(A), pp.863--864. Choose the normalized quarter-turned
interior direction from `cairns_normalized_interior_direction`, pull it back along
`ds`, and use the midpoint of the resulting radial segment. The direction
normalization supplied by `hds` makes the side expression strictly positive. -/
theorem cairns_radial_star_nonempty
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hE : E₁ ≠ E₂)
    (hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ)) :
    let N := (E₁ + E₂) / 2
    let γ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (z - E₁)).im}
    γ.Nonempty := by
  dsimp
  let d : ℂ := E₂ - E₁
  let c : ℝ := (star d * (Eₚ - E₁)).im
  have hd : d ≠ 0 := sub_ne_zero.mpr hE.symm
  obtain ⟨v, hv⟩ := cairns_normalized_interior_direction E₁ E₂ Eₚ hE hSide
  have hvA : 0 ≤ c * (star d * (v : ℂ)).im := hv.le
  let vA : {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im} := ⟨v, by simpa [c, d] using hvA⟩
  let Q : ν := ds.symm vA
  let t : ℝ := 1 / 2
  refine ⟨(1 - t) • ((E₁ + E₂) / 2) + t • (Q : ℂ), Q, Q.property, t, ?_, ?_⟩
  · constructor <;> norm_num [t]
  · constructor
    · rfl
    · change 0 < c * (star d * (((1 - t) • ((E₁ + E₂) / 2) + t • (Q : ℂ)) - E₁)).im
      have hQdir : ((Q : ℂ) - (E₁ + E₂) / 2) =
          (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ) * (v : ℂ) := by
        have hdsQ := hds Q
        have happly : ds Q = vA := ds.apply_symm_apply vA
        rw [happly] at hdsQ
        change (v : ℂ) =
          ((Q : ℂ) - (E₁ + E₂) / 2) /
            (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ) at hdsQ
        have hnormQ : 0 < ‖(Q : ℂ) - (E₁ + E₂) / 2‖ := by
          apply norm_pos_iff.mpr
          intro hzero
          apply hN
          exact (sub_eq_zero.mp hzero).symm ▸ Q.property
        have hdsQ' : (v : ℂ) =
            ((Q : ℂ) - (E₁ + E₂) / 2) /
              (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ) := by
          simpa [vA] using hdsQ
        have hden : (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ) ≠ 0 :=
          ofReal_ne_zero.mpr (ne_of_gt hnormQ)
        have hmul := (div_eq_iff hden).mp hdsQ'.symm
        simpa [mul_comm] using hmul
      have hIm : (star d * ((Q : ℂ) - (E₁ + E₂) / 2)).im =
          ‖(Q : ℂ) - (E₁ + E₂) / 2‖ * (star d * (v : ℂ)).im := by
        rw [hQdir]
        simp [Complex.mul_im, Complex.mul_re]
        ring
      have hZ : ((1 - t) • ((E₁ + E₂) / 2) + t • (Q : ℂ)) - E₁ =
          d / 2 + t • ((Q : ℂ) - (E₁ + E₂) / 2) := by
        dsimp [t, d]
        norm_num [smul_eq_mul]
        ring
      have hImZ : (star d * (((1 - t) • ((E₁ + E₂) / 2) + t • (Q : ℂ)) - E₁)).im =
          t * (star d * ((Q : ℂ) - (E₁ + E₂) / 2)).im := by
        rw [hZ]
        simp [Complex.mul_im, Complex.mul_re]
        ring
      rw [hImZ, hIm]
      have hnormQ : 0 < ‖(Q : ℂ) - (E₁ + E₂) / 2‖ := by
        apply norm_pos_iff.mpr
        intro hzero
        apply hN
        exact (sub_eq_zero.mp hzero).symm ▸ Q.property
      have htv : 0 < t := by norm_num [t]
      have hv' : 0 < c * (star d * (v : ℂ)).im := by simpa [c, d] using hv
      have hp := mul_pos htv (mul_pos hnormQ hv')
      convert hp using 1; ring

end HolomorphicAnosov

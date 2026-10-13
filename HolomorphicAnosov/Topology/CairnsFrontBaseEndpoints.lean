import HolomorphicAnosov.Topology.CairnsRadialPointUniqueness

namespace HolomorphicAnosov
open Set

/-- The only front points on the base line of the Cairns radial star are its
specified base endpoints.

Source: Cairns (1951), §4(A), printed pp.863–864. A front point on the base line
has displacement `a (E₂-E₁)` from the midpoint for a real nonzero `a`. For
positive `a` its ray agrees with the ray to `E₂`; for negative `a` it agrees
with the ray to `E₁`. Injectivity of the normalized direction map forces the
corresponding front points to agree. -/
theorem cairns_front_base_endpoints
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hE : E₁ ≠ E₂)
    (hE₁ : E₁ ∈ ν) (hE₂ : E₂ ∈ ν) (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ))
    {Q : ℂ} (hQ : Q ∈ ν) (hbase : (star (E₂ - E₁) * (Q - E₁)).im = 0) :
    Q = E₁ ∨ Q = E₂ := by
  let N := (E₁ + E₂) / 2
  let d := E₂ - E₁
  have hd : d ≠ 0 := sub_ne_zero.mpr hE.symm
  have hN' : N ∉ ν := hN
  have hQne : Q - N ≠ 0 := by
    intro h
    exact hN' ((sub_eq_zero.mp h) ▸ hQ)
  have hcross : (star d * (Q - N)).im = 0 := by
    convert hbase using 1
    simp [d, N, Complex.mul_im]
    ring
  have him : ((Q - N) / d).im = 0 := by
    rw [Complex.div_im]
    have he : (Q - N).im * d.re - (Q - N).re * d.im = 0 := by
      simp [Complex.mul_im] at hcross ⊢
      nlinarith [hcross]
    rw [← sub_div, he, zero_div]
  let a : ℝ := ((Q - N) / d).re
  have ha : Q - N = (a : ℂ) * d := by
    have he : (Q - N) / d = (a : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using him
    exact (div_eq_iff hd).mp he
  have hane : a ≠ 0 := by
    intro h
    rw [h, Complex.ofReal_zero, zero_mul] at ha
    exact hQne ha
  have hNall : ∀ R ∈ ν, R ≠ N := by
    intro R hR heq
    exact hN' (heq ▸ hR)
  let A := {v : Circle | 0 ≤
    (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im}
  rcases lt_or_gt_of_ne hane with hneg | hpos
  · left
    have heq : (1 - (1 / 2 : ℝ)) • N + (1 / 2 : ℝ) • Q =
        (1 - (-a)) • N + (-a) • E₁ := by
      have heq : Q - (E₁ + E₂) / 2 = (a : ℂ) * (E₂ - E₁) := ha
      dsimp [N]
      push_cast
      linear_combination heq / 2
    have hu := cairns_radial_point_unique hNall ds (fun v : A ↦ (v : Circle))
      Subtype.val_injective hds (Q := ⟨Q, hQ⟩) (R := ⟨E₁, hE₁⟩)
      (by norm_num : (0 : ℝ) < 1 / 2) (neg_pos.mpr hneg) heq
    exact congrArg Subtype.val hu.1
  · right
    have heq : (1 - (1 / 2 : ℝ)) • N + (1 / 2 : ℝ) • Q =
        (1 - a) • N + a • E₂ := by
      have heq : Q - (E₁ + E₂) / 2 = (a : ℂ) * (E₂ - E₁) := ha
      dsimp [N]
      push_cast
      linear_combination heq / 2
    have hu := cairns_radial_point_unique hNall ds (fun v : A ↦ (v : Circle))
      Subtype.val_injective hds (Q := ⟨Q, hQ⟩) (R := ⟨E₂, hE₂⟩)
      (by norm_num : (0 : ℝ) < 1 / 2) hpos heq
    exact congrArg Subtype.val hu.1

end HolomorphicAnosov

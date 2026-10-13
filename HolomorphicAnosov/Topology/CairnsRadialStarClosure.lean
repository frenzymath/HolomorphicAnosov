import HolomorphicAnosov.Topology.CairnsInteriorRayClosure
import HolomorphicAnosov.Topology.CairnsSemicircleInteriorDense
import HolomorphicAnosov.Topology.CairnsNormalizedInteriorDirection
import HolomorphicAnosov.Topology.CairnsRadialStarClosureSubset

namespace HolomorphicAnosov
open Set

/-- The closure of the strict Cairns radial star is exactly the closed sweep.

Source: Cairns (1951), §4(A), printed pp.863–864. Compactness gives the forward
inclusion. Each closed radial segment in a strict-side direction lies in the
closure by continuity in its radial parameter. Strict-side directions are dense
in the closed semicircle; the continuous inverse direction map transports this
density to the front. Holding the radial parameter fixed and taking limits
therefore includes both boundary rays as well as all interior directions. -/
theorem cairns_radial_star_closure_eq_sweep
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hν : IsCompact ν)
    (hE : E₁ ≠ E₂)
    (hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ)) :
    let N := (E₁ + E₂) / 2
    closure {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (z - E₁)).im} =
    {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • N + t • Q} := by
  dsimp only
  apply Subset.antisymm (cairns_radial_star_closure_subset_sweep E₁ E₂ Eₚ ν hν hSide hN)
  rintro z ⟨Q, hQ, t, ht, rfl⟩
  let A := {v : Circle | 0 ≤
    (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im}
  obtain ⟨w, hw⟩ := cairns_normalized_interior_direction E₁ E₂ Eₚ hE hSide
  have hdense := cairns_semicircle_interior_dense
    (star (E₂ - E₁) * (Eₚ - E₁)).im (E₂ - E₁) w hw
  let f : A → ℂ := fun v ↦ (1 - t) • ((E₁ + E₂) / 2) + t • (ds.symm v : ℂ)
  have hf : Continuous f := by fun_prop
  have hmap : MapsTo f
      {v : A | 0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
        (star (E₂ - E₁) * ((v : Circle) : ℂ)).im}
      (closure {z : ℂ | ∃ R ∈ ν, ∃ s ∈ Ioo (0 : ℝ) 1,
        z = (1 - s) • ((E₁ + E₂) / 2) + s • R ∧
        0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
          (star (E₂ - E₁) * (z - E₁)).im}) := by
    intro v hv
    change 0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
      (star (E₂ - E₁) * ((v : Circle) : ℂ)).im at hv
    apply cairns_interior_ray_subset_closure E₁ E₂ Eₚ ν (ds.symm v).property _ ht
    have hnorm : 0 < ‖(ds.symm v : ℂ) - (E₁ + E₂) / 2‖ := by
      apply norm_pos_iff.mpr
      intro heq
      exact hN ((sub_eq_zero.mp heq) ▸ (ds.symm v).property)
    have hdir := hds (ds.symm v)
    rw [ds.apply_symm_apply] at hdir
    have hv' : 0 <
        ((star (E₂ - E₁) * (Eₚ - E₁)).im *
          (star (E₂ - E₁) * ((ds.symm v : ℂ) - (E₁ + E₂) / 2)).im) /
            ‖(ds.symm v : ℂ) - (E₁ + E₂) / 2‖ := by
      rw [hdir, ← mul_div_assoc, Complex.div_ofReal_im, ← mul_div_assoc] at hv
      exact hv
    have hpos := (div_pos_iff_of_pos_right hnorm).mp hv'
    have hcross : (star (E₂ - E₁) * ((ds.symm v : ℂ) - E₁)).im =
        (star (E₂ - E₁) * ((ds.symm v : ℂ) - (E₁ + E₂) / 2)).im := by
      simp [Complex.mul_im]
      ring
    rw [hcross]
    exact hpos
  simpa [f, closure_closure] using
    hf.continuousWithinAt.mem_closure (hdense (ds ⟨Q, hQ⟩)) hmap

end HolomorphicAnosov

import HolomorphicAnosov.Topology.CairnsRadialSweepCompact

namespace HolomorphicAnosov
open Set

/-- The closure of the strict radial star is contained in its closed sweep.

Source: Cairns (1951), §4(A), pp.863--864.  Every strict radial point uses a
parameter in `Ioo (0,1)`, hence also in `Icc (0,1)`.  The resulting closed sweep
is compact, therefore closed, and contains the star; closure minimality gives
the asserted inclusion. -/
theorem cairns_radial_star_closure_subset_sweep
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hν : IsCompact ν)
    (_hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (_hN : (E₁ + E₂) / 2 ∉ ν) :
    let N := (E₁ + E₂) / 2
    let S := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • N + t • Q}
    let γ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
        (star (E₂ - E₁) * (z - E₁)).im}
    closure γ ⊆ S := by
  dsimp
  let N : ℂ := (E₁ + E₂) / 2
  let S : Set ℂ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
    z = (1 - t) • N + t • Q}
  let γ : Set ℂ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
    z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im *
        (star (E₂ - E₁) * (z - E₁)).im}
  have hSweepCompact : IsCompact S := by
    dsimp [S, N]
    exact cairns_radial_sweep_compact (N := (E₁ + E₂) / 2) hν
  have hγS : γ ⊆ S := by
    intro z hz
    rcases hz with ⟨Q, hQ, t, ht, hzt, _⟩
    exact ⟨Q, hQ, t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hzt⟩
  exact closure_minimal hγS hSweepCompact.isClosed

end HolomorphicAnosov

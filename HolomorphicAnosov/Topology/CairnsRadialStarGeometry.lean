import HolomorphicAnosov.Topology.CairnsRadialPointUniqueness
import HolomorphicAnosov.Topology.CairnsNormalizedInteriorDirection
import HolomorphicAnosov.Topology.CairnsRadialStarNonempty
import HolomorphicAnosov.Topology.CairnsRadialSweepCompact
import HolomorphicAnosov.Topology.CairnsRadialSweepUnique
import HolomorphicAnosov.Topology.CairnsRadialStarClosureSubset
import HolomorphicAnosov.Topology.CairnsBaseSegmentInSweep
import HolomorphicAnosov.Topology.CairnsRadialStarClosure
import HolomorphicAnosov.Topology.CairnsRadialStarOpen
import HolomorphicAnosov.Topology.CairnsRadialStarFrontier
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Subpath

namespace HolomorphicAnosov
open Set

/-- The geometric star/frontier/closed-sweep component of Cairns's radial construction.

Source: Cairns (1951), §4(A), printed pp.863--864.  Once the normalized direction
map is a homeomorphism onto the selected closed semicircle, polar coordinates and
the positive continuous inverse radius identify the strict radial star, its base
frontier, and its closed sweep.  The proof is retained as a named provider because
the parent construction still requires the full endpoint and frontier argument. -/
theorem cairns_radial_star_geometry
    (E₁ E₂ Eₚ : ℂ) (ν : Set ℂ) (hν : IsCompact ν)
    (hE : E₁ ≠ E₂)
    (hSide : (star (E₂ - E₁) * (Eₚ - E₁)).im ≠ 0)
    (hE₁ : E₁ ∈ ν) (hE₂ : E₂ ∈ ν)
    (hN : (E₁ + E₂) / 2 ∉ ν)
    (ds : ν ≃ₜ {v : Circle | 0 ≤
      (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (v : ℂ)).im})
    (hds : ∀ Q : ν, ((ds Q : Circle) : ℂ) =
      ((Q : ℂ) - (E₁ + E₂) / 2) / (‖(Q : ℂ) - (E₁ + E₂) / 2‖ : ℂ)) :
    let N := (E₁ + E₂) / 2
    let S := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • N + t • Q}
    let γ := {z : ℂ | ∃ Q ∈ ν, ∃ t ∈ Ioo (0 : ℝ) 1,
      z = (1 - t) • N + t • Q ∧
      0 < (star (E₂ - E₁) * (Eₚ - E₁)).im * (star (E₂ - E₁) * (z - E₁)).im}
    γ.Nonempty ∧ IsOpen γ ∧ frontier γ = segment ℝ E₁ E₂ ∪ ν ∧
      closure γ = S ∧
      (∀ z ∈ closure γ, z ≠ N → ∃! w : ν × Icc (0 : ℝ) 1,
        z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)) := by
  dsimp only
  have hnonempty := cairns_radial_star_nonempty E₁ E₂ Eₚ ν hE hSide hN ds hds
  have hopen := cairns_radial_star_isOpen E₁ E₂ Eₚ ν hν hE hSide hE₁ hE₂ hN ds hds
  have hfrontier := cairns_radial_star_frontier E₁ E₂ Eₚ ν hν hE hSide hE₁ hE₂ hN ds hds
  have hclosure := cairns_radial_star_closure_eq_sweep E₁ E₂ Eₚ ν hν hE hSide hN ds hds
  refine ⟨hnonempty, hopen, hfrontier, hclosure, ?_⟩
  intro z hz hzN
  have hNall : ∀ Q ∈ ν, Q ≠ (E₁ + E₂) / 2 := by
    intro Q hQ heq
    exact hN (heq ▸ hQ)
  rw [hclosure] at hz
  exact cairns_radial_sweep_unique hNall ds (fun v ↦ (v : Circle))
    Subtype.val_injective hds hz hzN

end HolomorphicAnosov

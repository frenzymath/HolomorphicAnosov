import HolomorphicAnosov.Topology.CompactRadialSweepHomeomorph
import HolomorphicAnosov.Topology.CairnsPositiveRadialRadius
import HolomorphicAnosov.Topology.CairnsRadialStarGeometry
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Subpath

namespace HolomorphicAnosov
open Set

/-- A compact front whose normalized direction is a homeomorphism onto the
selected closed semicircle bounds the literal open radial star together with
its base chord. This is the conditional radial geometry used by Cairns (1951),
§4(A), printed pp.863--864, after constructing the prescribed target front.
The proof below is an agent expansion of that source step. The existence of
the direction homeomorphism for an affine chord-replacement front is a separate
obligation; it is not inferred from an arbitrary arc parametrization.

Proof. Put N=(E₁+E₂)/2 and let A be the displayed closed direction semicircle.
The transverse cross-product is nonzero, so A is a genuine semicircle with
endpoints the directions NE₁ and NE₂. The inverse direction homeomorphism
provides a continuous radius r(v)=|ds⁻¹(v)-N|>0 on A. Its endpoints are exactly
E₁ and E₂, by normalization and injectivity. Compactness gives a positive
minimum and finite maximum radius. Each front point is N+r(v)v.

Away from N, polar coordinates identify the literal open star with the set
of strict directions in A and radii 0<r<r(v). This is open in the plane and
nonempty. The compact parametrization (v,t)↦N+t*r(v)*v, 0≤t≤1, has image the
closed sweep. Its strict parameter locus is dense, including at both endpoint
directions and at t=0,1; hence this image is exactly the star's closure.
The boundary consists of its top front (t=1), the two endpoint radial segments,
and the center. The two endpoint segments join to [E₁,E₂], because N is their
midpoint, proving the claimed frontier. The positive radial expression fixes
v uniquely by normalization, then fixes t by its norm, which proves uniqueness
away from N. The radius continuity and positivity clauses follow from the
continuous inverse direction map and center exclusion. When both source and
target fronts satisfy these clauses, compact_radial_sweep_homeomorph supplies
the continuous affine radial extension; this theorem asserts only the radial
star geometry needed for that separate application.
-/
theorem cairns_target_radial_star_extension
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
        z = (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)) ∧
      Continuous (fun v ↦ ‖(ds.symm v : ℂ) - N‖) ∧
      (∀ v, 0 < ‖(ds.symm v : ℂ) - N‖) := by
  dsimp
  have hgeom := cairns_radial_star_geometry E₁ E₂ Eₚ ν hν hE hSide hE₁ hE₂ hN ds hds
  have hr := continuous_positive_inverse_direction_radius ((E₁ + E₂) / 2) ν (by
    intro Q hQ hEq
    exact hN (hEq ▸ hQ)) ds
  rcases hgeom with ⟨h1, h2, h3, h4, h5⟩
  rcases hr with ⟨h6, h7⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end HolomorphicAnosov

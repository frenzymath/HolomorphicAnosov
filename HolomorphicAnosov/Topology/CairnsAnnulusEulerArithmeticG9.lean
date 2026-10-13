import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

/-!
# Arithmetic genus-zero consequence for a two-boundary Euler identity

Source: Gallier--Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
Theorem 6.1, p.96. The finite normal form gives χ = 2 − 2g − b; for b=2,
χ = 0 forces g=0 by integer arithmetic.
-/

namespace HolomorphicAnosov.Topology
open GallierXu

/-- The two-boundary normal-form Euler identity has genus zero when χ vanishes. -/
theorem annulus_euler_zero_genus_zero_g9
    {χ : ℤ} {g : ℕ}
    (hχ : χ = 0)
    (hEuler : χ = (2 : ℤ) - 2 * (g : ℤ) - 2) :
    g = 0 := by
  have hg : (g : ℤ) = 0 := by linarith
  exact_mod_cast hg

/-/ The finite planar annulus count reduces to integer arithmetic once the
triangle-edge, boundary, and two-boundary face equations have been extracted
from the straight subdivision.  For an annulus the face equation is
`F = 2 Vᵢ + V_b`; the `- 2` term belongs to a disk and must not be used here.
-/
theorem annulus_chi_zero_of_planar_counts_g9
    {Vᵢ V_b Eᵢ E_b F : ℤ}
    (htri : 3 * F = 2 * Eᵢ + E_b)
    (hboundary : E_b = V_b)
    (hfaces : F = 2 * Vᵢ + V_b) :
    (Vᵢ + V_b) - (Eᵢ + E_b) + F = 0 := by
  linarith

end HolomorphicAnosov.Topology


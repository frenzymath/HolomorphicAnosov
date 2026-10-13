import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusNormalFormCylinder
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierSubset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
# Finite polygonal exterior-annulus core

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
preliminary 2(B), printed p.860 (physical pp.2--3). Cairns omits the finite
exterior-annulus straightening used later on p.861. This module isolates that
omission as a named theorem so the parent can depend on it explicitly.
-/

open Set

namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Finite polygonal exterior-annulus construction required by Cairns 2(B).

The current agent supplement reduces the omitted step to construction of a
finite embedded triangulation of `R \ interior D`, verification of its two
boundary cycles and orientable manifold links, application of
`GallierXu.orientable_triangulated_surface_normal_form`, and realization of
the resulting genus-zero two-boundary word by a quotient cylinder. The imported
Gallier--Xu theorem currently has its own named theorem-level `sorry`, and no
independent public polygonal annulus API exists, so this is an honest named
proof boundary rather than an asserted completion. -/
theorem cairns_polygonal_annulus_base
    (D R : Set Plane)
    (hcompact : IsCompact D)
    (hregular : closure (interior D) = D)
    (hinterior_nonempty : (interior D).Nonempty)
    (hinterior_path : IsPathConnected (interior D))
    (hexterior_path : IsPathConnected Dᶜ)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)} : Set Plane)) ∧
      frontier D = P.boundary ℝ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧
      R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R) :
    ∃ (γ : frontier D ≃ₜ Metric.sphere (0 : Plane) 1)
      (Ψ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}),
      (∀ x : frontier D, ∃ y : ↥(R \ interior D),
        (y : Plane) = (x : Plane) ∧ (Ψ y : Plane) = (γ x : Plane)) ∧
      (fun x : ↥(R \ interior D) ↦ (Ψ x : Plane)) ''
        {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
          Metric.sphere (0 : Plane) 2 := by
  obtain ⟨N, K, B, o, hpure, hconnected, hinter, hlinks, hboundary, horiented, H,
      hinnerBoundary, houterBoundary⟩ :=
    cairns_polygonal_annulus_triangulation D R hcompact hregular hinterior_nonempty
      hinterior_path hexterior_path hpolygon hrectangle hcontain
  have hfrontierD := cairns_polygonal_annulus_frontier_subset D R hcompact hcontain
  exact cairns_polygonal_annulus_normal_form_cylinder D R K B o hpure hconnected hinter hlinks
    hboundary horiented H hfrontierD hinnerBoundary houterBoundary

end HolomorphicAnosov.Topology


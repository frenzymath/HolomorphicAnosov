import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusTriangulation
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusGenusZeroG9
import HolomorphicAnosov.Topology.CairnsAnnulusRectangleRadialMap
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusNormalWordCylinder
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusBoundaryTransport
import HolomorphicAnosov.Topology.GallierXuOrientableSurfaceNormalForm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
# Normal form and cylinder realization for the polygonal exterior annulus

Source: Gallier--Xu, *A Guide to the Classification Theorem for Compact
Surfaces*, Theorem 6.1 and Lemma 6.1, pp.88--96, together with the explicit
two-boundary quotient-cylinder realization described after the finite
triangulation in Cairns preliminary 2(B), p.860. This module isolates the
finite normal-form application and its geometric transport from the abstract
carrier to the literal annulus.
-/

open Set

namespace HolomorphicAnosov.Topology

open GallierXu

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A finite oriented two-boundary triangulation of the literal annulus can be
straightened to the round closed annulus, while retaining the prescribed inner
boundary and mapping the outer boundary to the radius-two circle.

The proof applies the named Gallier--Xu finite normal form, uses the Euler
identity and the fact that the two boundary components force genus zero, and
then realizes the resulting two-boundary word as the quotient cylinder
`([0,1]×[1,2])/((0,r)∼(1,r))`. The final radial correction is deliberately
left to the existing `cairns_annulus_boundary_correction` consumer. The finite
normal-form/cylinder assembly is a genuine proposition and is recorded here as
the remaining source-backed theorem-level proof boundary.
-/
theorem cairns_polygonal_annulus_normal_form_cylinder
    (D R : Set Plane)
    {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (horiented : Oriented (trianglePresentation K o))
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hfrontierD : frontier D ⊆ R \ interior D)
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1)) :
    ∃ (γ : frontier D ≃ₜ Metric.sphere (0 : Plane) 1)
      (Ψ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}),
      (∀ x : frontier D, ∃ y : ↥(R \ interior D),
        (y : Plane) = (x : Plane) ∧ (Ψ y : Plane) = (γ x : Plane)) ∧
      (fun x : ↥(R \ interior D) ↦ (Ψ x : Plane)) ''
        {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        Metric.sphere (0 : Plane) 2 := by
  have hnormal :=
    GallierXu.orientable_triangulated_surface_normal_form K (by norm_num)
      hpure hconnected hincidence hlinks B hboundary o horiented
  obtain ⟨g, sequence, H₀, hH₀, hσ, hEulerNormal⟩ := hnormal
  have hg : g = 0 :=
    cairns_polygonal_annulus_genus_zero_g9 D R K B hpure hconnected hincidence
      hlinks hboundary H hinnerBoundary houterBoundary o horiented g hEulerNormal
  obtain ⟨T, hTinner, hTouter⟩ :=
    cairns_polygonal_annulus_normal_word_cylinder hg
  obtain ⟨σ, hσ⟩ := hσ
  exact cairns_polygonal_annulus_boundary_transport D R K B hfrontierD H hinnerBoundary
    houterBoundary sequence H₀ σ hσ hg T hTinner hTouter

end HolomorphicAnosov.Topology


import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Frontier decomposition for the literal Cairns annulus

This helper isolates the elementary set identity used by the prescribed-boundary
parameterization.  For compact regular-closed D contained in the interior of a
compact R, the frontier of `R \ interior D` is the union of the two frontiers.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The annulus frontier is exactly the union of its inner and outer frontiers. -/
theorem cairns_polygonal_annulus_frontier_decomposition
    (D R : Set Plane) (hcompactD : IsCompact D) (hcompactR : IsCompact R)
    (hregular : closure (interior D) = D) (hcontain : D ⊆ interior R) :
    frontier (R \ interior D) = frontier D ∪ frontier R := by
  have hclosedD : IsClosed D := hcompactD.isClosed
  have hclosedR : IsClosed R := hcompactR.isClosed
  have hAcompact : IsCompact (R \ interior D) :=
    hcompactR.inter_right isOpen_interior.isClosed_compl
  have hinteriorA : interior (R \ interior D) = interior R \ D := by
    rw [sdiff_eq, interior_inter, interior_compl, hregular, sdiff_eq]
  rw [hAcompact.isClosed.frontier_eq, hinteriorA,
    hclosedD.frontier_eq, hclosedR.frontier_eq]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union]
  constructor
  · rintro ⟨⟨hxR, hxiD⟩, hx⟩
    by_cases hxD : x ∈ D
    · exact Or.inl ⟨hxD, hxiD⟩
    · exact Or.inr ⟨hxR, fun hxiR ↦ hx ⟨hxiR, hxD⟩⟩
  · rintro (⟨hxD, hxiD⟩ | ⟨hxR, hxiR⟩)
    · exact ⟨⟨interior_subset (hcontain hxD), hxiD⟩, fun hx ↦ hx.2 hxD⟩
    · refine ⟨⟨hxR, fun hx ↦ hxiR (hcontain (interior_subset hx))⟩, ?_⟩
      exact fun hx ↦ hxiR hx.1

end HolomorphicAnosov.Topology


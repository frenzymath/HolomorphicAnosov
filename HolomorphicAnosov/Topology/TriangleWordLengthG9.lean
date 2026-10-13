import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

namespace HolomorphicAnosov.Topology
open GallierXu

/-!
# Length of a triangular boundary word

Gallier--Xu Definition 6.1 records the three directed edge occurrences of an
original triangular face. This reusable finite-count lemma exposes that fact
for the current `triangleWord` adapter.
-/

/-- Every ordered three-vertex triangle contributes exactly three darts. -/
theorem triangleWord_length_g9 {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) : (triangleWord s o).length = 3 := by
  simp [triangleWord]


end HolomorphicAnosov.Topology

namespace HolomorphicAnosov.Topology
open GallierXu

/-- The flattened triangle presentation has three darts per original triangle. -/
theorem trianglePresentation_occurrences_length_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    (occurrences (trianglePresentation K o)).length = 3 * (simplices K 2).card := by
  have h : (occurrences (trianglePresentation K o)).length = (simplices K 2).card * 3 := by
    simp [occurrences, trianglePresentation, triangleWord_length_g9, List.length_flatten]
  calc
    (occurrences (trianglePresentation K o)).length = (simplices K 2).card * 3 := h
    _ = 3 * (simplices K 2).card := by omega

end HolomorphicAnosov.Topology

import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

namespace HolomorphicAnosov.Topology
open GallierXu

/-!
# Number of triangular face words

Gallier--Xu Definition 6.1 retains one presentation word for each original
2-simplex.  This finite indexing fact is used when transporting face counts.
-/

/-- The triangle presentation has exactly one word for every cardinality-three face. -/
theorem trianglePresentation_length_g9 {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) :
    (trianglePresentation K o).length = (simplices K 2).card := by
  simp [trianglePresentation]


end HolomorphicAnosov.Topology

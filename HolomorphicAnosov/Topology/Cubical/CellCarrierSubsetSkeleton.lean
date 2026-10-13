import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision

namespace HolomorphicAnosov.Cubical

/-- Every cell carrier of dimension at most q is included in the q-skeleton. -/
theorem cell_carrier_subset_skeleton {N : ℕ}
    (K : FiniteRectilinearSubdivision N) (q : ℕ)
    (c : ClosedCoordinateCell N) (hc : c ∈ K.cells) (hd : c.dimension ≤ q) :
    c.carrier ⊆ K.skeleton q := by
  intro x hx
  simp only [FiniteRectilinearSubdivision.skeleton, Set.mem_iUnion]
  exact ⟨c, hc, hd, hx⟩

end HolomorphicAnosov.Cubical

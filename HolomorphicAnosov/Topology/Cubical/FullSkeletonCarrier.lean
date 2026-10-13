import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision

namespace HolomorphicAnosov.Cubical

/-- The ambient-dimensional skeleton of a finite coordinate subdivision is its
outer cube. Source: Hatcher Lemma 2.34 pp.137–138, finite-dimensional case.
Every cell has at most N active coordinates; hence the dimension cutoff at N
retains every cell, whose union is the outer cube by the cover axiom. -/
theorem full_skeleton_eq_cube_carrier {N : ℕ} (K : FiniteRectilinearSubdivision N) :
    K.skeleton N = K.cube.carrier := by
  rw [← K.cover]
  ext x
  simp only [FiniteRectilinearSubdivision.skeleton, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, _, hx⟩
    exact ⟨c, hc, hx⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨c, hc, ?_, hx⟩
    simpa [ClosedCoordinateCell.dimension] using
      ({i : Fin N | c.lower i < c.upper i}.ncard_le_card)

end HolomorphicAnosov.Cubical

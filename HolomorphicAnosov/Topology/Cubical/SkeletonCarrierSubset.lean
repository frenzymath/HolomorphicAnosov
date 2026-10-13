import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision

namespace HolomorphicAnosov.Cubical

/-- Every selected skeleton is contained in the carrier of its cubical subcomplex.
This is the direct union inclusion used in the finite-skeleton neighborhood theorem. -/
theorem subcomplex_skeleton_subset_carrier {N : ℕ}
    {K : FiniteRectilinearSubdivision N} (M : CubicalSubcomplex K) (q : ℕ) :
    M.skeleton q ⊆ M.carrier := by
  intro x hx
  simp only [CubicalSubcomplex.skeleton, Set.mem_iUnion] at hx
  obtain ⟨c, hc, _, hcx⟩ := hx
  simp only [CubicalSubcomplex.carrier, Set.mem_iUnion]
  exact ⟨c, hc, hcx⟩

end HolomorphicAnosov.Cubical

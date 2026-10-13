import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision

namespace HolomorphicAnosov.Cubical

/-- The zero-skeleton of a finite rectilinear subdivision is a finite subset of
its original Euclidean ambient space. Source: Hatcher Lemma 2.34 pp.137–138,
the discrete zero-skeleton base case. Proof: a zero-dimensional coordinate cell
has no strict coordinate interval, so its two corners coincide and its carrier
is the singleton consisting of that corner. The skeleton is therefore contained
in the finite image of the original cell family under the lower-corner map. -/
theorem zeroSkeleton_finite {N : ℕ} (K : FiniteRectilinearSubdivision N) :
    (K.skeleton 0).Finite := by
  apply (K.finite_cells.image ClosedCoordinateCell.lower).subset
  intro x hx
  simp only [FiniteRectilinearSubdivision.skeleton, Set.mem_iUnion] at hx
  obtain ⟨c, hc, hd, hx⟩ := hx
  have hempty : {i : Fin N | c.lower i < c.upper i} = ∅ := by
    apply (Set.ncard_eq_zero (Set.toFinite _)).mp
    exact Nat.eq_zero_of_le_zero hd
  refine ⟨c, hc, ?_⟩
  funext i
  have hnot : ¬ c.lower i < c.upper i := by
    intro h
    have hi : i ∈ {i : Fin N | c.lower i < c.upper i} := h
    rw [hempty] at hi
    exact hi
  exact le_antisymm (hx.1 i) ((hx.2 i).trans (le_of_not_gt hnot))

end HolomorphicAnosov.Cubical


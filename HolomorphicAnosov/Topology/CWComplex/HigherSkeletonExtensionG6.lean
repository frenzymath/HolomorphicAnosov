import HolomorphicAnosov.Topology.CWComplex.SuccessorMapGluingG6
import HolomorphicAnosov.Topology.CWComplex.HigherCellExtension

namespace HolomorphicAnosov
universe u v w

/-- Every continuous map on the n-skeleton, n ≥ 2, extends over the next skeleton
when the target has a surjective contractible covering.

Source: Hatcher, Algebraic Topology, Proposition 1B.9, p.91. Fill each new
characteristic disk using the existing higher-cell extension theorem, which lifts
and contracts its attaching sphere. Choice selects all fillings simultaneously.
Their boundary equations imply agreement wherever a characteristic point belongs
to the lower skeleton; successor-skeleton gluing produces the continuous extension.
No finite-dimensional, regular-cell or local-finiteness hypothesis is used. -/
theorem cw_higher_skeleton_extension_g6
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] [ContractibleSpace E]
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (n : ℕ) (hn : 2 ≤ n)
    (f : C((Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y)) :
    ∃ f' : C((Topology.CWComplex.skeleton (Set.univ : Set K)
      ((n + 1 : ℕ) : ℕ∞) : Set K), Y),
      ∀ x : (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K),
        f' ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast Nat.le_succ n) x.property⟩ = f x := by
  classical
  choose B hB using fun i ↦ cw_realization_higher_cell_extension_succ p hp hsurj n hn i f
  apply cw_successor_map_gluing_g6 n f B
  intro i z hx
  have hz : ‖z.val‖ = 1 := cw_successor_coordinate_boundary_of_lower n i z hx
  have hs : z.val ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact hB i ⟨z.val, hs⟩

end HolomorphicAnosov

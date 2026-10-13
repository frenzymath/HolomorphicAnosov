import HolomorphicAnosov.Topology.BasedHomotopyUniqueness

namespace HolomorphicAnosov

open _root_.Topology

/-- Apply explicit rooted parent-edge data to obtain a carrier contraction.
This is the proved geometric core after the prescribed-tree reindexing.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1 p.84. The parent,
depth, edge-equivalence, and incidence fields are exactly the hypotheses of
the existing CW edge-track gluing theorem.
-/
theorem graph_spanning_tree_loop_rooted_contraction_apply_g3
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (T : Set X) [Topology.CWComplex T]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell T (n + 2)))
    (r : Topology.RelCWComplex.cell T 0)
    (d : Topology.RelCWComplex.cell T 0 → ℕ) (hdr : d r = 0)
    (parent : {v : Topology.RelCWComplex.cell T 0 // v ≠ r} →
      Topology.RelCWComplex.cell T 0)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : {v : Topology.RelCWComplex.cell T 0 // v ≠ r} ≃
      Topology.RelCWComplex.cell T 1)
    (hlink : ∀ v, (Topology.CWComplex.OneSkeletonGraph T).IsLink
      (edge v) (parent v) v.val) :
    ∃ H : C(unitInterval × T, X),
      (∀ x, H (0, x) = x.val) ∧
      (∀ x, H (1, x) = Topology.RelCWComplex.map 0 r 0) ∧
      (∀ t, H (t, ⟨Topology.RelCWComplex.map 0 r 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 r ⟨0, by simp, rfl⟩⟩) =
        Topology.RelCWComplex.map 0 r 0) ∧
      (∀ q, H q ∈ T) := by
  exact rooted_cw_tree_inclusion_contraction T hhigh r d hdr parent hdepth edge hlink

end HolomorphicAnosov

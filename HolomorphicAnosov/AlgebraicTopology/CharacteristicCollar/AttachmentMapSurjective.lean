import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- For every Hausdorff CW space and degree m, its characteristic attachment map onto its m-skeleton is surjective.

Proof: Every skeleton point belongs to an open cell of dimension below m+1. If its cell dimension is below m, it belongs to the lower-skeleton summand. Otherwise the dimension equals m, and its open-cell representative is also a closed-disk representative in the corresponding attachment summand.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem attachmentMap_surjective (m : ℕ) : Function.Surjective (attachmentMap X m) := by
  intro z
  have hz := z.2
  have hu := CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
    (C := (univ : Set X)) m
  have hz : z.1 ∈ (CWComplex.skeletonLT (univ : Set X) m : Set X) ∪
      ⋃ i : RelCWComplex.cell (univ : Set X) m, RelCWComplex.closedCell m i := by
    exact hu.symm ▸ hz
  rcases hz with hz | hz
  · exact ⟨Sum.inl ⟨z, hz⟩, rfl⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨v, hv, he⟩ := hi
    refine ⟨Sum.inr ⟨i, ULift.up ⟨v, hv⟩⟩, ?_⟩
    exact Subtype.ext he

end HolomorphicAnosov.CharacteristicCellComparison

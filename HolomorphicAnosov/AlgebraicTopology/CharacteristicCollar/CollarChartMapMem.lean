import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarCharts
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Every collar-chart point maps through the characteristic attachment into the skeleton collar.

Proof: A lower-skeleton chart point belongs to the left part of the defining union. A disk-collar chart point supplies its own witness for the characteristic collar image.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarChartMap_mem (m : ℕ) (z : CollarCharts X m) :
    attachmentMap X m (collarChartMap X m z) ∈ skeletonCollar X m := by
  rcases z with z | ⟨i, z⟩
  · exact Or.inl z.2
  · exact Or.inr ⟨⟨i, z⟩, rfl⟩

end HolomorphicAnosov.CharacteristicCellComparison

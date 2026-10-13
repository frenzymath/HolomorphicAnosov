import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarCharts
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMapMem

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The collar-chart cover is the collar-chart map with codomain restricted to the inverse image of the skeleton collar under the attachment.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
def collarChartCover (m : ℕ) : CollarCharts X m →
    ↥((attachmentMap X m) ⁻¹' skeletonCollar X m) :=
  fun z ↦ ⟨collarChartMap X m z, collarChartMap_mem X m z⟩

end HolomorphicAnosov.CharacteristicCellComparison

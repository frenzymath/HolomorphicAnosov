import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarDeformationCharacteristic
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarCharts
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartMapMem
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarChartTimeMap

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- At every time the collar-chart path agrees with the skeleton-collar deformation of that chart point’s attached image.

Proof: On the lower-skeleton chart the defining branch of the skeleton deformation is identity. On the disk chart use its characteristic evaluation rule.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem collarChartTimeMap_eq (m : ℕ) (t : unitInterval) (z : CollarCharts X m) :
    collarChartTimeMap X m z t = skeletonCollarDeformation X m t
      ⟨attachmentMap X m (collarChartMap X m z), collarChartMap_mem X m z⟩ := by
  classical
  rcases z with z | ⟨i, z⟩
  · change z.1 = skeletonCollarDeformation X m t ⟨z.1, Or.inl z.2⟩
    simp only [skeletonCollarDeformation, dite_eq_left z.2]
  · exact (skeletonCollarDeformation_characteristic X m t i z).symm

end HolomorphicAnosov.CharacteristicCellComparison
